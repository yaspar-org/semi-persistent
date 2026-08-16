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
use crate::containers::IndexLike; // prod-parity: L::min() (was L::MIN)
use crate::containers::Tagged;
use crate::containers::{ShrinkPolicy, VecI, VecToken};
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

/// A node's content hash, folded to 32 bits.
///
/// The index stores the fingerprint rather than the whole 64-bit hash. It is
/// not a filter that has to be exact — every candidate the table returns is
/// still confirmed against the node's operator and children — so its only job
/// is to keep the table from reading the node arena on a near-miss, and 32
/// bits do that: at a million nodes the expected number of colliding pairs in
/// the whole table is under two hundred.
///
/// What the width buys is the entry: `(StoredKey<u32>, ())` is eight bytes
/// where `(StoredKey<u64>, G)` was sixteen, so a probe of a million-node table
/// touches half as many cache lines and a growth rehashes half as much memory.
type Fingerprint = u32;

/// Fold a 64-bit content hash into a fingerprint, mixing the high half in so
/// every input bit reaches the result.
#[inline]
fn fold32(h: u64) -> Fingerprint {
    (h ^ (h >> 32)) as Fingerprint
}

/// Spread a fingerprint over the 64 bits hashbrown reads.
///
/// hashbrown takes the bucket index from the low bits and the control byte
/// from the top seven, so a fingerprint zero-extended into a `u64` would file
/// every entry under the same control byte and turn each probe into a scan.
/// Multiplying by an odd constant is a bijection on `u64`, so distinct
/// fingerprints keep distinct hashes and equal ones keep equal hashes — which
/// is what lets `remove` find an entry from its stored fingerprint.
#[inline]
fn spread(fp: Fingerprint) -> u64 {
    (fp as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

#[derive(Clone, Copy, Debug)]
struct StoredKey<L> {
    fp: Fingerprint,
    local_id: L,
}

impl<L> Hash for StoredKey<L> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(spread(self.fp));
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
    /// One entry per node, so `L` (a local node id) is the index width.
    nodes: VecI<FixedArityNode<G, O, K>, L, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
    /// Recanonicalization history, indexed at `usize`: its population is the number of
    /// rewrites performed, not the number of nodes, and a single node can be recanonicalized
    /// arbitrarily many times — so no id capacity bounds it and `L` here would be a cap.
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
            nodes: VecI::new(),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            history: if PROOFS { Some(VecI::new()) } else { None },
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == <L as IndexLike>::min()
    }

    pub fn get(&self, id: L) -> FixedArityNode<G, O, K> {
        self.nodes.get(id)
    }

    pub fn set(&mut self, id: L, node: FixedArityNode<G, O, K>) {
        self.nodes.set(id, node);
    }

    pub fn probe(&self, op: &O, children: &[G; K]) -> Option<G> {
        let fp = self.fingerprint(op, children);
        self.index
            .raw_entry()
            .from_hash(spread(fp), |sk| {
                sk.fp == fp && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == *op && n.children == *children
                }
            })
            .map(|(sk, _)| self.nodes.get(sk.local_id).global_id())
    }

    pub fn insert(&mut self, global_id: G, op: O, children: [G; K]) -> L {
        let node = FixedArityNode::new(global_id, op, children);
        let fp = self.fingerprint(&op, &children);
        let lid = self.nodes.len();
        self.nodes.try_push(node).expect("push: within index word");
        self.index.insert(StoredKey { fp, local_id: lid }, ());
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
        let old_fp = self.fingerprint(&node.op(), &node.children);

        F::canonize(&mut node.children, &find);

        let new_fp = self.fingerprint(&node.op(), &node.children);
        if new_fp == old_fp {
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
            hist.try_push(self.nodes.get(local_id))
                .expect("push: within index word");
        }

        self.index.remove(&StoredKey {
            fp: old_fp,
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
                fp: new_fp,
                local_id,
            },
            (),
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
            nodes: self
                .nodes
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            history: self.history.as_mut().map(|h| {
                h.try_mark(shrink)
                    .expect("mark: frame depth is bounded by the saturation driver")
            }),
        }
    }

    pub fn restore(&mut self, token: CacheToken) {
        self.nodes
            .try_restore(token.nodes)
            .expect("restore: token minted by this container's own mark");
        if let (Some(h), Some(tok)) = (&mut self.history, token.history) {
            h.try_restore(tok)
                .expect("restore: token minted by this container's own mark");
        }
        self.rebuild_index();
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        // `from_usize` needs no bound check here: `nodes` is indexed *by* `L`, so its own
        // capacity guard is the id bound (`IndexLike::max_nat()` of a dense id is its
        // `id_bound()`). Every position the arena can hold therefore has a local id. The
        // scans that DO need a check are the ones over a container indexed by an id's
        // *word* rather than the id — see `EGraph::node_ids`.
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            self.index.insert(
                StoredKey {
                    fp: fold32(n.content_hash()),
                    local_id: lid,
                },
                (),
            );
        }
    }

    fn fingerprint(&self, op: &O, children: &[G; K]) -> Fingerprint {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        children.hash(&mut h);
        fold32(h.finish())
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
    /// One entry per node, so `L` (a local node id) is the index width.
    nodes: VecI<VariableArityNode<G, O>, L, TRACK>,
    /// The shared child pool the nodes' spans address. Indexed at `usize`, matching the
    /// `start`/`end` words in [`VariableArityNode`]: its population is `Σ arity` over the
    /// nodes, which neither `L`'s nor `G`'s capacity bounds, so an id-width index here would
    /// be a new cap rather than a narrowing. See [`VariableArityNode::start`].
    children: VecI<C, usize, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
    /// Recanonicalization history. `usize` for a different reason than `children`: the
    /// population here is the number of *rewrites* the run has performed, which is unbounded
    /// by any id capacity — a single node can be recanonicalized arbitrarily many times.
    history_nodes: Option<VecI<VariableArityNode<G, O>, usize, TRACK>>,
    /// Children of the history entries; `Σ arity` over `history_nodes`, so `usize` for both
    /// of the reasons above at once.
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
            nodes: VecI::new(),
            children: VecI::new(),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            history_nodes: if PROOFS { Some(VecI::new()) } else { None },
            history_children: if PROOFS { Some(VecI::new()) } else { None },
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == <L as IndexLike>::min()
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
        let fp = self.fingerprint(&op, elems);
        self.index
            .raw_entry()
            .from_hash(spread(fp), |sk| {
                sk.fp == fp && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == op && self.children_eq(&n, elems)
                }
            })
            .map(|(sk, _)| self.nodes.get(sk.local_id).global_id())
    }

    pub fn insert(&mut self, global_id: G, op: O, elems: &[C]) -> L {
        let start = self.children.len();
        for &e in elems {
            self.children.try_push(e).expect("push: within index word");
        }
        let end = self.children.len();
        let node = VariableArityNode::make(global_id, op, start, end);
        let fp = self.fingerprint(&op, elems);
        let lid = self.nodes.len();
        self.nodes.try_push(node).expect("push: within index word");
        self.index.insert(StoredKey { fp, local_id: lid }, ());
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
        mode: crate::canon::CanonMode<G>,
    ) {
        let node = self.nodes.get(local_id);
        let (start, end) = node.span();
        let old_fp = self.children_fingerprint(&node);

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
                hc.try_push(self.children.get(i))
                    .expect("push: within index word");
            }
            let hist_end = hc.len();
            hn.try_push(VariableArityNode::make(
                node.global_id(),
                node.op(),
                hist_start,
                hist_end,
            ))
            .expect("push: within index word");
        }

        self.index.remove(&StoredKey {
            fp: old_fp,
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

        let new_fp = self.fingerprint(&node.op(), &buf[..new_len]);

        if let Some(existing_gid) = self.probe(node.op(), &buf[..new_len]) {
            collisions.push((gid, existing_gid));
        }

        self.index.insert(
            StoredKey {
                fp: new_fp,
                local_id,
            },
            (),
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
            nodes: self
                .nodes
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            children: self
                .children
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            history_nodes: self.history_nodes.as_mut().map(|h| {
                h.try_mark(shrink)
                    .expect("mark: frame depth is bounded by the saturation driver")
            }),
            history_children: self.history_children.as_mut().map(|h| {
                h.try_mark(shrink)
                    .expect("mark: frame depth is bounded by the saturation driver")
            }),
        }
    }

    pub fn restore(&mut self, token: PoolCacheToken) {
        self.nodes
            .try_restore(token.nodes)
            .expect("restore: token minted by this container's own mark");
        self.children
            .try_restore(token.children)
            .expect("restore: token minted by this container's own mark");
        if let (Some(h), Some(tok)) = (&mut self.history_nodes, token.history_nodes) {
            h.try_restore(tok)
                .expect("restore: token minted by this container's own mark");
        }
        if let (Some(h), Some(tok)) = (&mut self.history_children, token.history_children) {
            h.try_restore(tok)
                .expect("restore: token minted by this container's own mark");
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
        // `from_usize` needs no bound check here: `nodes` is indexed *by* `L`, so its own
        // capacity guard is the id bound (`IndexLike::max_nat()` of a dense id is its
        // `id_bound()`). Every position the arena can hold therefore has a local id. The
        // scans that DO need a check are the ones over a container indexed by an id's
        // *word* rather than the id — see `EGraph::node_ids`.
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            let fp = self.children_fingerprint(&n);
            self.index.insert(StoredKey { fp, local_id: lid }, ());
        }
    }

    fn fingerprint(&self, op: &O, elems: &[C]) -> Fingerprint {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        elems.hash(&mut h);
        fold32(h.finish())
    }

    fn children_fingerprint(&self, node: &VariableArityNode<G, O>) -> Fingerprint {
        let mut h = rapidhash::fast::RapidHasher::default();
        node.op().hash(&mut h);
        let (start, end) = node.span();
        (end - start).hash(&mut h);
        for i in start..end {
            self.children.get(i).hash(&mut h);
        }
        fold32(h.finish())
    }
}

// ---------------------------------------------------------------------------
// LitCache<G, O, V, L, TRACK>
// ---------------------------------------------------------------------------

pub struct LitCache<G: DenseId, O: DenseId, V: DenseId, L: DenseId, const TRACK: bool = true> {
    nodes: VecI<LitNode<G, O, V>, L, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
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
            nodes: VecI::new(),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == <L as IndexLike>::min()
    }

    pub fn get(&self, id: L) -> LitNode<G, O, V> {
        self.nodes.get(id)
    }

    pub fn set(&mut self, id: L, node: LitNode<G, O, V>) {
        self.nodes.set(id, node);
    }

    pub fn probe(&self, op: O, lit: V) -> Option<G> {
        let fp = self.fingerprint(&op, &lit);
        self.index
            .raw_entry()
            .from_hash(spread(fp), |sk| {
                sk.fp == fp && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == op && n.lit == lit
                }
            })
            .map(|(sk, _)| self.nodes.get(sk.local_id).global_id())
    }

    pub fn insert(&mut self, global_id: G, op: O, lit: V) -> L {
        let node = LitNode::new(global_id, op, lit);
        let fp = self.fingerprint(&op, &lit);
        let lid = self.nodes.len();
        self.nodes.try_push(node).expect("push: within index word");
        self.index.insert(StoredKey { fp, local_id: lid }, ());
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
            nodes: self
                .nodes
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            history: None,
        }
    }

    pub fn restore(&mut self, token: CacheToken) {
        self.nodes
            .try_restore(token.nodes)
            .expect("restore: token minted by this container's own mark");
        self.rebuild_index();
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        // `from_usize` needs no bound check here: `nodes` is indexed *by* `L`, so its own
        // capacity guard is the id bound (`IndexLike::max_nat()` of a dense id is its
        // `id_bound()`). Every position the arena can hold therefore has a local id. The
        // scans that DO need a check are the ones over a container indexed by an id's
        // *word* rather than the id — see `EGraph::node_ids`.
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            self.index.insert(
                StoredKey {
                    fp: fold32(n.content_hash()),
                    local_id: lid,
                },
                (),
            );
        }
    }

    fn fingerprint(&self, op: &O, lit: &V) -> Fingerprint {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        lit.hash(&mut h);
        fold32(h.finish())
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

    /// A 32-bit fingerprint collision does not produce a wrong hash-cons hit.
    ///
    /// `probe` uses the fingerprint only to reach a candidate; the hit is
    /// declared by `n.op() == *op && n.children == *children` (fixed arity) and
    /// `n.op() == op && self.children_eq(&n, elems)` (variable arity). Without
    /// that confirmation a collision would return some *other* node's class,
    /// which `EGraph::add` would then treat as the term's class — an unsound
    /// merge of two structurally different terms. The test brute-forces a real
    /// collision (birthday: ~2^16 candidates expected) and checks both probes
    /// still answer with their own node.
    #[test]
    fn fingerprint_collision_is_disambiguated_by_content() {
        const LIMIT: u32 = 4_000_000;

        // -- fixed arity: `[G; 2]`, hashed element-wise --
        let mut fixed = FixedArityCache::<ENodeId, OpId, Plain2Id, 2, false>::new();
        let op = OpId::new(0);
        let mut seen: std::collections::HashMap<Fingerprint, u32> =
            std::collections::HashMap::new();
        let (a, b) = (0..LIMIT)
            .find_map(|n| {
                let fp = fixed.fingerprint(&op, &[ENodeId::new(n), ENodeId::new(0)]);
                seen.insert(fp, n).map(|prev| (prev, n))
            })
            .expect("no 32-bit fingerprint collision within the search bound");
        assert_ne!(a, b);
        let (ca, cb) = (
            [ENodeId::new(a), ENodeId::new(0)],
            [ENodeId::new(b), ENodeId::new(0)],
        );
        // A genuine collision: same fingerprint, different children.
        assert_eq!(fixed.fingerprint(&op, &ca), fixed.fingerprint(&op, &cb));
        assert_ne!(ca, cb);

        let ga = ENodeId::new(LIMIT + 1);
        let gb = ENodeId::new(LIMIT + 2);
        assert!(matches!(
            fixed.probe_or_insert(ga, op, ca),
            InsertResult::Inserted { .. }
        ));
        // The colliding node must NOT be reported as already present.
        assert!(matches!(
            fixed.probe_or_insert(gb, op, cb),
            InsertResult::Inserted { .. }
        ));
        assert_eq!(fixed.probe(&op, &ca), Some(ga));
        assert_eq!(fixed.probe(&op, &cb), Some(gb));

        // -- variable arity: `&[C]`, hashed with a length prefix --
        let mut var = VariableArityCache::<ENodeId, OpId, ENodeId, PlainNId, false>::new();
        let mut seen: std::collections::HashMap<Fingerprint, u32> =
            std::collections::HashMap::new();
        let (a, b) = (0..LIMIT)
            .find_map(|n| {
                let fp = var.fingerprint(&op, &[ENodeId::new(n), ENodeId::new(0)]);
                seen.insert(fp, n).map(|prev| (prev, n))
            })
            .expect("no 32-bit fingerprint collision within the search bound");
        let (va, vb) = (
            [ENodeId::new(a), ENodeId::new(0)],
            [ENodeId::new(b), ENodeId::new(0)],
        );
        assert_eq!(var.fingerprint(&op, &va), var.fingerprint(&op, &vb));
        assert_ne!(va, vb);

        assert!(matches!(
            var.probe_or_insert(ga, op, &va),
            InsertResult::Inserted { .. }
        ));
        assert!(matches!(
            var.probe_or_insert(gb, op, &vb),
            InsertResult::Inserted { .. }
        ));
        assert_eq!(var.probe(op, &va), Some(ga));
        assert_eq!(var.probe(op, &vb), Some(gb));
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
            crate::canon::CanonMode::PLAIN,
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
            crate::canon::CanonMode::PLAIN,
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
            crate::canon::CanonMode::PLAIN,
        );
        assert!(collisions.is_empty());
        assert!(c.probe(op, &[id(1), id(3)]).is_some());
        // old 3-element key gone
        assert!(c.probe(op, &[id(1), id(2), id(3)]).is_none());
    }

    #[test]
    fn recanonize_ac_merges_mult() {
        type MSetChild = crate::containers::Pair<ENodeId, Multiplicity>;
        let pair = |g, m| crate::containers::Pair {
            a: g,
            b: Multiplicity(m),
        };
        let mut c = VariableArityCache::<ENodeId, OpId, MSetChild, MSetNodeId, false>::new();
        let op = OpId::new(0);
        let elems: &[MSetChild] = &[pair(id(1), 1), pair(id(2), 1), pair(id(3), 1)];
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
            crate::canon::CanonMode::PLAIN,
        );
        assert!(collisions.is_empty());
        let expected: &[MSetChild] = &[pair(id(1), 2), pair(id(3), 1)];
        assert!(c.probe(op, expected).is_some());
    }
}
