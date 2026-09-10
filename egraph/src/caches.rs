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
/// What the width buys is the entry size: a hint is one fingerprint bucket
/// key plus a list of 4-byte local ids, so a probe of a million-node table
/// touches half the cache lines a 64-bit key would and a growth rehashes half
/// as much memory.
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

/// Bucket key for the hint index: one bucket per fingerprint, hashed through
/// the passthrough hasher as `spread(fp)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FpKey(Fingerprint);

impl Hash for FpKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(spread(self.0));
    }
}

/// One hint-map value, packed to 4 bytes so a map entry stays 8 bytes — the
/// same footprint as the retired exact table's `(StoredKey, ())` entry. At
/// EqSat scale entry size IS probe cost: a 32-byte entry (key + inline
/// SmallVec bucket) made the table 4x the cache lines and regressed
/// math-microbenchmark 9 to 12% with bit-identical work counts (same node,
/// recanonize and collision totals); the small SMT tables never left L2, so
/// the corpus sweep did not see it.
///
/// MSB clear: the value IS the single local id hinted at this fingerprint
/// (the common all-distinct case; ids are 31-bit by the `define_id31`
/// doctrine, so the MSB is free). MSB set: the low 31 bits index the cache's
/// `spill` table, whose entry lists every id hinted at this fingerprint
/// (congruent clusters and re-key histories).
#[derive(Clone, Copy, Debug)]
struct HintSlot(u32);

const HINT_SPILL_TAG: u32 = 1 << 31;

impl HintSlot {
    #[inline]
    fn single(id: usize) -> Self {
        debug_assert!(id < HINT_SPILL_TAG as usize);
        HintSlot(id as u32)
    }
    #[inline]
    fn spilled(ix: usize) -> Self {
        debug_assert!(ix < HINT_SPILL_TAG as usize);
        HintSlot(ix as u32 | HINT_SPILL_TAG)
    }
    #[inline]
    fn as_single(self) -> Option<usize> {
        (self.0 & HINT_SPILL_TAG == 0).then_some(self.0 as usize)
    }
    #[inline]
    fn spill_index(self) -> usize {
        (self.0 & !HINT_SPILL_TAG) as usize
    }
}

/// One spilled hint bucket. Four ids inline: a bucket exists only once a
/// fingerprint has at least two hinted ids.
type HintBucket<L> = smallvec::SmallVec<[L; 4]>;

/// Per-bucket length that triggers an in-place compaction on the next push:
/// sort + dedup + drop bounds-dead ids, and drop content-stale ids when NO
/// mark is live (droppability of a stale hint is exactly "no restore can
/// revive it"). While marks are live a content-stale hint must survive: a
/// later restore rolls the node's content back and revalidates it (that is
/// the whole design — restore does no index work).
const HINT_COMPACT_LEN: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InsertResult<G, L> {
    Hit { global_id: G },
    Inserted { local_id: L },
}

/// One open mark, mirroring the frame the node arena pushed for the same mark.
/// The hint index needs nothing from it at restore time (restore does no
/// index work); the frame stack exists to validate and consume tokens.
#[derive(Clone, Copy, Debug)]
struct CacheFrame;

/// Restore rebuilds an append-only value index once the incremental deletions
/// would exceed `1 / REBUILD_RATIO` of a rebuild. Used by the literal value
/// interner (`crate::literal::LitValStore`), whose entries never re-key; the
/// node caches' hint index has no rebuild path at all.
pub(crate) const REBUILD_RATIO: usize = 4;

/// Whether a suffix-only restore can fix an append-only index in place rather
/// than rebuilding it. See [`REBUILD_RATIO`].
#[inline]
pub(crate) fn restore_incrementally(
    suffix_len: usize,
    pending_len: usize,
    saved_len: usize,
) -> bool {
    REBUILD_RATIO * (suffix_len + pending_len) <= saved_len
}

#[derive(Clone, Copy, Debug)]
pub struct CacheToken {
    nodes: VecToken,
    history: Option<VecToken>,
    frame_index: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct PoolCacheToken {
    nodes: VecToken,
    children: VecToken,
    history_nodes: Option<VecToken>,
    history_children: Option<VecToken>,
    frame_index: usize,
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
    // Value layer: NoValueCompression by measurement (F2.4): the layered RLE
    // candidates cost 7.28/6.84 MB against 5.06 MB plain and 4.62 MB sorted
    // runs on the corpus, zero wins in 39,272 frames. Revisit at EqSat scale.
    nodes: crate::containers::VecD<FixedArityNode<G, O, K>, L, TRACK>,
    /// Hint index: fingerprint -> local ids that at some point held content
    /// with that fingerprint. The arena is the source of truth; a probe
    /// validates every candidate against current node content, so restore
    /// performs NO index maintenance — rolling the arena back revalidates the
    /// old-content hints and invalidates the new-content ones by itself. This
    /// is what removes the re-key repair from the restore path entirely, and
    /// it is also what keeps congruent-duplicate clusters (thousands of nodes
    /// with identical content after merge waves, measured 14 distinct
    /// fingerprints across 11678 live nodes on QF_UF_cyclic_scheduler.3) from
    /// degrading the table: a cluster is one bucket pushed to in O(1), not a
    /// same-hash probe chain the map walks quadratically.
    index: hashbrown::HashMap<FpKey, HintSlot, PassthroughBuildHasher>,
    /// Spilled hint buckets; `HintSlot` values with the spill tag index here.
    spill: Vec<HintBucket<L>>,
    /// Recanonicalization history, indexed at `usize`: its population is the number of
    /// rewrites performed, not the number of nodes, and a single node can be recanonicalized
    /// arbitrarily many times — so no id capacity bounds it and `L` here would be a cap.
    history: Option<VecI<FixedArityNode<G, O, K>, usize, TRACK>>,
    frames: Vec<CacheFrame>,
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
            nodes: crate::containers::VecD::new_kind(crate::containers::env_diff_store_kind()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            spill: Vec::new(),
            history: if PROOFS { Some(VecI::new()) } else { None },
            frames: Vec::new(),
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
        self.probe_hints(op, children, None)
    }

    /// Scan the hint bucket for `(op, children)`: the first id whose CURRENT
    /// arena content equals the query is the answer. The content compare is
    /// the validity check — a hint whose node has since re-keyed (or been
    /// truncated) simply fails it and is skipped. `skip` excludes one id, for
    /// the recanonize collision probe: a node that oscillated back to earlier
    /// content has a valid hint for ITSELF in the bucket, which is not a
    /// collision.
    fn probe_hints(&self, op: &O, children: &[G; K], skip: Option<L>) -> Option<G> {
        self.probe_hints_fp(self.fingerprint(op, children), op, children, skip)
    }

    /// `probe_hints_fp` that also promotes the answer to the front of its
    /// bucket. Bucket order carries no meaning (every candidate is validated
    /// against arena content), so the swap is free of correctness weight; it
    /// matters because a search workload re-probes the same terms constantly
    /// while restores leave content-stale hints in front of them - measured
    /// 36 to 51 entries scanned per probe on the search benchmarks against
    /// 1.19 on a saturation-only workload.
    fn probe_hints_fp_mut(
        &mut self,
        fp: Fingerprint,
        op: &O,
        children: &[G; K],
        skip: Option<L>,
    ) -> Option<G> {
        let slot = *self.index.get(&FpKey(fp))?;
        let live = self.nodes.len().as_usize();
        match slot.as_single() {
            Some(raw) => {
                let id = L::from_usize(raw);
                if Some(id) == skip || raw >= live {
                    return None;
                }
                let n = self.nodes.get(id);
                (n.op() == *op && n.children == *children).then(|| n.global_id())
            }
            None => {
                let ix = slot.spill_index();
                // Lazy reclamation of BOUNDS-DEAD hints, during a scan we
                // are performing anyway, so restore still does no index work.
                // An id past the live length names a cell the arena has
                // truncated; nothing can bring that hint back, because a
                // later intern reusing the id pushes its own fresh hint.
                //
                // Content-stale entries are deliberately NOT reclaimed here.
                // "The content does not match this QUERY" is not the same as
                // "this hint is dead": two contents can share a fingerprint,
                // so a node whose current content collides with the query's
                // fingerprint still needs its hint. Dropping on query
                // mismatch broke completeness and silently interned 39
                // duplicate nodes on math-microbenchmark. The correct test is
                // fingerprint(current content) != fp, which needs a cached
                // per-node fingerprint to be cheap - see the notes at
                // FixedArityNode.
                let mut hit: Option<G> = None;
                let mut pos: usize = 0;
                while pos < self.spill[ix].len() {
                    let id = self.spill[ix][pos];
                    if id.as_usize() >= live {
                        self.spill[ix].swap_remove(pos);
                        continue;
                    }
                    if Some(id) == skip {
                        pos += 1;
                        continue;
                    }
                    let n = self.nodes.get(id);
                    if n.op() == *op && n.children == *children {
                        hit = Some(n.global_id());
                        break;
                    }
                    pos += 1;
                }
                let gid = hit?;
                if pos != 0 {
                    self.spill[ix].swap(0, pos);
                }
                Some(gid)
            }
        }
    }

    /// `probe_hints` with the fingerprint already in hand: the callers that
    /// need it afterwards (intern, recanonize) compute it once and thread it
    /// rather than hashing the same content twice per operation.
    fn probe_hints_fp(
        &self,
        fp: Fingerprint,
        op: &O,
        children: &[G; K],
        skip: Option<L>,
    ) -> Option<G> {
        let slot = *self.index.get(&FpKey(fp))?;
        let live = self.nodes.len().as_usize();
        let check = |id: L| -> Option<G> {
            if Some(id) == skip || id.as_usize() >= live {
                return None;
            }
            let n = self.nodes.get(id);
            (n.op() == *op && n.children == *children).then(|| n.global_id())
        };
        match slot.as_single() {
            Some(raw) => check(L::from_usize(raw)),
            None => self.spill[slot.spill_index()]
                .iter()
                .find_map(|&id| check(id)),
        }
    }

    /// Record that `id` (currently) holds content with fingerprint `fp`.
    /// O(1): no duplicate scan — a repeated hint is harmless and compaction
    /// dedups it later. Hints are never removed on re-key or restore; see the
    /// `index` field doc for why that is the design and not a leak.
    ///
    /// Amortized compaction drops duplicate and bounds-dead ids always, and
    /// content-stale ids when NO mark is live: droppability of a stale hint
    /// is exactly "no restore can revive it", and with an empty frame stack
    /// nothing can.
    fn push_hint(&mut self, fp: Fingerprint, id: L) {
        let key = FpKey(fp);
        let Some(&slot) = self.index.get(&key) else {
            self.index.insert(key, HintSlot::single(id.as_usize()));
            return;
        };
        if let Some(raw) = slot.as_single() {
            if raw == id.as_usize() {
                return;
            }
            // A dead single (its id truncated by a restore) is replaced in
            // place instead of promoted: droppability is the compaction rule
            // for dead ids (a truncated id only returns via a fresh intern,
            // which pushes a fresh hint), and promoting it would manufacture
            // a heap spill bucket for a fingerprint with one live hint.
            if raw >= self.nodes.len().as_usize() {
                self.index.insert(key, HintSlot::single(id.as_usize()));
                return;
            }
            let ix = self.spill.len();
            let mut b = HintBucket::<L>::new();
            b.push(L::from_usize(raw));
            b.push(id);
            self.spill.push(b);
            self.index.insert(key, HintSlot::spilled(ix));
            return;
        }
        let ix = slot.spill_index();
        let b = &self.spill[ix];
        // Skip a hint this bucket already carries. Buckets are probed orders
        // of magnitude more often than they are pushed to (measured 79M
        // probes against thousands of pushes on the search benchmarks), so
        // paying a bounded membership scan here to keep every later scan
        // shorter is the right side of the trade: it removed 40% of bucket
        // entries on search-portfolio, which were re-hints of a node
        // returning to content it had held before.
        if b.iter().any(|e| e.as_usize() == id.as_usize()) {
            return;
        }
        if b.len() >= HINT_COMPACT_LEN && b.len().is_power_of_two() {
            let live = self.nodes.len().as_usize();
            let frameless = self.frames.is_empty();
            let nodes = &self.nodes;
            let b = &mut self.spill[ix];
            if frameless {
                b.retain(|&mut e| e.as_usize() < live && fold32(nodes.get(e).content_hash()) == fp);
            } else {
                b.retain(|&mut e| e.as_usize() < live);
            }
            b.sort_unstable_by_key(|e| e.as_usize());
            b.dedup();
        }
        self.spill[ix].push(id);
    }

    pub fn insert(&mut self, global_id: G, op: O, children: [G; K]) -> L {
        let fp = self.fingerprint(&op, &children);
        self.insert_fp(fp, global_id, op, children)
    }

    /// `insert` with the fingerprint already computed (see `probe_or_insert`).
    pub fn insert_fp(&mut self, fp: Fingerprint, global_id: G, op: O, children: [G; K]) -> L {
        let node = FixedArityNode::new(global_id, op, children);
        let lid = self.nodes.len();
        self.nodes.try_push(node).expect("push: within index word");
        self.push_hint(fp, lid);
        lid
    }

    pub fn probe_or_insert(&mut self, global_id: G, op: O, children: [G; K]) -> InsertResult<G, L> {
        // One fingerprint for the pair of operations: the probe's hash is
        // reused by the insert instead of being recomputed on a miss.
        let fp = self.fingerprint(&op, &children);
        if let Some(gid) = self.probe_hints_fp_mut(fp, &op, &children, None) {
            return InsertResult::Hit { global_id: gid };
        }
        let lid = self.insert_fp(fp, global_id, op, children);
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
        let orig = self.nodes.get(local_id);
        let mut node = orig;

        F::canonize(&mut node.children, &find);

        // No-change filter, hash-free: the cached content tag rejects the
        // common case in one word compare, and any survivor is settled by the
        // direct children comparison (K <= 3 words). This replaces two full
        // fingerprint computations per recanonize.
        if node.children == orig.children {
            return;
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

        let gid = node.global_id();
        let mut new_node = FixedArityNode::new(gid, node.op(), node.children);
        if PROOFS {
            new_node.set_history();
        }
        // One fingerprint for the whole operation: it keys the collision
        // probe and the hint push (previously each recomputed a hash of the
        // same content).
        let new_fp = self.fingerprint(&new_node.op(), &new_node.children);
        self.nodes.set(local_id, new_node);

        // Collision probe AFTER the write, excluding this node: the old hint
        // stays in its bucket (a restore past this point revalidates it), and
        // a self-hint from earlier content is not a collision.
        if let Some(existing_gid) =
            self.probe_hints_fp_mut(new_fp, &node.op(), &node.children, Some(local_id))
        {
            collisions.push((gid, existing_gid));
        }

        self.push_hint(new_fp, local_id);
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
        let token = CacheToken {
            nodes: self
                .nodes
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            history: self.history.as_mut().map(|h| {
                h.try_mark(shrink)
                    .expect("mark: frame depth is bounded by the saturation driver")
            }),
            frame_index: self.frames.len(),
        };
        self.frames.push(CacheFrame);
        token
    }

    pub fn restore(&mut self, token: CacheToken) {
        let _frame = *self
            .frames
            .get(token.frame_index)
            .expect("restore: token minted by this cache's own mark, and not already spent");
        assert!(
            self.nodes.is_valid_token(&token.nodes),
            "restore: node-arena token is not restorable"
        );
        if let (Some(h), Some(tok)) = (&self.history, token.history.as_ref()) {
            assert!(
                h.is_valid_token(tok),
                "restore: history token is not restorable"
            );
        }
        // The index needs NO maintenance here: hints self-correct. Rolling
        // the arena back revalidates every pre-mark hint (the content it
        // points at returns) and invalidates every post-mark one (its content
        // is gone or reverted, so the probe's content compare skips it).
        // Truncated ids fail the probe's bounds check until a fresh intern
        // reuses the slot and pushes a fresh hint.
        self.nodes
            .try_restore(token.nodes)
            .expect("restore: token minted by this container's own mark");
        if let (Some(h), Some(tok)) = (&mut self.history, token.history) {
            h.try_restore(tok)
                .expect("restore: token minted by this container's own mark");
        }
        self.frames.truncate(token.frame_index);
        #[cfg(debug_assertions)]
        debug_assert!(
            self.index_is_complete(),
            "restore left the hashcons hint index incomplete"
        );
    }

    /// Completeness oracle: every live node's content is findable through the
    /// hint index (probe returns SOME node with equal content, not necessarily
    /// this one — congruent duplicates share an answer). This is the invariant
    /// hash-consing needs; hints being stale is fine, hints being missing is
    /// not.
    #[cfg(debug_assertions)]
    fn index_is_complete(&self) -> bool {
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let n = self.nodes.get(L::from_usize(i));
            if self.probe(&n.op(), &n.children).is_none() {
                return false;
            }
        }
        true
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
    // Same measured demotion as the fixed-arity cache (46.9/42.8 KB layered
    // RLE vs 35.0 KB plain, 33.8 KB sorted runs, zero wins in 537 frames).
    nodes: crate::containers::VecD<VariableArityNode<G, O>, L, TRACK>,
    /// The shared child pool the nodes' spans address. Indexed at `usize`, matching the
    /// `start`/`end` words in [`VariableArityNode`]: its population is `Σ arity` over the
    /// nodes, which neither `L`'s nor `G`'s capacity bounds, so an id-width index here would
    /// be a new cap rather than a narrowing. See [`VariableArityNode::start`].
    children: crate::containers::VecD<C, usize, TRACK>,
    /// Hint index over (op, span contents); see [`FixedArityCache::index`].
    index: hashbrown::HashMap<FpKey, HintSlot, PassthroughBuildHasher>,
    /// Spilled hint buckets; `HintSlot` values with the spill tag index here.
    spill: Vec<HintBucket<L>>,
    /// Recanonicalization history. `usize` for a different reason than `children`: the
    /// population here is the number of *rewrites* the run has performed, which is unbounded
    /// by any id capacity — a single node can be recanonicalized arbitrarily many times.
    history_nodes: Option<VecI<VariableArityNode<G, O>, usize, TRACK>>,
    /// Children of the history entries; `Σ arity` over `history_nodes`, so `usize` for both
    /// of the reasons above at once.
    history_children: Option<VecI<C, usize, TRACK>>,
    frames: Vec<CacheFrame>,
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
            nodes: crate::containers::VecD::new_kind(crate::containers::env_diff_store_kind()),
            children: crate::containers::VecD::new_kind(crate::containers::env_diff_store_kind()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            spill: Vec::new(),
            history_nodes: if PROOFS { Some(VecI::new()) } else { None },
            history_children: if PROOFS { Some(VecI::new()) } else { None },
            frames: Vec::new(),
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
        self.probe_hints(op, elems, None)
    }

    /// Hint-bucket scan; see [`FixedArityCache::probe_hints`]. Validity here
    /// reads through the child pool (`children_eq` over the node's span), so
    /// a pool-only recanonize invalidates and a pool rollback revalidates
    /// without the node record changing.
    fn probe_hints(&self, op: O, elems: &[C], skip: Option<L>) -> Option<G> {
        let fp = self.fingerprint(&op, elems);
        let slot = *self.index.get(&FpKey(fp))?;
        let live = self.nodes.len().as_usize();
        let check = |id: L| -> Option<G> {
            if Some(id) == skip || id.as_usize() >= live {
                return None;
            }
            let n = self.nodes.get(id);
            (n.op() == op && self.children_eq(&n, elems)).then(|| n.global_id())
        };
        match slot.as_single() {
            Some(raw) => check(L::from_usize(raw)),
            None => self.spill[slot.spill_index()]
                .iter()
                .find_map(|&id| check(id)),
        }
    }

    /// See [`FixedArityCache::push_hint`], including the frameless
    /// content-validating compaction (validity here reads through the child
    /// pool, as `var_children_fingerprint` does).
    fn push_hint(&mut self, fp: Fingerprint, id: L) {
        let key = FpKey(fp);
        let Some(&slot) = self.index.get(&key) else {
            self.index.insert(key, HintSlot::single(id.as_usize()));
            return;
        };
        if let Some(raw) = slot.as_single() {
            if raw == id.as_usize() {
                return;
            }
            // A dead single (its id truncated by a restore) is replaced in
            // place instead of promoted: droppability is the compaction rule
            // for dead ids (a truncated id only returns via a fresh intern,
            // which pushes a fresh hint), and promoting it would manufacture
            // a heap spill bucket for a fingerprint with one live hint.
            if raw >= self.nodes.len().as_usize() {
                self.index.insert(key, HintSlot::single(id.as_usize()));
                return;
            }
            let ix = self.spill.len();
            let mut b = HintBucket::<L>::new();
            b.push(L::from_usize(raw));
            b.push(id);
            self.spill.push(b);
            self.index.insert(key, HintSlot::spilled(ix));
            return;
        }
        let ix = slot.spill_index();
        let b = &self.spill[ix];
        // Skip a hint this bucket already carries. Buckets are probed orders
        // of magnitude more often than they are pushed to (measured 79M
        // probes against thousands of pushes on the search benchmarks), so
        // paying a bounded membership scan here to keep every later scan
        // shorter is the right side of the trade: it removed 40% of bucket
        // entries on search-portfolio, which were re-hints of a node
        // returning to content it had held before.
        if b.iter().any(|e| e.as_usize() == id.as_usize()) {
            return;
        }
        if b.len() >= HINT_COMPACT_LEN && b.len().is_power_of_two() {
            let live = self.nodes.len().as_usize();
            let frameless = self.frames.is_empty();
            let nodes = &self.nodes;
            let children = &self.children;
            let b = &mut self.spill[ix];
            if frameless {
                b.retain(|&mut e| {
                    e.as_usize() < live && var_children_fingerprint(children, &nodes.get(e)) == fp
                });
            } else {
                b.retain(|&mut e| e.as_usize() < live);
            }
            b.sort_unstable_by_key(|e| e.as_usize());
            b.dedup();
        }
        self.spill[ix].push(id);
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
        self.push_hint(fp, lid);
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

        // Collision probe excluding this node (see the fixed-arity twin: a
        // self-hint from earlier content is not a collision), then hint the
        // new content. The old hint stays for restore to revalidate.
        if let Some(existing_gid) = self.probe_hints(node.op(), &buf[..new_len], Some(local_id)) {
            collisions.push((gid, existing_gid));
        }

        self.push_hint(new_fp, local_id);
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
        let token = PoolCacheToken {
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
            frame_index: self.frames.len(),
        };
        self.frames.push(CacheFrame);
        token
    }

    pub fn restore(&mut self, token: PoolCacheToken) {
        let _frame = *self
            .frames
            .get(token.frame_index)
            .expect("restore: token minted by this cache's own mark, and not already spent");
        assert!(
            self.nodes.is_valid_token(&token.nodes),
            "restore: node-arena token is not restorable"
        );
        assert!(
            self.children.is_valid_token(&token.children),
            "restore: child-pool token is not restorable"
        );
        if let (Some(h), Some(tok)) = (&self.history_nodes, token.history_nodes.as_ref()) {
            assert!(
                h.is_valid_token(tok),
                "restore: history token is not restorable"
            );
        }
        if let (Some(h), Some(tok)) = (&self.history_children, token.history_children.as_ref()) {
            assert!(
                h.is_valid_token(tok),
                "restore: history token is not restorable"
            );
        }
        // No index maintenance: hints self-correct against the rolled-back
        // arena and child pool (see the fixed-arity restore above). A
        // pool-only recanonize is covered because validity reads through the
        // span into the pool, which rolls back here too.
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
        self.frames.truncate(token.frame_index);
        #[cfg(debug_assertions)]
        debug_assert!(
            self.index_is_complete(),
            "restore left the hashcons hint index incomplete"
        );
    }

    /// See [`FixedArityCache::index_is_complete`].
    #[cfg(debug_assertions)]
    fn index_is_complete(&self) -> bool {
        let count = self.nodes.len().as_usize();
        let mut elems: Vec<C> = Vec::new();
        for i in 0..count {
            let n = self.nodes.get(L::from_usize(i));
            elems.clear();
            let (s, e) = n.span();
            for j in s..e {
                elems.push(self.children.get(j));
            }
            if self.probe(n.op(), &elems).is_none() {
                return false;
            }
        }
        true
    }

    fn children_eq(&self, node: &VariableArityNode<G, O>, elems: &[C]) -> bool {
        let (start, end) = node.span();
        if end - start != elems.len() {
            return false;
        }
        (0..elems.len()).all(|i| self.children.get(start + i) == elems[i])
    }

    fn fingerprint(&self, op: &O, elems: &[C]) -> Fingerprint {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        elems.hash(&mut h);
        fold32(h.finish())
    }
}

/// Fingerprint of a variable-arity node's CURRENT content, reading through
/// the child pool. Free function (not a method) so compaction can call it
/// under a split borrow of the pool and the node arena. Matches
/// `VariableArityCache::fingerprint` on the same content: a slice hash is a
/// length prefix followed by the elements.
fn var_children_fingerprint<G, O, C, const TRACK: bool>(
    children: &crate::containers::VecD<C, usize, TRACK>,
    node: &VariableArityNode<G, O>,
) -> Fingerprint
where
    G: DenseId + Hash,
    O: DenseId + Hash,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
{
    let mut h = rapidhash::fast::RapidHasher::default();
    node.op().hash(&mut h);
    let (start, end) = node.span();
    (end - start).hash(&mut h);
    for i in start..end {
        children.get(i).hash(&mut h);
    }
    fold32(h.finish())
}

// ---------------------------------------------------------------------------
// LitCache<G, O, V, L, TRACK>
// ---------------------------------------------------------------------------

pub struct LitCache<G: DenseId, O: DenseId, V: DenseId, L: DenseId, const TRACK: bool = true> {
    nodes: crate::containers::VecD<LitNode<G, O, V>, L, TRACK>,
    /// Hint index; see [`FixedArityCache::index`]. Literal content never
    /// changes, so the only staleness here is truncated ids after a restore.
    index: hashbrown::HashMap<FpKey, HintSlot, PassthroughBuildHasher>,
    /// Spilled hint buckets; `HintSlot` values with the spill tag index here.
    spill: Vec<HintBucket<L>>,
    frames: Vec<CacheFrame>,
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
            nodes: crate::containers::VecD::new_kind(crate::containers::env_diff_store_kind()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            spill: Vec::new(),
            frames: Vec::new(),
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
        let slot = *self.index.get(&FpKey(fp))?;
        let live = self.nodes.len().as_usize();
        let check = |id: L| -> Option<G> {
            if id.as_usize() >= live {
                return None;
            }
            let n = self.nodes.get(id);
            (n.op() == op && n.lit == lit).then(|| n.global_id())
        };
        match slot.as_single() {
            Some(raw) => check(L::from_usize(raw)),
            None => self.spill[slot.spill_index()]
                .iter()
                .find_map(|&id| check(id)),
        }
    }

    pub fn insert(&mut self, global_id: G, op: O, lit: V) -> L {
        let node = LitNode::new(global_id, op, lit);
        let fp = self.fingerprint(&op, &lit);
        let lid = self.nodes.len();
        self.nodes.try_push(node).expect("push: within index word");
        // Same single/spill protocol as the node caches; literal content
        // never changes, so compaction is bounds + dedup only.
        let key = FpKey(fp);
        match self.index.get(&key).copied() {
            None => {
                self.index.insert(key, HintSlot::single(lid.as_usize()));
            }
            Some(slot) => {
                if let Some(raw) = slot.as_single() {
                    if raw >= lid.as_usize() {
                        // Equal: duplicate hint, nothing to do. Greater: a
                        // dead single from a restore (lid is the newest live
                        // id), replaced in place as in the node caches.
                        if raw > lid.as_usize() {
                            self.index.insert(key, HintSlot::single(lid.as_usize()));
                        }
                    } else {
                        let ix = self.spill.len();
                        let mut b = HintBucket::<L>::new();
                        b.push(L::from_usize(raw));
                        b.push(lid);
                        self.spill.push(b);
                        self.index.insert(key, HintSlot::spilled(ix));
                    }
                } else {
                    let ix = slot.spill_index();
                    let b = &mut self.spill[ix];
                    if b.len() >= HINT_COMPACT_LEN && b.len().is_power_of_two() {
                        let live = lid.as_usize() + 1;
                        b.retain(|&mut e| e.as_usize() < live);
                        b.sort_unstable_by_key(|e| e.as_usize());
                        b.dedup();
                    }
                    b.push(lid);
                }
            }
        }
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
        let token = CacheToken {
            nodes: self
                .nodes
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            history: None,
            frame_index: self.frames.len(),
        };
        self.frames.push(CacheFrame);
        token
    }

    pub fn restore(&mut self, token: CacheToken) {
        let _frame = *self
            .frames
            .get(token.frame_index)
            .expect("restore: token minted by this cache's own mark, and not already spent");
        // No index maintenance: truncated ids fail the probe's bounds check.
        self.nodes
            .try_restore(token.nodes)
            .expect("restore: token minted by this container's own mark");
        self.frames.truncate(token.frame_index);
        #[cfg(debug_assertions)]
        debug_assert!(
            self.index_is_complete(),
            "restore left the literal hint index incomplete"
        );
    }

    /// See [`FixedArityCache::index_is_complete`].
    #[cfg(debug_assertions)]
    fn index_is_complete(&self) -> bool {
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let n = self.nodes.get(L::from_usize(i));
            if self.probe(n.op(), n.lit).is_none() {
                return false;
            }
        }
        true
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

    // -- mark / restore --

    const SHRINK: ShrinkPolicy = ShrinkPolicy::Never;

    /// Restore drops the entries of the nodes the scope added and keeps the
    /// rest, which is what makes a later `probe` answer for the restored graph.
    #[test]
    fn restore_drops_the_post_mark_suffix() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        let token = c.mark(SHRINK);
        c.probe_or_insert(id(20), op, [id(3), id(4)]);
        assert!(c.probe(&op, &[id(3), id(4)]).is_some());

        c.restore(token);
        assert_eq!(c.len(), Plain2Id::new(1));
        assert_eq!(c.probe(&op, &[id(1), id(2)]), Some(id(10)));
        assert!(c.probe(&op, &[id(3), id(4)]).is_none());
        // The freed local id is reusable and does not collide with the entry
        // the discarded node left behind, because there is none.
        c.probe_or_insert(id(30), op, [id(5), id(6)]);
        assert_eq!(c.probe(&op, &[id(5), id(6)]), Some(id(30)));
    }

    /// A pre-mark node recanonized inside the scope is filed under its new key
    /// while the scope runs and back under the mark's key after restore.
    #[test]
    fn restore_rekeys_a_recanonized_pre_mark_node() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        let token = c.mark(SHRINK);
        c.recanonize_node::<PlainCanon>(
            Plain2Id::new(0),
            |g| if g == id(2) { id(1) } else { g },
            &mut Vec::new(),
            &mut Vec::new(),
        );
        assert!(c.probe(&op, &[id(1), id(1)]).is_some());
        assert!(c.probe(&op, &[id(1), id(2)]).is_none());

        c.restore(token);
        assert_eq!(c.probe(&op, &[id(1), id(2)]), Some(id(10)));
        assert!(c.probe(&op, &[id(1), id(1)]).is_none());
    }

    /// Same for a variable-arity node, whose content lives in the shared child
    /// pool: the pool rolls back with the arena and the key follows it.
    #[test]
    fn restore_rekeys_a_recanonized_variable_arity_node() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, SetNodeId>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, &[id(1), id(2), id(3)]);
        let token = c.mark(SHRINK);
        c.recanonize_node::<SetCanon>(
            SetNodeId::new(0),
            |g| if g == id(2) { id(1) } else { g },
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            crate::canon::CanonMode::PLAIN,
        );
        assert!(c.probe(op, &[id(1), id(3)]).is_some());

        c.restore(token);
        assert_eq!(c.probe(op, &[id(1), id(2), id(3)]), Some(id(10)));
        assert!(c.probe(op, &[id(1), id(3)]).is_none());
    }

    /// Nested marks: restoring the outer token past an unrestored inner mark
    /// has to undo both the inner suffix and a pre-outer-mark node the inner
    /// scope re-keyed.
    #[test]
    fn restore_past_an_open_inner_mark() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        let outer = c.mark(SHRINK);
        c.probe_or_insert(id(20), op, [id(3), id(4)]);
        let _inner = c.mark(SHRINK);
        c.probe_or_insert(id(30), op, [id(5), id(6)]);
        c.recanonize_node::<PlainCanon>(
            Plain2Id::new(0),
            |g| if g == id(2) { id(7) } else { g },
            &mut Vec::new(),
            &mut Vec::new(),
        );

        c.restore(outer);
        assert_eq!(c.len(), Plain2Id::new(1));
        assert_eq!(c.probe(&op, &[id(1), id(2)]), Some(id(10)));
        assert!(c.probe(&op, &[id(1), id(7)]).is_none());
        assert!(c.probe(&op, &[id(3), id(4)]).is_none());
        assert!(c.probe(&op, &[id(5), id(6)]).is_none());
    }

    /// A node added after the OUTER mark and re-keyed under the inner scope
    /// appears in the pending set of an outer restore (the inner stratum's
    /// capture names it) yet belongs to the suffix the outer restore deletes.
    /// The restore must skip it instead of re-reading the rolled-back slot
    /// (the corpus-measured out-of-bounds abort in `notify_backtrack`). The
    /// in-restore `index_matches_rebuild` assertion checks the resulting
    /// index against the from-scratch rebuild.
    #[test]
    fn restore_to_outer_skips_a_rekeyed_inner_suffix_node() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        let outer = c.mark(SHRINK);
        c.probe_or_insert(id(20), op, [id(3), id(4)]);
        let _inner = c.mark(SHRINK);
        // Re-key the post-outer-mark node: its local id (1) passes the inner
        // frame's saved_len filter (2) but not the outer's (1).
        c.recanonize_node::<PlainCanon>(
            Plain2Id::new(1),
            |g| if g == id(4) { id(5) } else { g },
            &mut Vec::new(),
            &mut Vec::new(),
        );
        assert!(c.probe(&op, &[id(3), id(5)]).is_some());

        c.restore(outer);
        assert_eq!(c.len(), Plain2Id::new(1));
        assert_eq!(c.probe(&op, &[id(1), id(2)]), Some(id(10)));
        assert!(c.probe(&op, &[id(3), id(4)]).is_none());
        assert!(c.probe(&op, &[id(3), id(5)]).is_none());
    }

    /// Same scenario through the pool-backed cache.
    #[test]
    fn pool_restore_to_outer_skips_a_rekeyed_inner_suffix_node() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, SetNodeId>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, &[id(1), id(2), id(3)]);
        let outer = c.mark(SHRINK);
        c.probe_or_insert(id(20), op, &[id(4), id(5), id(6)]);
        let _inner = c.mark(SHRINK);
        c.recanonize_node::<SetCanon>(
            SetNodeId::new(1),
            |g| if g == id(6) { id(7) } else { g },
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            crate::canon::CanonMode::PLAIN,
        );
        assert!(c.probe(op, &[id(4), id(5), id(7)]).is_some());

        c.restore(outer);
        assert_eq!(c.probe(op, &[id(1), id(2), id(3)]), Some(id(10)));
        assert!(c.probe(op, &[id(4), id(5), id(6)]).is_none());
        assert!(c.probe(op, &[id(4), id(5), id(7)]).is_none());
    }

    /// A scope that adds more than a quarter of the arena takes the rebuild
    /// fallback, and lands on the same index the incremental path would build.
    #[test]
    fn restore_falls_back_to_rebuild_on_a_large_suffix() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        let token = c.mark(SHRINK);
        for k in 0..10 {
            c.probe_or_insert(id(100 + k), op, [id(200 + k), id(0)]);
        }
        assert!(!restore_incrementally(10, 0, 1));

        c.restore(token);
        assert_eq!(c.len(), Plain2Id::new(1));
        assert_eq!(c.probe(&op, &[id(1), id(2)]), Some(id(10)));
        assert!(c.probe(&op, &[id(200), id(0)]).is_none());
    }

    /// The check `restore` asserts on rejects a missing hint. Without this,
    /// an index that never diverges and a check that never looks are the same
    /// test result.
    #[cfg(debug_assertions)]
    #[test]
    fn completeness_check_rejects_a_missing_hint() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(2)]);
        assert!(c.index_is_complete());

        let fp = c.fingerprint(&op, &[id(1), id(2)]);
        c.index.remove(&FpKey(fp));
        assert!(
            !c.index_is_complete(),
            "a node whose content no probe can find is incomplete"
        );
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
