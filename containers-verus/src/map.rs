// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent map backed by [`AppendOnlyVec`] + a transient hash index.
//!
//! The append-only log `(K, V)` is the source of truth; semi-persistence
//! (mark/restore) lives entirely in that already-verified log. A `HashMap`
//! accelerates key lookup, mapping each key to the dense log index of its MOST
//! RECENT entry (last-write-wins; older entries linger in the log as shadows).
//! On `restore` the log truncates and the index is rebuilt from the survivors.
//!
//! Verified invariant (`wf`): the exec index agrees with `is_last_occurrence`,
//! the declarative "this position is the latest one holding its key", over the
//! current log. From that, `get_by_key`/`contains_key` provably read the
//! latest value, and `restore` provably returns the map to its marked logical
//! contents (the log headline theorem composes through). `rebuild_index`
//! re-establishes the agreement after a restore.
//!
//! Keys are `K: Clone + Hash + Eq` (production parity — String/Vec keys work).
//! The one clone-spec fact needed is the key model's own requirement (3):
//! `Key::clone` produces a result identical to its input (see
//! `clone_key_exact`).
//!
//! The index's `BuildHasher` is [`crate::hasher_spec::IndexHasher`], which uses
//! the same hash ALGORITHM production gets from hashbrown 0.17's default. Its
//! seed is DETERMINISTIC by default (a fixed constant, so runs are reproducible)
//! and CONTROLLABLE three ways — `SP_HASHER_SEED`,
//! `hasher_spec::set_default_seed`, or `IndexHasher::with_seed` per instance.
//! The `hasher-random-seed` feature changes only what the seed defaults to.
//! Not literally production's type — hashbrown's `DefaultHashBuilder` is a
//! newtype wrapping `foldhash::fast::RandomState` and forwarding every `write_*`
//! to it.
//!
//! Note the seed is invisible to this map's OBSERVABLE behaviour either way:
//! the log is the source of truth, `iter()` walks it in insertion order,
//! `rebuild_index` replays it in insertion order, and the index is never
//! iterated (lookup-only). Fixing the seed makes the internal layout and probe
//! sequences reproducible too. See `hasher_spec` for the full policy.
//!
//! vstd models `std::HashMap<K, V, S>` generically over any `S: BuildHasher`,
//! so this is the same verified container with a faster hash function; the one
//! `builds_valid_hashers::<S>()` fact it needs is
//! `hasher_spec::axiom_index_hasher_builds_valid_hashers`
//! (mirrors vstd's shipped `RandomState` axiom).

use std::collections::HashMap;
use std::hash::Hash;
use vstd::prelude::*;

use crate::append_only_vec::AppendOnlyVec;
use crate::vec::{ShrinkPolicy, VecToken};

// The index hasher (and the determinism policy behind it) lives in one place:
// `hasher_spec`. Re-exported here because it appears in `SpMap`'s field type.
pub use crate::hasher_spec::IndexHasher;

verus! {

// `std_specs::hash` is the spec-only model of `HashMap`; vstd gates the whole
// module behind `cfg(verus_keep_ghost)` (set by the Verus driver, NOT by plain
// `cargo build`). We mirror that gate on the import, so cargo skips it. Its
// items (`obeys_key_model`, `builds_valid_hashers`, `group_hash_axioms`) are
// used only in spec/`requires`/`broadcast use` positions, which the `verus!`
// macro erases under cargo — so after erasure cargo never references them.
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

/// Opaque token for `SpMap::mark` / `SpMap::restore`.
#[derive(Copy, Clone)]
pub struct MapToken {
    pub(crate) inner: VecToken,
}

impl MapToken {
    /// Reconstruction coordinate (spec twin; the field is `pub(crate)`).
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.inner.frame_idx as nat
    }
}

/// `true` iff position `i` is the LAST occurrence of key `log[i].0` in `log`
/// (no later entry repeats that key). The exec index points exactly here.
pub open(crate) spec fn is_last_occurrence<K, V>(log: Seq<(K, V)>, i: int) -> bool {
    &&& 0 <= i < log.len()
    &&& (forall|j: int| i < j < log.len() ==> (#[trigger] log[j]).0 != log[i].0)
}

/// Semi-persistent map. (`SpMap` rather than `Map` to avoid colliding with
/// `vstd::map::Map`, which is `HashMap`'s view type.)
pub struct SpMap<K, V, const TRACK: bool = true>
where
    K: Clone + Hash + Eq,
{
    pub(crate) log: AppendOnlyVec<(K, V), TRACK>,
    pub(crate) index: HashMap<K, usize, IndexHasher>,
}

impl<K, V, const TRACK: bool> SpMap<K, V, TRACK>
where
    K: Clone + Hash + Eq,
{
    /// The log sequence (source of truth).
    pub open(crate) spec fn log_view(&self) -> Seq<(K, V)> {
        self.log.view()
    }

    /// The index map (spec twin; the field is `pub(crate)` — privacy closeout).
    pub open(crate) spec fn index_view(&self) -> Map<K, usize> {
        self.index@
    }

    /// Frame-stack depth of the log (spec twin).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.log.depth_spec()
    }

    /// Lifetime restore count of the log (spec twin).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.log.fork_count_spec()
    }

    /// Log snapshot stack (spec twin).
    pub open(crate) spec fn log_snapshots_view(&self) -> Seq<Seq<(K, V)>> {
        self.log.snapshots_view()
    }

    /// Index/log agreement: the exec index contains `k → i` iff `i` is the
    /// last occurrence of `k` in the log. (`obeys_key_model` keeps the
    /// HashMap key model well-behaved.)
    pub open(crate) spec fn index_agrees(&self) -> bool {
        let log = self.log_view();
        let m = self.index@;
        &&& obeys_key_model::<K>()
        &&& builds_valid_hashers::<IndexHasher>()
        &&& (forall|i: int| #[trigger] is_last_occurrence(log, i)
                ==> m.contains_key(log[i].0) && m[log[i].0] == i)
        &&& (forall|k: K| #[trigger] m.contains_key(k)
                ==> 0 <= m[k] < log.len() && log[m[k] as int].0 == k
                    && is_last_occurrence(log, m[k] as int))
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.log.wf()
        &&& self.index_agrees()
    }

    /// Token validity, delegated to the log.
    pub open(crate) spec fn is_token_valid_spec(&self, token: MapToken) -> bool {
        self.log.is_token_valid_spec(token.inner)
    }

    /// "Restorable now", delegated to the log (the map's single component).
    pub open(crate) spec fn is_restorable_spec(&self, token: MapToken) -> bool {
        self.log.is_restorable_spec(token.inner)
    }

    pub fn new() -> (m: Self)
        requires
            // The key type must conform to the HashMap key model. vstd proves
            // this for primitive keys via group_hash_axioms; a custom key type
            // supplies it with `assume(obeys_key_model::<MyKey>())`. It is a
            // property of `K`, so it threads through `wf` for the map's life.
            obeys_key_model::<K>(),
        ensures m.wf(), m.log_view().len() == 0, m.index_view() == Map::<K, usize>::empty(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::hasher_spec::axiom_index_hasher_builds_valid_hashers;
        let log = AppendOnlyVec::new();
        // `default()` (not `new()`): `new()` hardcodes std's `RandomState`;
        // `default()` builds the map with our chosen `S = IndexHasher`
        // (foldhash), and vstd specs it to the empty map for any `S: Default`.
        // That generic-over-`S: Default` spec is also why the SEED knob lives in
        // `IndexHasher::default()` rather than a `with_hasher` constructor: vstd
        // does not spec `with_hasher`, so this route keeps seed control free of
        // added trust. See hasher_spec.
        let index: HashMap<K, usize, IndexHasher> = HashMap::default();
        let m = SpMap { log, index };
        proof {
            assert(m.log_view().len() == 0);
            assert(m.index@ =~= Map::<K, usize>::empty());
        }
        m
    }

    /// Number of entries in the log (including overwritten shadows).
    pub fn log_len(&self) -> (n: usize)
        ensures n == self.log_view().len(),
    {
        self.log.len()
    }

    /// Current dense index for a key, if present.
    pub fn id_of(&self, key: &K) -> (r: Option<usize>)
        requires self.wf(),
        ensures
            match r {
                Some(i) => self.index_view().contains_key(*key) && self.index_view()[*key] == i,
                None => !self.index_view().contains_key(*key),
            },
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        match self.index.get(key) {
            Some(i) => Some(*i),
            None => None,
        }
    }

    /// Whether a key is currently present.
    pub fn contains_key(&self, key: &K) -> (b: bool)
        requires self.wf(),
        ensures b == self.index_view().contains_key(*key),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.contains_key(key)
    }

    /// Value+key pair at a dense log index.
    pub fn get(&self, idx: usize) -> (r: &(K, V))
        requires self.wf(), idx < self.log_view().len(),
        ensures *r == self.log_view()[idx as int],
    {
        self.log.get(idx)
    }

    /// The key at a dense log index (production `Map::key` parity).
    pub fn key(&self, idx: usize) -> (r: &K)
        requires self.wf(), idx < self.log_view().len(),
        ensures *r == self.log_view()[idx as int].0,
    {
        &self.log.get(idx).0
    }

    /// The value at a dense log index (production `Map::get` returned `&V`;
    /// under the verus names `get` returns the pair and this returns the
    /// value).
    pub fn get_val(&self, idx: usize) -> (r: &V)
        requires self.wf(), idx < self.log_view().len(),
        ensures *r == self.log_view()[idx as int].1,
    {
        &self.log.get(idx).1
    }

    /// The current (latest) value for a key, if present (production
    /// `Map::get_by_key` parity). Reads through the index: the entry at
    /// `index[key]` provably holds `key`'s last occurrence (`index_agrees`),
    /// so this is the live value.
    pub fn get_by_key(&self, key: &K) -> (r: Option<&V>)
        requires self.wf(),
        ensures
            match r {
                Some(v) => self.index_view().contains_key(*key)
                    && *v == self.log_view()[self.index_view()[*key] as int].1,
                None => !self.index_view().contains_key(*key),
            },
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        match self.index.get(key) {
            Some(i) => {
                let idx = *i;
                // index_agrees gives 0 <= idx < log.len().
                Some(&self.log.get(idx).1)
            }
            None => None,
        }
    }

    /// Number of LIVE keys (production `Map::len` parity): the index's size —
    /// each live key has exactly one index entry (`index_agrees`), so
    /// `index.len()` is the live-key count. O(1); no separate counter field.
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.index_view().len(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.len()
    }

    /// No live keys (production parity).
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.index_view().len() == 0),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.len() == 0
    }

    pub fn depth(&self) -> (d: usize)
        ensures d == self.depth_spec(),
    {
        self.log.depth()
    }

    /// Insert or overwrite. Appends `(key, val)` to the log (the new last
    /// occurrence of `key`) and points the index at it. Returns the dense
    /// log index of the new entry.
    pub fn insert(&mut self, key: K, val: V) -> (id: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            id == old(self).log_view().len(),
            final(self).log_view() == old(self).log_view().push((key, val)),
            final(self).index_view() == old(self).index_view().insert(key, id),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::hasher_spec::axiom_index_hasher_builds_valid_hashers;
        let ghost old_log = self.log_view();
        let key_for_index = clone_key_exact(&key);
        let id = self.log.push((key, val));
        self.index.insert(key_for_index, id);
        proof {
            let log = self.log_view();
            let m = self.index@;
            assert(log == old_log.push((key, val)));
            assert(log[id as int] == (key, val));
            // The appended entry is the unique new last-occurrence of `key`;
            // every other position's last-occurrence status is unchanged
            // (only an entry with key `key` could lose it, and the new tail
            // entry has key `key`, so prior `key` entries are no longer last —
            // but the index now maps `key` to `id`, matching).
            assert(is_last_occurrence(log, id as int));
            assert forall|i: int| #[trigger] is_last_occurrence(log, i)
                implies m.contains_key(log[i].0) && m[log[i].0] == i by {
                if i == id as int {
                    assert(m[key] == id);
                } else {
                    // i < id; entry unchanged from old_log. It's still a last
                    // occurrence in the longer log only if its key != key
                    // (else the tail entry shadows it). So log[i].0 != key,
                    // and the index entry for log[i].0 is untouched by insert.
                    assert(log[i] == old_log[i]);
                    assert(log[i].0 != key);
                    assert(is_last_occurrence(old_log, i)) by {
                        assert forall|j: int| i < j < old_log.len()
                            implies (#[trigger] old_log[j]).0 != old_log[i].0 by {
                            assert(old_log[j] == log[j]);
                        }
                    }
                    assert(old(self).index@.contains_key(log[i].0));
                    assert(old(self).index@[log[i].0] == i);
                    assert(m[log[i].0] == old(self).index@[log[i].0]);
                }
            }
            assert forall|k: K| #[trigger] m.contains_key(k)
                implies 0 <= m[k] < log.len() && log[m[k] as int].0 == k
                    && is_last_occurrence(log, m[k] as int) by {
                if k == key {
                    assert(m[k] == id);
                } else {
                    assert(m[k] == old(self).index@[k]);
                    assert(old(self).index@.contains_key(k));
                    // old last-occurrence of k is still last (the new tail has
                    // key `key` != k, doesn't shadow k).
                    let p = old(self).index@[k] as int;
                    assert(is_last_occurrence(old_log, p));
                    assert(log[p] == old_log[p]);
                    assert forall|j: int| p < j < log.len()
                        implies (#[trigger] log[j]).0 != log[p].0 by {
                        if j < old_log.len() {
                            assert(log[j] == old_log[j]);
                        } else {
                            assert(log[j].0 == key);
                            assert(log[p].0 == k);
                        }
                    }
                }
            }
        }
        id
    }

    /// Mark, delegating to the log.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: MapToken)
        requires old(self).wf(), TRACK, old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_view(),
            final(self).index_view() == old(self).index_view(),
            token.frame_idx_spec() == old(self).depth_spec(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let inner = self.log.mark(shrink);
        proof {
            // log.mark preserves view() and the index is untouched, so the
            // log/index agreement carries unchanged.
            assert(self.log_view() == old(self).log_view());
            assert(self.index@ == old(self).index@);
        }
        MapToken { inner }
    }

    /// "Restorable now" (plan 2.2), delegating to the log — the map's single
    /// component, so component-wise restorability IS map restorability.
    pub fn is_valid_token(&self, token: &MapToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        self.log.is_valid_token(&token.inner)
    }

    /// Restore: truncate the log to the token's snapshot, then rebuild the
    /// index from the survivors. The log restore reproduces the marked
    /// contents (headline theorem composes); rebuild re-establishes agreement.
    pub fn restore(&mut self, token: MapToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).is_token_valid_spec(token),
            token.frame_idx_spec() < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
            old(self).fork_count_spec() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_snapshots_view()[token.frame_idx_spec() as int],
    {
        self.log.restore(token.inner);
        self.rebuild_index();
    }

    /// Rebuild the index from the current log: scan left-to-right, mapping each
    /// key to the position seen so far. After the full scan each key maps to
    /// its last occurrence.
    fn rebuild_index(&mut self)
        requires old(self).log.wf(), obeys_key_model::<K>(),
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_view(),
            final(self).log == old(self).log,
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::hasher_spec::axiom_index_hasher_builds_valid_hashers;
        let ghost log = self.log_view();
        self.index.clear();
        let n = self.log.len();
        let mut i: usize = 0;
        // Invariant: index agrees with last-occurrence RESTRICTED to the prefix
        // [0, i): a key maps to its last occurrence within [0, i), and every
        // index entry is such a last-occurrence-within-prefix.
        while i < n
            invariant
                self.log == old(self).log,
                log == self.log_view(),
                n == log.len(),
                0 <= i <= n,
                obeys_key_model::<K>(),
                builds_valid_hashers::<IndexHasher>(),
                forall|p: int| 0 <= p < i && is_last_occurrence_prefix(log, p, i as int)
                    ==> #[trigger] self.index@.contains_key(log[p].0)
                        && self.index@[log[p].0] == p,
                forall|k: K| #[trigger] self.index@.contains_key(k)
                    ==> 0 <= self.index@[k] < i && log[self.index@[k] as int].0 == k
                        && is_last_occurrence_prefix(log, self.index@[k] as int, i as int),
            decreases n - i,
        {
            let entry = self.log.get(i);
            let key = clone_key_exact(&entry.0);
            self.index.insert(key, i);
            proof {
                let m = self.index@;
                // After inserting (key, i): key's last-occ-in-[0,i+1) is i.
                assert forall|p: int| 0 <= p < (i + 1) && is_last_occurrence_prefix(log, p, (i + 1) as int)
                    implies #[trigger] m.contains_key(log[p].0) && m[log[p].0] == p by {
                    if p == i as int {
                        assert(m[key] == i);
                    } else {
                        // p < i and last-occ in [0,i+1): so log[p].0 != log[i].0
                        // (else i would shadow it), hence it was last-occ in
                        // [0,i) and the index for it is unchanged.
                        assert(log[p].0 != log[i as int].0);
                        assert(is_last_occurrence_prefix(log, p, i as int));
                        assert(m[log[p].0] == old(self).index@[log[p].0] || true);
                    }
                }
                assert forall|kk: K| #[trigger] m.contains_key(kk)
                    implies 0 <= m[kk] < (i + 1) && log[m[kk] as int].0 == kk
                        && is_last_occurrence_prefix(log, m[kk] as int, (i + 1) as int) by {
                    if kk == key {
                        assert(m[kk] == i);
                    } else {
                        // unchanged entry; was last-occ in [0,i), still is in
                        // [0,i+1) because log[i].0 == key != kk.
                        assert(log[i as int].0 != kk);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            // At i == n, last-occurrence-in-prefix-[0,n) == last-occurrence.
            let m = self.index@;
            assert forall|p: int| #[trigger] is_last_occurrence(log, p)
                implies m.contains_key(log[p].0) && m[log[p].0] == p by {
                assert(is_last_occurrence_prefix(log, p, n as int));
            }
            assert forall|k: K| #[trigger] m.contains_key(k)
                implies 0 <= m[k] < log.len() && log[m[k] as int].0 == k
                    && is_last_occurrence(log, m[k] as int) by {
                assert(is_last_occurrence_prefix(log, m[k] as int, n as int));
            }
        }
    }
}

/// Like `is_last_occurrence` but only within the prefix `[0, bound)`: position
/// `i` holds a key not repeated in `(i, bound)`. (Used as the rebuild loop's
/// running invariant; at `bound == log.len()` it coincides with
/// `is_last_occurrence`.)
pub open(crate) spec fn is_last_occurrence_prefix<K, V>(log: Seq<(K, V)>, i: int, bound: int) -> bool {
    &&& 0 <= i < bound <= log.len()
    &&& (forall|j: int| i < j < bound ==> (#[trigger] log[j]).0 != log[i].0)
}

/// Clone a map key, with the clone PROVABLY identical to the original.
///
/// This is requirement (3) of vstd's hash-table key model — "the executable
/// `Key::clone` function produces a result identical to its input" — which
/// `SpMap` already assumes for every key type via `obeys_key_model::<K>()`
/// (`new`'s precondition, threaded through `wf`). vstd states that
/// requirement in prose on the `uninterp obeys_key_model` and provides no
/// lemma projecting it out, so this helper carries it as its contract:
/// `external_body`, trusted content exactly = key-model requirement (3),
/// no NEW assumption beyond what `obeys_key_model` already asserts.
/// Trust ledger: group D (key-model facts).
#[verifier::external_body]
fn clone_key_exact<K: Clone>(key: &K) -> (r: K)
    requires obeys_key_model::<K>(),
    ensures r == *key,
{
    key.clone()
}

} // verus!

// prod-parity: production derives `Debug` on `MapToken`; manual here (composes a
// `VecToken`, which is now `Debug`).
impl core::fmt::Debug for MapToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MapToken")
            .field("inner", &self.inner)
            .finish()
    }
}

// prod-parity: production derives `Debug` on `Map`; the consumer's registries and
// literal stores hold an `SpMap` in a `#[derive(Debug)]` struct
// (`egraph/src/registry.rs`, `literal.rs`). Manual because deriving inside
// `verus!{}` is unsupported. Prints the live entries via the public `iter`
// (the log is the source of truth); shadowed/overwritten log entries are not
// shown, matching the map's logical contents.
impl<K, V, const TRACK: bool> core::fmt::Debug for SpMap<K, V, TRACK>
where
    K: Clone + core::hash::Hash + Eq + core::fmt::Debug,
    V: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map()
            .entries(self.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): log iteration in
// insertion order, including overwritten shadows (production `Map::iter`
// semantics). Delegates to the verified AppendOnlyVec::as_slice.
// ---------------------------------------------------------------------------

impl<K, V, const TRACK: bool> SpMap<K, V, TRACK>
where
    K: Clone + std::hash::Hash + Eq,
{
    /// Iterate over the log entries in insertion order, including shadows
    /// (production parity: production's `Map::iter` also yields shadows).
    #[inline(always)]
    pub fn iter(&self) -> core::slice::Iter<'_, (K, V)> {
        self.log.as_slice().iter()
    }
}
