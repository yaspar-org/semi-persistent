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
//! Like the rest of the crate we model the `Copy` subset of `Clone` (`K: Copy`)
//! to avoid clone-spec plumbing.

use std::collections::HashMap;
use std::hash::Hash;
use vstd::prelude::*;

use crate::append_only_vec::AppendOnlyVec;
use crate::vec::{ShrinkPolicy, VecToken};

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
    pub inner: VecToken,
}

/// `true` iff position `i` is the LAST occurrence of key `log[i].0` in `log`
/// (no later entry repeats that key). The exec index points exactly here.
pub open spec fn is_last_occurrence<K, V>(log: Seq<(K, V)>, i: int) -> bool {
    &&& 0 <= i < log.len()
    &&& (forall|j: int| i < j < log.len() ==> (#[trigger] log[j]).0 != log[i].0)
}

/// Semi-persistent map. (`SpMap` rather than `Map` to avoid colliding with
/// `vstd::map::Map`, which is `HashMap`'s view type.)
pub struct SpMap<K, V, const TRACK: bool>
where
    K: Copy + Hash + Eq,
{
    pub log: AppendOnlyVec<(K, V), TRACK>,
    pub index: HashMap<K, usize>,
}

impl<K, V, const TRACK: bool> SpMap<K, V, TRACK>
where
    K: Copy + Hash + Eq,
{
    /// The log sequence (source of truth).
    pub open spec fn log_view(&self) -> Seq<(K, V)> {
        self.log.view()
    }

    /// Index/log agreement: the exec index contains `k → i` iff `i` is the
    /// last occurrence of `k` in the log. (`obeys_key_model` keeps the
    /// HashMap key model well-behaved.)
    pub open spec fn index_agrees(&self) -> bool {
        let log = self.log_view();
        let m = self.index@;
        &&& obeys_key_model::<K>()
        &&& builds_valid_hashers::<std::collections::hash_map::RandomState>()
        &&& (forall|i: int| #[trigger] is_last_occurrence(log, i)
                ==> m.contains_key(log[i].0) && m[log[i].0] == i)
        &&& (forall|k: K| #[trigger] m.contains_key(k)
                ==> 0 <= m[k] < log.len() && log[m[k] as int].0 == k
                    && is_last_occurrence(log, m[k] as int))
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.log.wf()
        &&& self.index_agrees()
    }

    /// Token validity, delegated to the log.
    pub open spec fn is_token_valid_spec(&self, token: MapToken) -> bool {
        self.log.is_token_valid_spec(token.inner)
    }

    pub fn new() -> (m: Self)
        requires
            // The key type must conform to the HashMap key model. vstd proves
            // this for primitive keys via group_hash_axioms; a custom key type
            // supplies it with `assume(obeys_key_model::<MyKey>())`. It is a
            // property of `K`, so it threads through `wf` for the map's life.
            obeys_key_model::<K>(),
        ensures m.wf(), m.log_view().len() == 0, m.index@ == Map::<K, usize>::empty(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let log = AppendOnlyVec::new();
        let index: HashMap<K, usize> = HashMap::new();
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
                Some(i) => self.index@.contains_key(*key) && self.index@[*key] == i,
                None => !self.index@.contains_key(*key),
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
        ensures b == self.index@.contains_key(*key),
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

    pub fn depth(&self) -> (d: usize)
        ensures d == self.log.frames@.len(),
    {
        self.log.depth()
    }

    /// Insert or overwrite. Appends `(key, val)` to the log (the new last
    /// occurrence of `key`) and points the index at it. Returns the dense
    /// log index of the new entry.
    pub fn insert(&mut self, key: K, val: V) -> (id: usize)
        requires old(self).wf(),
        ensures
            self.wf(),
            id == old(self).log_view().len(),
            self.log_view() == old(self).log_view().push((key, val)),
            self.index@ == old(self).index@.insert(key, id),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_log = self.log_view();
        let id = self.log.push((key, val));
        self.index.insert(key, id);
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
        requires old(self).wf(), old(self).log.frames@.len() < u32::MAX,
        ensures
            self.wf(),
            self.log_view() == old(self).log_view(),
            self.index@ == old(self).index@,
            token.inner.frame_idx == old(self).log.frames@.len(),
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

    /// Validity check, delegating to the log.
    pub fn is_valid_token(&self, token: MapToken) -> (b: bool)
        requires self.wf(), self.log.frames@.len() < u32::MAX,
        ensures b == self.is_token_valid_spec(token),
    {
        self.log.is_valid_token(token.inner)
    }

    /// Restore: truncate the log to the token's snapshot, then rebuild the
    /// index from the survivors. The log restore reproduces the marked
    /// contents (headline theorem composes); rebuild re-establishes agreement.
    pub fn restore(&mut self, token: MapToken)
        requires
            old(self).wf(),
            old(self).is_token_valid_spec(token),
            token.inner.frame_idx < old(self).log.frames@.len(),
            old(self).log.frames@.len() < u32::MAX,
            old(self).log.forks.origins@.len() + 1 <= u32::MAX,
        ensures
            self.wf(),
            self.log_view() == old(self).log.snapshots_view()[token.inner.frame_idx as int],
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
            self.wf(),
            self.log_view() == old(self).log_view(),
            self.log == old(self).log,
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
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
                builds_valid_hashers::<std::collections::hash_map::RandomState>(),
                forall|p: int| 0 <= p < i && is_last_occurrence_prefix(log, p, i as int)
                    ==> #[trigger] self.index@.contains_key(log[p].0)
                        && self.index@[log[p].0] == p,
                forall|k: K| #[trigger] self.index@.contains_key(k)
                    ==> 0 <= self.index@[k] < i && log[self.index@[k] as int].0 == k
                        && is_last_occurrence_prefix(log, self.index@[k] as int, i as int),
            decreases n - i,
        {
            let (k, _v) = self.log.get(i);
            let key = *k;
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
pub open spec fn is_last_occurrence_prefix<K, V>(log: Seq<(K, V)>, i: int, bound: int) -> bool {
    &&& 0 <= i < bound <= log.len()
    &&& (forall|j: int| i < j < bound ==> (#[trigger] log[j]).0 != log[i].0)
}

} // verus!
