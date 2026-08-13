// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent map backed by [`AppendOnlyVec`] + transient HashMap.
//!
//! The append-only log is the source of truth. A transient `HashMap`
//! accelerates key lookup. On `restore`, the log is truncated and the
//! `HashMap` is rebuilt from surviving entries.

use super::append_only_vec::AppendOnlyVec;
use super::token::VecToken;
use crate::dense_id::IndexLike;
use std::hash::Hash;

/// Opaque token for [`Map::mark`] / [`Map::restore`].
#[derive(Clone, Copy, Debug)]
pub struct MapToken(VecToken);

/// Semi-persistent map with mark/restore.
///
/// Insert appends `(K, V)` to the log and updates the HashMap.
/// Overwrites append a new entry (the old one stays in the log as a shadow).
/// On restore, the log truncates and the HashMap rebuilds from survivors.
/// Rebuild is O(surviving_len) — fine for small maps (registries, globals).
///
/// # Index width
///
/// `I` names a log position and so bounds the map, exactly as in
/// [`AppendOnlyVec`]. It is also the value type of the accelerating `HashMap`, which
/// is where the width actually pays: one entry per live key, so a registry keyed by
/// a 31-bit id space stores `u32` positions instead of `usize` and drops 4 bytes per
/// key. See [`AppendOnlyVec`]'s note for why the default is `usize`.
pub struct Map<K: Hash + Eq + Clone, V, I: IndexLike = usize, const TRACK: bool = true> {
    log: AppendOnlyVec<(K, V), I, TRACK>,
    index: hashbrown::HashMap<K, I>,
}

impl<K: Hash + Eq + Clone, V, I: IndexLike, const TRACK: bool> Map<K, V, I, TRACK> {
    pub fn new() -> Self {
        Self {
            log: AppendOnlyVec::new(),
            index: hashbrown::HashMap::new(),
        }
    }

    /// Insert or overwrite. Returns the dense log index of the new entry.
    ///
    /// # Panics
    ///
    /// If the log has no room left in `I`; see [`AppendOnlyVec::push`].
    /// Total-API twin (parity with the verified crate's shell): production's
    /// core panics on misuse, so the twin always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_insert(&mut self, key: K, val: V) -> Result<I, &'static str> {
        Ok(self.insert(key, val))
    }

    pub fn insert(&mut self, key: K, val: V) -> I {
        let id = self.log.push((key.clone(), val));
        self.index.insert(key, id);
        id
    }

    /// Look up the current dense index for a key.
    #[inline]
    pub fn id_of(&self, key: &K) -> Option<I> {
        self.index.get(key).copied()
    }

    /// Get the value at a dense log index.
    #[inline]
    pub fn get(&self, idx: I) -> &V {
        &self.log.get(idx).1
    }

    /// Get a mutable reference to the value at a dense log index.
    #[inline]
    pub fn get_mut(&mut self, idx: I) -> &mut V {
        &mut self.log.get_mut(idx).1
    }

    /// Get the key at a dense log index.
    #[inline]
    pub fn key(&self, idx: I) -> &K {
        &self.log.get(idx).0
    }

    /// Get the current value for a key.
    pub fn get_by_key(&self, key: &K) -> Option<&V> {
        self.id_of(key).map(|id| self.get(id))
    }

    /// Number of live keys.
    ///
    /// `usize`, not `I`: this is the hash index's own cardinality, not a log
    /// position. It is in fact bounded by the log — each live key holds one
    /// position — but that bound is an injection argument the verified twin cannot
    /// discharge cheaply, and the count is never stored, so narrowing it would buy
    /// nothing. [`log_len`](Self::log_len) is the one that counts positions.
    pub fn len(&self) -> usize {
        self.index.len()
    }

    /// Number of entries in the log (including overwritten shadows).
    pub fn log_len(&self) -> I {
        self.log.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.index.contains_key(key)
    }

    /// Total-API twin (parity with the verified crate's shell): production's
    /// core panics on misuse, so the twin always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_mark(&mut self, policy: super::ShrinkPolicy) -> Result<MapToken, &'static str> {
        Ok(self.mark(policy))
    }

    pub fn mark(&mut self, shrink: super::ShrinkPolicy) -> MapToken {
        MapToken(self.log.mark(shrink))
    }

    /// Restore to the given token. Truncates the log and rebuilds the
    /// HashMap from surviving entries.
    /// Total-API twin (parity with the verified crate's shell): production's
    /// core panics on misuse, so the twin always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_restore(&mut self, token: MapToken) -> Result<(), &'static str> {
        self.restore(token);
        Ok(())
    }

    pub fn restore(&mut self, token: MapToken) {
        self.log.restore(token.0);
        self.rebuild_index();
    }

    pub fn depth(&self) -> usize {
        self.log.depth()
    }

    pub fn is_valid_token(&self, token: &MapToken) -> bool {
        self.log.is_valid_token(&token.0)
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        for (i, (k, _)) in self.log.iter().enumerate() {
            // Infallible: `i` is below the surviving log length, which `push` kept
            // inside `I`. Checked anyway so a broken length invariant surfaces here
            // rather than as two keys aliased onto one wrapped position.
            let pos = I::try_from_usize(i).expect("log position overflow during index rebuild");
            self.index.insert(k.clone(), pos);
        }
    }

    /// Iterate over `(key, value)` pairs in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.log.iter()
    }
}

impl<K: Hash + Eq + Clone + std::fmt::Debug, V: std::fmt::Debug, I: IndexLike, const TRACK: bool>
    std::fmt::Debug for Map<K, V, I, TRACK>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Map")
            .field("len", &self.index.len())
            .field("log_len", &self.log.len())
            .finish()
    }
}

impl<K: Hash + Eq + Clone, V, I: IndexLike, const TRACK: bool> Default for Map<K, V, I, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 10);
        m.insert("b", 20);
        assert_eq!(m.len(), 2);
        assert_eq!(*m.get_by_key(&"a").unwrap(), 10);
        assert_eq!(*m.get_by_key(&"b").unwrap(), 20);
    }

    #[test]
    fn overwrite() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 1);
        m.insert("a", 2);
        assert_eq!(*m.get_by_key(&"a").unwrap(), 2);
        assert_eq!(m.len(), 1);
        assert_eq!(m.log_len(), 2);
    }

    #[test]
    fn mark_restore_inserts() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 10);
        let t = m.mark(crate::ShrinkPolicy::Never);
        m.insert("b", 20);
        m.insert("c", 30);
        assert_eq!(m.len(), 3);
        m.restore(t);
        assert_eq!(m.len(), 1);
        assert!(m.contains_key(&"a"));
        assert!(!m.contains_key(&"b"));
    }

    #[test]
    fn mark_restore_overwrite() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 1);
        let t = m.mark(crate::ShrinkPolicy::Never);
        m.insert("a", 2);
        assert_eq!(*m.get_by_key(&"a").unwrap(), 2);
        m.restore(t);
        assert_eq!(*m.get_by_key(&"a").unwrap(), 1);
    }

    #[test]
    fn nested_marks() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 1);
        let t1 = m.mark(crate::ShrinkPolicy::Never);
        m.insert("b", 2);
        let t2 = m.mark(crate::ShrinkPolicy::Never);
        m.insert("c", 3);
        m.insert("a", 99);
        assert_eq!(*m.get_by_key(&"a").unwrap(), 99);
        m.restore(t2);
        assert!(!m.contains_key(&"c"));
        assert_eq!(*m.get_by_key(&"a").unwrap(), 1);
        m.restore(t1);
        assert!(!m.contains_key(&"b"));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn restore_then_reinsert() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 1);
        let t = m.mark(crate::ShrinkPolicy::Never);
        m.insert("b", 2);
        m.restore(t);
        m.insert("b", 3);
        assert_eq!(*m.get_by_key(&"b").unwrap(), 3);
    }

    #[test]
    #[should_panic(expected = "abandoned future")]
    fn invalidated_token() {
        let mut m: Map<&str, i32> = Map::new();
        m.insert("a", 1);
        let t1 = m.mark(crate::ShrinkPolicy::Never);
        m.insert("b", 2);
        let t2 = m.mark(crate::ShrinkPolicy::Never);
        m.restore(t1);
        m.restore(t2);
    }
}
