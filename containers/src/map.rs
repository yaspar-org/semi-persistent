// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent map backed by [`AppendOnlyVec`] + transient HashMap.
//!
//! The append-only log is the source of truth. A transient `HashMap`
//! accelerates key lookup. On `restore`, the log is truncated and the
//! `HashMap` is rebuilt from surviving entries.

use super::append_only_vec::AppendOnlyVec;
use super::token::VecToken;
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
pub struct Map<K: Hash + Eq + Clone, V, const TRACK: bool = true> {
    log: AppendOnlyVec<(K, V), TRACK>,
    index: hashbrown::HashMap<K, usize>,
}

impl<K: Hash + Eq + Clone, V, const TRACK: bool> Map<K, V, TRACK> {
    pub fn new() -> Self {
        Self {
            log: AppendOnlyVec::new(),
            index: hashbrown::HashMap::new(),
        }
    }

    /// Insert or overwrite. Returns the dense log index of the new entry.
    pub fn insert(&mut self, key: K, val: V) -> usize {
        let id = self.log.push((key.clone(), val));
        self.index.insert(key, id);
        id
    }

    /// Look up the current dense index for a key.
    #[inline]
    pub fn id_of(&self, key: &K) -> Option<usize> {
        self.index.get(key).copied()
    }

    /// Get the value at a dense log index.
    #[inline]
    pub fn get(&self, idx: usize) -> &V {
        &self.log.get(idx).1
    }

    /// Get a mutable reference to the value at a dense log index.
    #[inline]
    pub fn get_mut(&mut self, idx: usize) -> &mut V {
        &mut self.log.get_mut(idx).1
    }

    /// Get the key at a dense log index.
    #[inline]
    pub fn key(&self, idx: usize) -> &K {
        &self.log.get(idx).0
    }

    /// Get the current value for a key.
    pub fn get_by_key(&self, key: &K) -> Option<&V> {
        self.id_of(key).map(|id| self.get(id))
    }

    /// Number of live keys.
    pub fn len(&self) -> usize {
        self.index.len()
    }

    /// Number of entries in the log (including overwritten shadows).
    pub fn log_len(&self) -> usize {
        self.log.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.index.contains_key(key)
    }

    pub fn mark(&mut self, shrink: super::ShrinkPolicy) -> MapToken {
        MapToken(self.log.mark(shrink))
    }

    /// Restore to the given token. Truncates the log and rebuilds the
    /// HashMap from surviving entries.
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
            self.index.insert(k.clone(), i);
        }
    }

    /// Iterate over `(key, value)` pairs in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.log.iter()
    }
}

impl<K: Hash + Eq + Clone + std::fmt::Debug, V: std::fmt::Debug, const TRACK: bool> std::fmt::Debug
    for Map<K, V, TRACK>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Map")
            .field("len", &self.index.len())
            .field("log_len", &self.log.len())
            .finish()
    }
}

impl<K: Hash + Eq + Clone, V, const TRACK: bool> Default for Map<K, V, TRACK> {
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
