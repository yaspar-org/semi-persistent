// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Session-level bare-pair memo for the exact solver.
//!
//! One entry per class pair `(l, r)`: the term and support of the first
//! context-clean solve, exactly the payload of the exact solver's in-call
//! `SubsumptionState::by_pair`. Promoted to a session container so
//! consecutive hybrid calls (`hybrid_exact`, `rollout_hybrid`) reuse each
//! other's clean solves instead of re-solving overlapping subgraphs; the
//! reuse rule is unchanged: a clean entry re-executes under any entry
//! context disjoint from its support, and the re-execution is the identical
//! derivation, so reuse is equality. Entries are valid for one snapshot and
//! one cycle mode, which is the session's own scope.
//!
//! Semi-persistence follows the interning-log pattern (design chapter 3's
//! derived-index section): the append-only log is the source of truth, the
//! hash index is derived, and `restore` validates the log token BEFORE
//! removing the truncated suffix's keys from the index, reading them from
//! the log while it is still live. Terms reference the session term pool;
//! the session restores the pool with its own token in the same bundle, so
//! a rolled-back entry never outlives the term it points to.

use std::collections::HashMap;

use crate::containers::error::ContainerError;
use crate::containers::{AppendOnlyVec, IndexLike, ShrinkPolicy, VecToken};

/// One memoized clean solve. Supports are sorted and deduplicated at
/// publication (the exact solver sorts before it writes).
struct MemoEntry<T, C> {
    key: (u64, u64),
    term: T,
    support_l: Vec<C>,
    support_r: Vec<C>,
}

/// Token for [`ExactMemo::mark`] / [`ExactMemo::restore`].
///
/// Carries the log length at the mark alongside the log's own token: restore
/// reads it to find the suffix of entries recorded since, which is exactly
/// the set of index keys it has to drop. Branch validity lives entirely in
/// the `VecToken`.
#[derive(Clone, Copy, Debug)]
pub struct ExactMemoToken(VecToken, usize);

/// The session memo. `T` is the term id type, `C` the class id type, `I` the
/// session index word.
pub struct ExactMemo<T: Copy, C: Copy + Ord, I: IndexLike = usize> {
    log: AppendOnlyVec<MemoEntry<T, C>, I>,
    /// Derived: class-pair key -> log position of its (unique) entry.
    index: HashMap<(u64, u64), usize>,
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> ExactMemo<T, C, I> {
    pub fn new() -> Self {
        ExactMemo {
            log: AppendOnlyVec::new(),
            index: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.log.len().as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The clean entry for `(l, r)`, if one was recorded: its term and its
    /// per-side support (sorted, deduplicated).
    pub fn get(&self, l: u64, r: u64) -> Option<(T, &[C], &[C])> {
        let &pos = self.index.get(&(l, r))?;
        let entry = self
            .log
            .get(I::try_from_usize(pos).expect("index within log length"));
        Some((entry.term, &entry.support_l, &entry.support_r))
    }

    /// Record the first clean solve of `(l, r)`; later writers lose, matching
    /// the in-call memo's `or_insert`.
    pub fn insert_if_absent(
        &mut self,
        l: u64,
        r: u64,
        term: T,
        support_l: Vec<C>,
        support_r: Vec<C>,
    ) -> Result<(), ContainerError> {
        if self.index.contains_key(&(l, r)) {
            return Ok(());
        }
        let pos = self.log.len().as_usize();
        self.log.try_push(MemoEntry {
            key: (l, r),
            term,
            support_l,
            support_r,
        })?;
        self.index.insert((l, r), pos);
        Ok(())
    }

    pub fn mark(&mut self) -> ExactMemoToken {
        let len = self.len();
        ExactMemoToken(
            self.log
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            len,
        )
    }

    pub fn is_valid_token(&self, token: &ExactMemoToken) -> bool {
        self.log.is_valid_token(&token.0) && token.1 <= self.len()
    }

    pub fn restore(&mut self, token: ExactMemoToken) {
        // Validate BEFORE touching the index: the removals below are not
        // undoable, so an invalid token must refuse while log and index are
        // still in step.
        assert!(
            self.log.is_valid_token(&token.0),
            "ExactMemo: token is invalid (foreign or abandoned)"
        );
        let saved_len = token.1;
        for pos in saved_len..self.len() {
            let entry = self
                .log
                .get(I::try_from_usize(pos).expect("position within log length"));
            self.index.remove(&entry.key);
        }
        self.log
            .try_restore(token.0)
            .expect("restore: token minted by this container's own mark");
        debug_assert_eq!(self.index.len(), self.len());
    }
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> Default for ExactMemo<T, C, I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Memo = ExactMemo<u32, u16>;

    #[test]
    fn first_writer_wins() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![3u16], vec![4u16])
            .unwrap();
        m.insert_if_absent(1, 2, 99, vec![], vec![]).unwrap();
        let (t, sl, sr) = m.get(1, 2).unwrap();
        assert_eq!((t, sl, sr), (10, &[3u16][..], &[4u16][..]));
        assert!(m.get(2, 1).is_none());
    }

    #[test]
    fn mark_restore_truncates_and_unindexes() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![], vec![]).unwrap();
        let token = m.mark();
        m.insert_if_absent(3, 4, 20, vec![], vec![]).unwrap();
        assert_eq!(m.len(), 2);

        m.restore(token);
        assert_eq!(m.len(), 1);
        assert!(m.get(1, 2).is_some());
        assert!(m.get(3, 4).is_none());

        // A re-insert after the rollback lands at the recycled position.
        m.insert_if_absent(3, 4, 21, vec![], vec![]).unwrap();
        assert_eq!(m.get(3, 4).unwrap().0, 21);
    }

    #[test]
    fn nested_marks() {
        let mut m = Memo::new();
        let outer = m.mark();
        m.insert_if_absent(1, 1, 1, vec![], vec![]).unwrap();
        let inner = m.mark();
        m.insert_if_absent(2, 2, 2, vec![], vec![]).unwrap();
        m.restore(inner);
        assert!(m.get(1, 1).is_some() && m.get(2, 2).is_none());
        m.restore(outer);
        assert!(m.get(1, 1).is_none());
        assert!(m.is_empty());
    }
}
