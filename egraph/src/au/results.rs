// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Best-result table (§4.5): shared by all algorithms in a session.
//!
//! Maps each OR node to the best anti-unifier found so far (a `TermId`), plus
//! a write-once "exact" flag when the exact solver finishes that node.
//!
//! Ranking is the lexicographic quality key `(size, variant_mass)`: minimum
//! size first; at equal size, minimum variant mass (= maximum backbone) wins.
//! Updates are strict improvements only under that order.
//!
//! Semi-persistence: mark saves the current length and starts an undo log for
//! overwrites to pre-existing entries. Restore replays the undo log backward
//! (restoring old values), then truncates entries added after the mark.

use super::space::OrId;
use super::terms::TermId;
use crate::containers::DenseId;

/// Sentinel quality for "no result yet": worse than every real result.
const NO_RESULT: (u32, u32) = (u32::MAX, u32::MAX);

/// One undo-log entry: the old state of a pre-mark entry before it was overwritten.
#[derive(Clone, Debug)]
struct UndoEntry {
    idx: usize,
    old_term: Option<TermId>,
    old_quality: (u32, u32),
    old_exact: bool,
}

/// Token for restoring a `BestResults` to a previous state.
#[derive(Clone, Copy, Debug)]
pub struct BestResultsToken {
    len: usize,
    undo_len: usize,
}

/// The best-result table for a search session.
#[derive(Debug)]
pub struct BestResults {
    term: Vec<Option<TermId>>,
    quality: Vec<(u32, u32)>,
    exact: Vec<bool>,
    undo_log: Vec<UndoEntry>,
    /// The length at the last mark (entries below this get undo-logged on overwrite).
    mark_len: usize,
}

impl BestResults {
    pub fn new() -> Self {
        BestResults {
            term: Vec::new(),
            quality: Vec::new(),
            exact: Vec::new(),
            undo_log: Vec::new(),
            mark_len: 0,
        }
    }

    pub fn ensure_capacity(&mut self, or_id: OrId) {
        let idx = or_id.to_usize();
        if idx >= self.term.len() {
            self.term.resize(idx + 1, None);
            self.quality.resize(idx + 1, NO_RESULT);
            self.exact.resize(idx + 1, false);
        }
    }

    pub fn offer(&mut self, or_id: OrId, term: TermId, quality: (u32, u32)) -> bool {
        let idx = or_id.to_usize();
        self.ensure_capacity(or_id);
        if quality < self.quality[idx] {
            // Log the old value if this entry existed before the current mark.
            if idx < self.mark_len {
                self.undo_log.push(UndoEntry {
                    idx,
                    old_term: self.term[idx],
                    old_quality: self.quality[idx],
                    old_exact: self.exact[idx],
                });
            }
            self.term[idx] = Some(term);
            self.quality[idx] = quality;
            true
        } else {
            false
        }
    }

    pub fn mark_exact(&mut self, or_id: OrId) {
        let idx = or_id.to_usize();
        self.ensure_capacity(or_id);
        if idx < self.mark_len && !self.exact[idx] {
            self.undo_log.push(UndoEntry {
                idx,
                old_term: self.term[idx],
                old_quality: self.quality[idx],
                old_exact: self.exact[idx],
            });
        }
        self.exact[idx] = true;
    }

    #[inline]
    pub fn best_term(&self, or_id: OrId) -> Option<TermId> {
        let idx = or_id.to_usize();
        if idx < self.term.len() {
            self.term[idx]
        } else {
            None
        }
    }

    #[inline]
    pub fn best_size(&self, or_id: OrId) -> u32 {
        let idx = or_id.to_usize();
        if idx < self.quality.len() {
            self.quality[idx].0
        } else {
            u32::MAX
        }
    }

    #[inline]
    pub fn best_quality(&self, or_id: OrId) -> (u32, u32) {
        let idx = or_id.to_usize();
        if idx < self.quality.len() {
            self.quality[idx]
        } else {
            NO_RESULT
        }
    }

    #[inline]
    pub fn is_exact(&self, or_id: OrId) -> bool {
        let idx = or_id.to_usize();
        if idx < self.exact.len() {
            self.exact[idx]
        } else {
            false
        }
    }

    pub fn mark(&mut self) -> BestResultsToken {
        self.mark_len = self.term.len();
        BestResultsToken {
            len: self.term.len(),
            undo_len: self.undo_log.len(),
        }
    }

    pub fn restore(&mut self, token: BestResultsToken) {
        // Replay undo log backward to restore overwritten pre-mark entries.
        while self.undo_log.len() > token.undo_len {
            let entry = self.undo_log.pop().unwrap();
            self.term[entry.idx] = entry.old_term;
            self.quality[entry.idx] = entry.old_quality;
            self.exact[entry.idx] = entry.old_exact;
        }
        // Truncate entries added after the mark.
        self.term.truncate(token.len);
        self.quality.truncate(token.len);
        self.exact.truncate(token.len);
        self.mark_len = token.len;
    }
}

impl Default for BestResults {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_improvement_only() {
        let mut results = BestResults::new();
        let or0 = OrId::from_usize(0);
        let t0 = TermId::from_usize(0);
        let t1 = TermId::from_usize(1);

        assert!(results.offer(or0, t0, (10, 10)));
        assert_eq!(results.best_size(or0), 10);
        assert_eq!(results.best_term(or0), Some(t0));

        assert!(!results.offer(or0, t1, (15, 15)));
        assert_eq!(results.best_term(or0), Some(t0));

        assert!(!results.offer(or0, t1, (10, 10)));
        assert_eq!(results.best_term(or0), Some(t0));

        assert!(results.offer(or0, t1, (5, 5)));
        assert_eq!(results.best_size(or0), 5);
        assert_eq!(results.best_term(or0), Some(t1));
    }

    #[test]
    fn equal_size_lower_vmass_wins() {
        let mut results = BestResults::new();
        let or0 = OrId::from_usize(0);
        let t0 = TermId::from_usize(0);
        let t1 = TermId::from_usize(1);

        assert!(results.offer(or0, t0, (3, 3)));
        assert!(results.offer(or0, t1, (3, 2)));
        assert_eq!(results.best_term(or0), Some(t1));
        assert_eq!(results.best_quality(or0), (3, 2));

        assert!(!results.offer(or0, t0, (3, 2)));
        assert!(results.offer(or0, t0, (2, 2)));
        assert_eq!(results.best_term(or0), Some(t0));
    }

    #[test]
    fn exact_flag_write_once() {
        let mut results = BestResults::new();
        let or0 = OrId::from_usize(0);

        assert!(!results.is_exact(or0));
        results.ensure_capacity(or0);
        assert!(!results.is_exact(or0));
        results.mark_exact(or0);
        assert!(results.is_exact(or0));
    }

    #[test]
    fn uninitialized_returns_none() {
        let results = BestResults::new();
        let or5 = OrId::from_usize(5);

        assert_eq!(results.best_term(or5), None);
        assert_eq!(results.best_size(or5), u32::MAX);
        assert!(!results.is_exact(or5));
    }

    #[test]
    fn mark_restore_truncates_new_entries() {
        let mut results = BestResults::new();
        let or0 = OrId::from_usize(0);
        let or1 = OrId::from_usize(1);
        let t0 = TermId::from_usize(0);

        results.offer(or0, t0, (5, 5));
        let token = results.mark();

        results.offer(or1, t0, (3, 3));
        assert_eq!(results.best_term(or1), Some(t0));

        results.restore(token);
        assert_eq!(results.best_term(or1), None);
        assert_eq!(results.best_term(or0), Some(t0));
    }

    #[test]
    fn mark_restore_undoes_overwrites() {
        let mut results = BestResults::new();
        let or0 = OrId::from_usize(0);
        let t0 = TermId::from_usize(0);
        let t1 = TermId::from_usize(1);

        results.offer(or0, t0, (10, 10));
        let token = results.mark();

        // Improve the pre-mark entry.
        results.offer(or0, t1, (5, 5));
        assert_eq!(results.best_term(or0), Some(t1));
        assert_eq!(results.best_quality(or0), (5, 5));

        // Restore: the overwrite is undone.
        results.restore(token);
        assert_eq!(results.best_term(or0), Some(t0));
        assert_eq!(results.best_quality(or0), (10, 10));
    }
}
