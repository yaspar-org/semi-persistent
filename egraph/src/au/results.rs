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
//! Semi-persistence: the table is one `VecP` arena of `ResultEntry` values.
//! The vector's conditional capture records pre-mark values on first write
//! per frame, and its branch genealogy validates tokens (foreign or abandoned
//! tokens are rejected by the underlying container). Mark/restore delegate.

use super::AuIds31;
use crate::config::AuIds;
use crate::containers::{DenseId, IndexLike, ShrinkPolicy, VecP, VecToken};

/// Sentinel quality for "no result yet": worse than every real result.
const NO_RESULT: (u32, u32) = (u32::MAX, u32::MAX);

/// One table entry. `Default` is the "no result yet" state.
#[derive(Clone, Copy, Debug)]
struct ResultEntry<T> {
    term: Option<T>,
    quality: (u32, u32),
    exact: bool,
}

impl<T> Default for ResultEntry<T> {
    fn default() -> Self {
        ResultEntry {
            term: None,
            quality: NO_RESULT,
            exact: false,
        }
    }
}

/// Token for restoring a `BestResults` to a previous state. Wraps the inner
/// vector's token; container identity and branch genealogy are validated by
/// the underlying semi-persistent vector.
#[derive(Clone, Copy, Debug)]
pub struct BestResultsToken {
    entries: VecToken,
}

/// The best-result table for a search session. The entry vector's index type
/// matches the configured word width, so wide OR ids never narrow.
pub struct BestResults<A: AuIds = AuIds31> {
    entries: VecP<ResultEntry<A::Term>, A::Index>,
}

impl<A: AuIds> BestResults<A> {
    pub fn new() -> Self {
        BestResults {
            entries: VecP::new(),
        }
    }

    pub fn ensure_capacity(&mut self, or_id: A::Or) {
        let idx = or_id.to_usize();
        while self.entries.len().as_usize() <= idx {
            self.entries.push(ResultEntry::default());
        }
    }

    /// The typed index for an OR id (checked; same word width by construction).
    #[inline]
    fn index_of(or_id: A::Or) -> A::Index {
        A::Index::try_from_usize(or_id.to_usize()).expect("OR id exceeds configured index width")
    }

    pub fn offer(&mut self, or_id: A::Or, term: A::Term, quality: (u32, u32)) -> bool {
        self.ensure_capacity(or_id);
        let idx = Self::index_of(or_id);
        let entry = self.entries.get(idx);
        if quality < entry.quality {
            self.entries.set(
                idx,
                ResultEntry {
                    term: Some(term),
                    quality,
                    exact: entry.exact,
                },
            );
            true
        } else {
            false
        }
    }

    pub fn mark_exact(&mut self, or_id: A::Or) {
        self.ensure_capacity(or_id);
        let idx = Self::index_of(or_id);
        let mut entry = self.entries.get(idx);
        if !entry.exact {
            entry.exact = true;
            self.entries.set(idx, entry);
        }
    }

    #[inline]
    fn entry(&self, or_id: A::Or) -> ResultEntry<A::Term> {
        let idx = or_id.to_usize();
        if idx < self.entries.len().as_usize() {
            self.entries.get(Self::index_of(or_id))
        } else {
            ResultEntry::default()
        }
    }

    #[inline]
    pub fn best_term(&self, or_id: A::Or) -> Option<A::Term> {
        self.entry(or_id).term
    }

    #[inline]
    pub fn best_size(&self, or_id: A::Or) -> u32 {
        self.entry(or_id).quality.0
    }

    #[inline]
    pub fn best_quality(&self, or_id: A::Or) -> (u32, u32) {
        self.entry(or_id).quality
    }

    #[inline]
    pub fn is_exact(&self, or_id: A::Or) -> bool {
        self.entry(or_id).exact
    }

    pub fn mark(&mut self) -> BestResultsToken {
        BestResultsToken {
            entries: self.entries.mark(ShrinkPolicy::Never),
        }
    }

    /// Is this token restorable right now (same instance, live branch)?
    pub fn is_valid_token(&self, token: &BestResultsToken) -> bool {
        self.entries.is_valid_token(&token.entries)
    }

    pub fn restore(&mut self, token: BestResultsToken) {
        self.entries.restore(token.entries);
    }
}

impl<A: AuIds> Default for BestResults<A> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::space::OrId;
    use crate::au::terms::TermId;

    #[test]
    fn strict_improvement_only() {
        let mut results: BestResults = BestResults::new();
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
        let mut results: BestResults = BestResults::new();
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
        let mut results: BestResults = BestResults::new();
        let or0 = OrId::from_usize(0);

        assert!(!results.is_exact(or0));
        results.ensure_capacity(or0);
        assert!(!results.is_exact(or0));
        results.mark_exact(or0);
        assert!(results.is_exact(or0));
    }

    #[test]
    fn uninitialized_returns_none() {
        let results: BestResults = BestResults::new();
        let or5 = OrId::from_usize(5);

        assert_eq!(results.best_term(or5), None);
        assert_eq!(results.best_size(or5), u32::MAX);
        assert!(!results.is_exact(or5));
    }

    #[test]
    fn mark_restore_truncates_new_entries() {
        let mut results: BestResults = BestResults::new();
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
        let mut results: BestResults = BestResults::new();
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
