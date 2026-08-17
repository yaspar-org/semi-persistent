// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-seek advance-distance accounting for the leapfrog join.
//!
//! Which seek strategy a cursor should run is decided by one distribution: how
//! far a seek actually advances (*d*) against how much of the run is left in
//! front of it (*rem*). Galloping pays about `2·log₂ d` probes, a bisection over
//! the remaining run pays `log₂ rem`, and the two cross where `d² ≈ rem`. That
//! is a statement about the workload, not about the code, so it has to be
//! measured on the workload rather than argued from the algorithm.
//!
//! This module records the joint distribution of `(⌊log₂ d⌋, ⌊log₂ rem⌋)` over
//! every seek the push-based matcher issues, plus the exact counts of the two
//! cases the histogram's first bucket hides (`d = 0`, `d = 1`). From it both
//! probe models are evaluated after the fact, for any strategy expressible as a
//! function of `d` and `rem`, with no second instrumented run per candidate.
//!
//! Off by default and zero cost when off, on the model of
//! [`phase_timing`](crate::phase_timing): the `seek-stats` feature selects the
//! recording implementation, and without it [`Probed`] is a type alias for the
//! bare cursor, so the wrapper and its call sites compile away. With it,
//! `EGRAPH_SEEK=1` prints both tables at exit. Measured at −0.31% to +0.28% on
//! `math-microbenchmark` with the feature off
//! (`doc/perf-results/E18-seek-strategy.md`).
//!
//! Only the push-based engine is wired (`ematch.rs`'s `cursor_of`/`cursor_in`),
//! which is the one `saturate` drives and the one every measurement in chapter
//! 20 reports. `MatchIterator`'s pull-based joins open their cursors directly
//! and are not counted.

/// Largest exponent the histogram resolves; everything above lands in the top
/// bucket. 2^20 is past the longest bucket any program under `comparison/`
/// produces, so the top bucket is empty in practice and its being a catch-all
/// costs nothing.
pub const LOG_BUCKETS: usize = 21;

#[cfg(not(feature = "seek-stats"))]
mod imp {
    /// Zero-cost stand-in: the wrapper *is* the cursor, so `Probed::new` is
    /// `SortedVecCursor::new` and no `seek` call site gains an instruction.
    pub type Probed<'a, K> = semi_persistent_containers::SortedVecCursor<'a, K>;

    #[inline(always)]
    pub fn dump() {}
}

#[cfg(feature = "seek-stats")]
mod imp {
    use super::LOG_BUCKETS;
    use crate::containers::DenseId;
    use semi_persistent_containers::{SortedCursor, SortedVecCursor};
    use std::sync::atomic::{AtomicU64, Ordering};

    // `AtomicU64` rather than a thread-local `Cell`, for the reason
    // `phase_timing` gives: the engine is single-threaded, so a relaxed add is a
    // plain instruction and a `static` needs no lazy init on the hot path.
    static JOINT: [[AtomicU64; LOG_BUCKETS]; LOG_BUCKETS] =
        [const { [const { AtomicU64::new(0) }; LOG_BUCKETS] }; LOG_BUCKETS];
    // Second table: the same `⌊log₂ d⌋`, against `⌊log₂ d̂⌋` for the stride
    // estimator a hinted gallop would start its ladder from. `d̂` is the
    // cursor's own running mean advance, which is the online form of the
    // plan-time `n/m` ratio and strictly better informed than it: `n/m` is that
    // mean predicted from two lengths, this is the mean actually observed so far
    // on this cursor. If `d̂` does not predict `d` here, no `n/m` rule
    // predicts it either.
    static HINT: [[AtomicU64; LOG_BUCKETS]; LOG_BUCKETS] =
        [const { [const { AtomicU64::new(0) }; LOG_BUCKETS] }; LOG_BUCKETS];
    static SEEKS: AtomicU64 = AtomicU64::new(0);
    static D0: AtomicU64 = AtomicU64::new(0);
    static D1: AtomicU64 = AtomicU64::new(0);
    static EXHAUSTED: AtomicU64 = AtomicU64::new(0);

    /// `⌊log₂ v⌋`, with `v = 0` folded into bucket 0 and everything at or above
    /// `2^(LOG_BUCKETS-1)` into the top bucket.
    #[inline]
    fn bucket(v: usize) -> usize {
        (usize::BITS - v.leading_zeros()) as usize - usize::from(v != 0)
    }

    #[inline]
    fn record(d: usize, rem: usize, hint: usize, exhausted: bool) {
        SEEKS.fetch_add(1, Ordering::Relaxed);
        match d {
            0 => D0.fetch_add(1, Ordering::Relaxed),
            1 => D1.fetch_add(1, Ordering::Relaxed),
            _ => 0,
        };
        if exhausted {
            EXHAUSTED.fetch_add(1, Ordering::Relaxed);
        }
        let db = bucket(d).min(LOG_BUCKETS - 1);
        let rb = bucket(rem).min(LOG_BUCKETS - 1);
        JOINT[db][rb].fetch_add(1, Ordering::Relaxed);
        HINT[db][bucket(hint).min(LOG_BUCKETS - 1)].fetch_add(1, Ordering::Relaxed);
    }

    /// `SortedVecCursor` plus the run length, recording every `seek`'s advance
    /// distance and the remaining run it advanced through.
    ///
    /// The length is captured at construction because the verified cursor does
    /// not publish it: `pos()` is the only positional accessor on its API, and
    /// this module deliberately does not reach past it.
    pub struct Probed<'a, K: DenseId> {
        inner: SortedVecCursor<'a, K>,
        len: usize,
        seeks: usize,
        advanced: usize,
    }

    impl<'a, K: DenseId> Probed<'a, K> {
        #[inline]
        pub fn new(data: &'a [K]) -> Self {
            Probed {
                len: data.len(),
                inner: SortedVecCursor::new(data),
                seeks: 0,
                advanced: 0,
            }
        }
    }

    impl<'a, K: DenseId> SortedCursor for Probed<'a, K> {
        type Key = K;

        #[inline]
        fn key(&self) -> Option<K> {
            // Spelled through the trait: the verified cursor's *inherent* `key`
            // returns `K` and refuses on exhaustion, and it shadows the trait
            // method under method resolution.
            SortedCursor::key(&self.inner)
        }

        #[inline]
        fn step(&mut self) {
            SortedCursor::step(&mut self.inner)
        }

        #[inline]
        fn seek(&mut self, target: K) {
            let before = self.inner.pos();
            SortedCursor::seek(&mut self.inner, target);
            let after = self.inner.pos();
            let d = after - before;
            // The hint this seek would have started from: the mean advance over
            // the seeks already issued on this cursor, 1 before there are any.
            let hint = self.advanced.checked_div(self.seeks).unwrap_or(0).max(1);
            self.seeks += 1;
            self.advanced += d;
            record(d, self.len - before, hint, after >= self.len);
        }
    }

    /// Print both tables under `EGRAPH_SEEK=1`, one line per `⌊log₂ d⌋`.
    ///
    /// Tab-separated with a `SEEK_` prefix on every line, so a run's output can
    /// be `grep`ed out of the program's own printing and pasted into a sheet.
    pub fn dump() {
        if std::env::var("EGRAPH_SEEK").unwrap_or_default().is_empty() {
            return;
        }
        let seeks = SEEKS.load(Ordering::Relaxed);
        println!(
            "SEEK_TOTAL\tseeks\t{}\td0\t{}\td1\t{}\texhausted\t{}",
            seeks,
            D0.load(Ordering::Relaxed),
            D1.load(Ordering::Relaxed),
            EXHAUSTED.load(Ordering::Relaxed),
        );
        emit("SEEK_JOINT", &JOINT);
        emit("SEEK_HINT", &HINT);
    }

    /// One `tag` table, one line per `⌊log₂ d⌋` that any seek reached.
    fn emit(tag: &str, table: &[[AtomicU64; LOG_BUCKETS]; LOG_BUCKETS]) {
        let mut hdr = format!("{tag}\tlog2d");
        for r in 0..LOG_BUCKETS {
            hdr.push_str(&format!("\tc{r}"));
        }
        println!("{hdr}");
        for d in 0..LOG_BUCKETS {
            let row: Vec<u64> = (0..LOG_BUCKETS)
                .map(|r| table[d][r].load(Ordering::Relaxed))
                .collect();
            if row.iter().all(|&v| v == 0) {
                continue;
            }
            let mut line = format!("{tag}\t{d}");
            for v in row {
                line.push_str(&format!("\t{v}"));
            }
            println!("{line}");
        }
    }
}

pub use imp::{Probed, dump};
