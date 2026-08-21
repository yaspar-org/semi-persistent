// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The seek-strategy sweep's premise, tested rather than asserted.
//!
//! `benches/seek_microbench.rs` prices three searches against each other:
//! galloping (what `SortedVecCursor::seek` runs), bisection over the remaining
//! run (what E7 replaced), and a *stride-hinted* gallop whose ladder starts at a
//! caller-supplied expected stride instead of at 1. A crossover table between
//! them is meaningful only if all three compute the same answer, and the hinted
//! one is the variant where that is not obvious: it starts its first probe an
//! arbitrary distance from the cursor.
//!
//! The three functions below are the bench's, copied. A benchmark target cannot
//! be imported by an integration test, and lifting them into the library would
//! put an unverified seek next to the verified one in the shipped crate, which
//! is exactly the thing chapter 7 says does not happen. So the duplication is
//! deliberate, and this file is what keeps it honest: every property is checked
//! against `SortedVecCursor` itself, so a copy that drifts from the bench is
//! still caught the moment it disagrees with production.

use proptest::prelude::*;
use semi_persistent_egraph::containers::SortedCursor;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::index::SortedVecCursor;

/// `SortedVecCursor::seek` transcribed: early check, doubling ladder, clamp,
/// bisection of the window the ladder bounded.
fn gallop(data: &[ENodeId], pos: &mut usize, target: ENodeId) {
    hinted(data, pos, target, 1)
}

/// A `partition_point` over the whole remaining run: the pre-E7 seek.
fn binary(data: &[ENodeId], pos: &mut usize, target: ENodeId) {
    let n = data.len();
    if *pos >= n || data[*pos] >= target {
        return;
    }
    *pos += data[*pos..].partition_point(|x| *x < target);
}

/// `gallop` with the ladder's first offset set to `hint` instead of 1.
///
/// Correct for every `hint >= 1`: the ladder's invariant is only that
/// `data[lo] < target`, which the early check establishes before the first
/// doubling and which each doubling preserves, and the bisected window is
/// `lo + 1 .. hi` for whatever `hi` the ladder stopped at. The hint moves where
/// the ladder starts, not what it maintains.
fn hinted(data: &[ENodeId], pos: &mut usize, target: ENodeId, hint: usize) {
    let n = data.len();
    if *pos >= n || data[*pos] >= target {
        return;
    }
    let mut lo = *pos;
    let mut step = hint.max(1);
    while step < n - lo && data[lo + step] < target {
        lo += step;
        step *= 2;
    }
    let hi = if step < n - lo { lo + step } else { n };
    *pos = lo + 1 + data[lo + 1..hi].partition_point(|x| *x < target);
}

fn sorted_unique() -> impl Strategy<Value = Vec<u32>> {
    proptest::collection::vec(0u32..200, 0..80).prop_map(|mut v| {
        v.sort_unstable();
        v.dedup();
        v
    })
}

/// Positions the reference cursor and returns where it landed.
fn reference(data: &[ENodeId], from: usize, target: ENodeId) -> usize {
    let mut c = SortedVecCursor::new(data);
    // Walk to `from` rather than seeking there: the seek is the thing under
    // test, so the starting position must be established without it.
    for _ in 0..from {
        <SortedVecCursor<'_, ENodeId> as SortedCursor>::step(&mut c);
    }
    <SortedVecCursor<'_, ENodeId> as SortedCursor>::seek(&mut c, target);
    c.pos()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1500))]

    /// All three searches land where the verified cursor lands, from every
    /// starting position, for every target, at every hint. The hint sweep is
    /// the point: it covers hints far below the true stride (a ladder that has
    /// to climb) and far above it (a ladder that overshoots on its first probe
    /// and hands a wide window to the bisection).
    #[test]
    fn strategies_agree_with_the_verified_cursor(
        vals in sorted_unique(),
        target in 0u32..210,
        hint in 1usize..64,
    ) {
        let data: Vec<ENodeId> = vals.iter().map(|&v| ENodeId::new(v)).collect();
        let t = ENodeId::new(target);
        for from in 0..=data.len() {
            let want = reference(&data, from, t);

            let mut p = from;
            gallop(&data, &mut p, t);
            prop_assert_eq!(p, want, "gallop from {}", from);

            let mut p = from;
            binary(&data, &mut p, t);
            prop_assert_eq!(p, want, "binary from {}", from);

            let mut p = from;
            hinted(&data, &mut p, t, hint);
            prop_assert_eq!(p, want, "hinted({}) from {}", hint, from);
        }
    }

    /// A hint at or past the end of the run is still correct: the ladder's
    /// `step < n - lo` guard sends it straight to the clamp, and the bisection
    /// searches the whole tail. This is the case an `n/m` estimator produces
    /// whenever `m` is 1.
    #[test]
    fn oversized_hints_are_correct(vals in sorted_unique(), target in 0u32..210) {
        let data: Vec<ENodeId> = vals.iter().map(|&v| ENodeId::new(v)).collect();
        let t = ENodeId::new(target);
        for from in 0..=data.len() {
            let want = reference(&data, from, t);
            for hint in [data.len().max(1), data.len() + 1, usize::MAX / 2] {
                let mut p = from;
                hinted(&data, &mut p, t, hint);
                prop_assert_eq!(p, want, "hinted({}) from {}", hint, from);
            }
        }
    }
}
