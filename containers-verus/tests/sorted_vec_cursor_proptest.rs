// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Defense-in-depth for the verified `SortedVecCursor`.
//!
//! `seek`'s soundness is machine-checked — `cargo verus verify -- --verify-only-module
//! sorted_vec_cursor` proves it lands on `seek_target_idx`, never skips a key, is monotone, and
//! cannot index out of bounds or overflow the doubling ladder, for *every* sorted
//! slice and target. So what is this file for?
//!
//! Under plain `cargo test` the Verus `requires`/`ensures` are **erased**. The
//! exec bodies are ordinary Rust, and nothing in a cargo build re-checks them.
//! This harness re-derives the four properties in plain Rust against a linear-scan
//! oracle, so that:
//!
//! 1. A future proof refactor that changes an exec body without re-running Verus
//!    is caught by `cargo test` alone (the repo's standard posture — see
//!    `tests/external_body_contract_fuzz.rs`, same reasoning).
//! 2. The verified cursor and the production one
//!    (`egraph/src/index.rs::SortedVecCursor`) are checked against the *same*
//!    oracle and the same generators as production's own `mod seek_props`, which
//!    is what makes "the verified one is a model of the production one" a tested
//!    claim rather than an asserted one.
//!
//! Both id widths are covered because production's are: `DenseId31` mirrors
//! `ENodeId` (31-bit) and `DenseId63` mirrors `ENodeId64` (63-bit), and the
//! ladder arithmetic is over `usize` in both.

// The inherent step is crate-private now; step through the guarded trait.
use semi_persistent_containers_verus::sorted_cursor::SortedCursor;
use proptest::prelude::*;
use semi_persistent_containers_verus::dense_id::{DenseId31, DenseId63};
use semi_persistent_containers_verus::opt::DenseId;
use semi_persistent_containers_verus::sorted_vec_cursor::SortedVecCursor;

/// A sorted, duplicate-free key vector — the cursor's `requires` (a strictly
/// sorted model), which is the representation invariant of the `SortedVec` it
/// cursors over. Same generator as production's `sorted_unique()`.
fn sorted_unique() -> impl Strategy<Value = Vec<usize>> {
    proptest::collection::vec(0usize..200, 0..64).prop_map(|mut v| {
        v.sort_unstable();
        v.dedup();
        v
    })
}

/// Targets from beyond the data's range as well as inside it, so both the "no
/// such key" path and the `hi = n` clamp are hit.
fn targets() -> impl Strategy<Value = Vec<usize>> {
    proptest::collection::vec(0usize..220, 0..16)
}

/// The oracle: linear scan from the cursor. This is `seek_target_idx` computed
/// the obvious way, and the forward-only `max` is the `from` argument.
fn expected_pos(data: &[usize], from: usize, target: usize) -> usize {
    let mut p = from;
    while p < data.len() && data[p] < target {
        p += 1;
    }
    p
}

fn ids<G: DenseId>(vals: &[usize]) -> Vec<G> {
    vals.iter().map(|&v| G::from_usize(v)).collect()
}

/// Property 1 — `seek(t)` lands on the first key ≥ `t`, or exhausts.
fn check_lands_on_first_ge<G: DenseId>(vals: &[usize], ts: &[usize]) {
    let data = ids::<G>(vals);
    for &t in ts {
        let mut c = SortedVecCursor::new(&data);
        c.seek(G::from_usize(t));
        let want = expected_pos(vals, 0, t);
        assert_eq!(c.pos(), want, "seek({t}) on {vals:?}");
        if c.is_valid() {
            assert!(c.key().to_usize() >= t, "landed below target");
            if want > 0 {
                assert!(vals[want - 1] < t, "skipped a key >= target");
            }
        }
    }
}

/// Property 2 — a seek sequence is monotone, in bounds, and matches the oracle
/// from the *current* position (the forward-only contract).
fn check_sequence_is_monotone<G: DenseId>(vals: &[usize], ts: &[usize]) {
    let data = ids::<G>(vals);
    let mut c = SortedVecCursor::new(&data);
    let mut prev = 0usize;
    for &t in ts {
        c.seek(G::from_usize(t));
        let p = c.pos();
        assert!(p >= prev, "pos went backwards: {prev} -> {p}");
        assert!(p <= vals.len(), "pos {p} out of bounds");
        assert_eq!(p, expected_pos(vals, prev, t), "seek({t}) mid-sequence");
        prev = p;
    }
}

/// Property 3 — interleaved seeks and steps skip nothing: the drained tail is
/// exactly `vals[pos..]`, in order, with no repeats.
fn check_no_keys_are_skipped<G: DenseId>(vals: &[usize], ops: &[(bool, usize)]) {
    let data = ids::<G>(vals);
    let mut c = SortedVecCursor::new(&data);
    let mut model = 0usize;
    for &(is_seek, arg) in ops {
        if is_seek {
            c.seek(G::from_usize(arg));
            model = expected_pos(vals, model, arg);
        } else if c.is_valid() {
            c.step();
            model += 1;
        }
        assert_eq!(c.pos(), model, "cursor diverged from the model");
    }
    let mut seen = Vec::new();
    while c.is_valid() {
        seen.push(c.key().to_usize());
        c.step();
    }
    assert_eq!(seen, vals[model.min(vals.len())..], "tail mismatch");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn lands_on_first_ge_31(vals in sorted_unique(), ts in targets()) {
        check_lands_on_first_ge::<DenseId31>(&vals, &ts);
    }

    #[test]
    fn lands_on_first_ge_63(vals in sorted_unique(), ts in targets()) {
        check_lands_on_first_ge::<DenseId63>(&vals, &ts);
    }

    #[test]
    fn sequence_is_monotone_31(vals in sorted_unique(), ts in targets()) {
        check_sequence_is_monotone::<DenseId31>(&vals, &ts);
    }

    #[test]
    fn sequence_is_monotone_63(vals in sorted_unique(), ts in targets()) {
        check_sequence_is_monotone::<DenseId63>(&vals, &ts);
    }

    #[test]
    fn no_keys_are_skipped_31(vals in sorted_unique(),
        ops in proptest::collection::vec((any::<bool>(), 0usize..220), 0..24)) {
        check_no_keys_are_skipped::<DenseId31>(&vals, &ops);
    }

    #[test]
    fn no_keys_are_skipped_63(vals in sorted_unique(),
        ops in proptest::collection::vec((any::<bool>(), 0usize..220), 0..24)) {
        check_no_keys_are_skipped::<DenseId63>(&vals, &ops);
    }
}

/// The doubling ladder on a long run of misses — ~12 doublings on 4096 keys.
/// Verus proves `lo + step` and `step * 2` cannot overflow; this is the sampled
/// version of that, kept because the erased build has no such proof.
#[test]
fn long_gallop_does_not_overflow() {
    let vals: Vec<usize> = (0..4096).map(|i| i * 2).collect();
    let data = ids::<DenseId63>(&vals);

    let mut c = SortedVecCursor::new(&data);
    c.seek(DenseId63::from_usize(100_000));
    assert!(!c.is_valid(), "seek past the end must exhaust");

    let mut c = SortedVecCursor::new(&data);
    c.seek(DenseId63::from_usize(8190));
    assert!(c.is_valid());
    assert_eq!(c.key().to_usize(), 8190, "last key");
}

/// Degenerate shapes, one per early exit in `seek`.
#[test]
fn edge_shapes() {
    // Empty slice: the `pos >= n` early return, on a cursor that starts exhausted.
    let empty: Vec<DenseId31> = Vec::new();
    let mut c = SortedVecCursor::new(&empty);
    assert!(!c.is_valid());
    c.seek(DenseId31::from_usize(7));
    assert!(!c.is_valid());

    // Single element: below it, on it, above it.
    let one = ids::<DenseId31>(&[5]);
    for (t, want_valid, want_key) in [(0usize, true, 5usize), (5, true, 5), (6, false, 0)] {
        let mut c = SortedVecCursor::new(&one);
        c.seek(DenseId31::from_usize(t));
        assert_eq!(c.is_valid(), want_valid, "seek({t})");
        if want_valid {
            assert_eq!(c.key().to_usize(), want_key);
        }
    }

    // Already exhausted: seek is a no-op, including backwards.
    let mut c = SortedVecCursor::new(&one);
    c.step();
    assert!(!c.is_valid());
    c.seek(DenseId31::from_usize(0));
    assert!(
        !c.is_valid(),
        "forward-only: an exhausted cursor does not rewind"
    );
}

/// Forward-only, stated directly: seeking *backwards* must not move the cursor.
/// This is the one place the verified contract deliberately differs from
/// `BPlusCursor`'s absolute seek, so it gets its own test rather than relying on
/// the sequence property to stumble into it.
#[test]
fn backward_seek_does_not_rewind() {
    let vals = [10usize, 20, 30, 40];
    let data = ids::<DenseId31>(&vals);
    let mut c = SortedVecCursor::new(&data);
    c.seek(DenseId31::from_usize(30));
    assert_eq!(c.key().to_usize(), 30);
    c.seek(DenseId31::from_usize(10));
    assert_eq!(c.key().to_usize(), 30, "backward seek moved the cursor");
}

/// The largest id each width admits, seeked to and past. `DenseId31` tops out at
/// `2^31 - 1` and `DenseId63` at `2^63 - 1`; both are the values a bit-stealing
/// id family is most likely to mishandle.
#[test]
fn saturated_ids() {
    fn run<G: DenseId>(max: usize) {
        let vals = [0usize, 1, max - 1, max];
        let data = ids::<G>(&vals);

        let mut c = SortedVecCursor::new(&data);
        c.seek(G::from_usize(max));
        assert!(c.is_valid());
        assert_eq!(c.key().to_usize(), max, "seek to the saturated id");

        let mut c = SortedVecCursor::new(&data);
        c.seek(G::from_usize(max - 1));
        assert_eq!(c.key().to_usize(), max - 1);
    }
    run::<DenseId31>((1usize << 31) - 1);
    run::<DenseId63>((1usize << 63) - 1);
}
