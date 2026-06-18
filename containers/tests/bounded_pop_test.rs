// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Regression tests for the bounded-pop fix.
//!
//! Before the fix, `Vec::pop` recorded a diff entry on *every* pop of a slot
//! below the active frame's `saved_len` (via the unconditional `force_capture`).
//! An adversary could then grow the diff log without bound:
//!
//! ```text
//! loop { vec.pop(); vec.push(x); }   // on an index < saved_len
//! ```
//!
//! a memory-exhaustion DoS. The fix uses first-write-wins `capture`, so the log
//! holds at most one entry per index per frame (`<= saved_len` total), and
//! `restore` regrows the popped region with `resize_default` before an
//! overwrite-only replay.

use semi_persistent_containers::{ShrinkPolicy, VecI};

/// The headline DoS regression: after a `mark`, hammering pop+push on a slot
/// inside the marked region must NOT grow the diff log with iteration count.
///
/// This test FAILS on `main` (diff_log grows ~linearly with N) and PASSES on
/// the bounded-pop branch (diff_log stays <= saved_len).
#[test]
fn pop_push_loop_keeps_diff_log_bounded() {
    let mut v: VecI<u32, u32, true> = VecI::new();
    const SAVED_LEN: usize = 8;
    for i in 0..SAVED_LEN as u32 {
        v.push(i);
    }

    let _token = v.mark(ShrinkPolicy::Never);
    assert_eq!(v.diff_log_len(), 0, "fresh frame starts with an empty log");

    // The exploit loop: pop the top slot (which sits below saved_len) and push
    // it back, over and over. Each pop captures the same index; first-write-wins
    // means only the first capture logs an entry.
    const ITERS: usize = 100_000;
    for _ in 0..ITERS {
        let popped = v.pop().expect("non-empty");
        v.push(popped);
    }

    // Bounded: at most one entry per index in [0, saved_len). The loop only ever
    // touches the single slot at index saved_len-1, so in practice the log holds
    // exactly one entry — and crucially does NOT scale with ITERS.
    assert!(
        v.diff_log_len() <= SAVED_LEN,
        "diff log must stay bounded by saved_len ({SAVED_LEN}), got {} after {ITERS} iterations",
        v.diff_log_len()
    );
    assert!(
        v.diff_log_len() < ITERS,
        "diff log must not grow with iteration count (regression guard)"
    );
}

/// Popping every slot in the marked region then restoring must round-trip
/// through the new `resize_default` regrow path.
#[test]
fn restore_roundtrips_after_popping_marked_region() {
    let mut v: VecI<u32, u32, true> = VecI::new();
    let snapshot: Vec<u32> = (10..20).collect();
    for &x in &snapshot {
        v.push(x);
    }

    let token = v.mark(ShrinkPolicy::Never);

    // Pop the entire marked region (and then some growth past it), exercising
    // the conditional-capture-on-pop path for every cell below saved_len.
    while !v.is_empty() {
        v.pop();
    }
    // Re-grow above the old length with fresh values to make sure restore
    // truncates the surplus too.
    for x in 100..130u32 {
        v.push(x);
    }

    v.restore(token);

    // The popped region must be regrown by resize_default and then fully
    // overwritten by the captured diffs: view() equals the pre-mark snapshot.
    let view = v.view();
    assert_eq!(view.len() as usize, snapshot.len(), "length restored");
    for (i, &expected) in snapshot.iter().enumerate() {
        assert_eq!(
            view.get(i as u32),
            expected,
            "slot {i} restored to snapshot"
        );
    }
}

/// A `set` after a pop+push re-entry into the marked region must not log a
/// second entry for that slot — the `mark_captured` re-entry branch in `push`
/// preserves first-write-wins.
#[test]
fn set_after_reentry_does_not_double_capture() {
    let mut v: VecI<u32, u32, true> = VecI::new();
    for i in 0..4u32 {
        v.push(i);
    }
    let token = v.mark(ShrinkPolicy::Never);

    // Pop slot 3 (captures it once), then push a new value back into slot 3.
    let _ = v.pop();
    v.push(999);
    let after_reentry = v.diff_log_len();

    // A later `set` on the re-entered slot must NOT add another entry: push's
    // mark_captured kept the capture bit set.
    v.set(3u32, 12345);
    assert_eq!(
        v.diff_log_len(),
        after_reentry,
        "set after re-entry must not double-capture slot 3"
    );

    // And restore still round-trips to the pre-mark state.
    v.restore(token);
    let view = v.view();
    assert_eq!(view.len(), 4);
    for i in 0..4u32 {
        assert_eq!(view.get(i), i, "slot {i} restored");
    }
}
