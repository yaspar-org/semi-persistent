// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime contract checks for the functions that remain `#[verifier::external_body]`
//! because they are genuinely external (a process-global atomic, or spec-free byte
//! accounting) rather than unproven. Verus can't (or needn't) prove these, so we
//! fuzz/smoke-test their contracts here instead.
//!
//! (The other former external_body functions — the IndexLike/DenseId integer casts —
//! are now VERIFIED, not fuzzed; their contracts are machine-checked. This file
//! covers only the irreducibly-external remainder.)

use semi_persistent_containers_verus::container_id::ContainerId;
use semi_persistent_containers_verus::parallel_store::ParallelStore;
use semi_persistent_containers_verus::vec::{ShrinkPolicy, Vec as SpVec};

// --------------------------------------------------------------------------
// ContainerId: new() mints fresh ids; eq() reflects identity equality.
//
// Contract (the soundness-relevant guarantee): distinct `new()` calls yield
// distinct ids (so a token minted by one container is rejected by another), and
// `eq` is a true equality (reflexive, symmetric, and matches "same id").
// --------------------------------------------------------------------------

#[test]
fn container_id_new_is_distinct() {
    // Mint many ids; every pair must be `!eq`. We can't read the raw u32 (private,
    // external_body), so distinctness is observed through `eq` itself.
    let ids: Vec<ContainerId> = (0..2000).map(|_| ContainerId::new()).collect();
    for (i, a) in ids.iter().enumerate() {
        // reflexive: an id equals itself.
        assert!(a.eq(*a), "ContainerId::eq not reflexive at {i}");
        // distinct from every other mint.
        for (j, b) in ids.iter().enumerate() {
            if i != j {
                assert!(
                    !a.eq(*b),
                    "ContainerId::new() returned equal ids at {i} and {j}"
                );
                // symmetric.
                assert_eq!(
                    a.eq(*b),
                    b.eq(*a),
                    "ContainerId::eq not symmetric at {i},{j}"
                );
            }
        }
    }
    println!("container_id_new_is_distinct: OK (2000 distinct ids)");
}

#[test]
fn container_id_eq_via_copy() {
    // ContainerId is Copy; a copy must compare equal to its source (same id).
    let a = ContainerId::new();
    let b = a; // Copy
    assert!(
        a.eq(b) && b.eq(a),
        "a copied ContainerId must eq its source"
    );
    let c = ContainerId::new();
    assert!(
        !a.eq(c),
        "a freshly minted id must differ from an earlier one"
    );
    println!("container_id_eq_via_copy: OK");
}

// Cross-container token rejection, end to end: a token minted by one Vec must be
// rejected by a different Vec (the whole point of the container id). Exercises
// the eq contract through the real `is_valid_token` path.
#[test]
fn cross_container_token_rejected() {
    type V = SpVec<u32, u32, ParallelStore<u32, u32>, true>;
    let mut a = V::new();
    let mut b = V::new();
    for i in 0..10u32 {
        a.push(i);
        b.push(i + 100);
    }
    let token_a = a.mark(ShrinkPolicy::Never);
    // a's own token is valid on a.
    assert!(a.is_valid_token(token_a), "a's token should be valid on a");
    // but the SAME token must be rejected by b (different container id).
    assert!(
        !b.is_valid_token(token_a),
        "a token from container a must be rejected by container b"
    );
    println!("cross_container_token_rejected: OK");
}

// Sanity that the ids really do span a wide space (not all colliding into a few):
// partition a batch into eq-classes by pairwise `eq` and require as many classes
// as ids (i.e. no two collide).
#[test]
fn container_id_no_collisions_in_batch() {
    let ids: Vec<ContainerId> = (0..500).map(|_| ContainerId::new()).collect();
    // count distinct eq-classes by greedy partitioning.
    let mut reps: Vec<ContainerId> = Vec::new();
    for &id in &ids {
        if !reps.iter().any(|r| r.eq(id)) {
            reps.push(id);
        }
    }
    assert_eq!(reps.len(), ids.len(), "all 500 minted ids must be distinct");
    println!("container_id_no_collisions_in_batch: OK");
}

// --------------------------------------------------------------------------
// Byte counters (tracking_bytes / total_bytes): spec-free diagnostics. The only
// meaningful runtime contract is "does not panic, total >= tracking, and both
// grow (weakly) as the container grows".
// --------------------------------------------------------------------------

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 17
    }
}

#[test]
fn byte_counters_are_consistent() {
    type V = SpVec<u64, u32, ParallelStore<u64, u32>, true>;
    for seed in 0..6u64 {
        let mut v = V::new();
        let mut rng = Lcg::new(seed ^ 0xB17E5);
        let mut prev_total = v.total_bytes();
        let mut prev_tracking = v.tracking_bytes();

        for step in 0..400 {
            // total always accounts for at least the tracking portion.
            let tracking = v.tracking_bytes();
            let total = v.total_bytes();
            assert!(
                total >= tracking,
                "seed={seed} step={step}: total_bytes {total} < tracking_bytes {tracking}"
            );
            // mark/push only ever ADD diff entries / frames / store slots, so the
            // counters are monotone non-decreasing under these operations.
            assert!(
                total >= prev_total,
                "seed={seed} step={step}: total_bytes shrank"
            );
            assert!(
                tracking >= prev_tracking,
                "seed={seed} step={step}: tracking_bytes shrank"
            );
            prev_total = total;
            prev_tracking = tracking;

            if rng.next().is_multiple_of(5) {
                let _ = v.mark(ShrinkPolicy::Never);
            } else {
                v.push(rng.next());
            }
        }
        println!(
            "byte_counters seed={seed}: OK (final total={})",
            v.total_bytes()
        );
    }
}

// --------------------------------------------------------------------------
// Runtime precondition guards (src/guard.rs).
//
// The public methods carry `requires` that a Verus-checked caller proves. An
// UNVERIFIED caller has no such obligation, and a violated overflow/capacity
// precondition would otherwise silently wrap (`as u32`/`as I` truncation) and
// corrupt the container. `check_precondition` turns that into a clean panic.
// These tests exercise the guards at a REACHABLE boundary (a `u8` index type,
// `max_nat == 256`) and the headroom query a caller uses to avoid them.
// --------------------------------------------------------------------------

// `push` traps when the length would overflow the index type, instead of
// wrapping. `u8` indices saturate at 255 live elements (max_nat == 256, and the
// precondition is `len + 1 < max_nat`, so the 255th push — taking len 254->255 —
// is the last legal one; pushing at len 255 must panic).
#[test]
fn push_overflow_traps_for_small_index() {
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v = V::new();
    // 255 pushes are fine: lengths 0..=254 each satisfy `len + 1 < 256`.
    for i in 0..255u32 {
        v.push(i);
    }
    // The 256th push (at len 255) would make len 256 == max_nat: must panic, not
    // wrap to a 0-length / corrupt index.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        v.push(999);
    }));
    assert!(
        result.is_err(),
        "Vec::push must trap at the index-type limit, not silently wrap"
    );
}

// `restores_remaining()` reports the fork-history headroom and drops by exactly
// one per `restore` (each restore appends one never-reclaimed fork origin).
#[test]
fn restores_remaining_tracks_fork_history() {
    type V = SpVec<u32, u32, ParallelStore<u32, u32>, true>;
    let mut v = V::new();
    v.push(1);
    v.push(2);

    // Fresh container: no restores taken yet, so full u32 headroom.
    let start = v.restores_remaining();
    assert_eq!(start, u32::MAX as usize);

    // Each restore consumes exactly one unit of headroom.
    for k in 1..=5usize {
        let t = v.mark(ShrinkPolicy::Never);
        v.push(100 + k as u32);
        v.restore(t);
        assert_eq!(
            v.restores_remaining(),
            start - k,
            "restores_remaining must drop by one per restore (after {k})"
        );
    }
}
