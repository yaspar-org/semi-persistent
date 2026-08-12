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
    assert!(a.is_valid_token(&token_a), "a's token should be valid on a");
    // but the SAME token must be rejected by b (different container id).
    assert!(
        !b.is_valid_token(&token_a),
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

// Overflow protocol (production parity): `push` itself carries no check —
// the trap fires at the NEXT `len()` read (`try_from_usize` fails), exactly
// like production's `expect("len overflow")`. `u8` indices: max_nat == 256,
// so a data length of 256 is the first unrepresentable one.
#[test]
fn push_overflow_traps_for_small_index() {
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v = V::new();
    // 255 pushes are fine: lengths 0..=254 each satisfy `len + 1 < 256`.
    for i in 0..255u32 {
        v.push(i);
    }
    // The 256th push (at len 255) violates the erased requires; like
    // production, the push itself completes (data length 256)...
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        v.push(999);
        // ...and the NEXT length read traps instead of silently wrapping
        // (production: `try_from_usize(256).expect("len overflow")`).
        let _ = v.len();
    }));
    assert!(
        result.is_err(),
        "an overflowed Vec must trap at the next len() read, not silently wrap"
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

// --------------------------------------------------------------------------
// Shrink helpers: the trusted data-preservation contract.
//
// `shrink_vec_capacity` (ParallelStore/InlineStore shrink_if) and
// `shrink_aov_capacity` (AppendOnlyVec's mark-time variant) are
// external_body with `ensures data@ == old(data)@` — the std-documented
// behavior of `Vec::shrink_to`. They are pub(crate), so the fuzz drives
// them through the public surface: `mark(ShrinkPolicy::IfOverallocated)`
// after workloads engineered to leave excess capacity (push-then-pop for
// Vec — pop leaves capacity behind; plain growth slack for AppendOnlyVec),
// then checks the element sequence is unchanged. This closes the last
// contract-carrying `ensures` with no runtime test (trust ledger §2b).
// --------------------------------------------------------------------------

#[test]
fn shrink_preserves_vec_contents() {
    use semi_persistent_containers_verus::inline_store::InlineStore;
    type VP = SpVec<u64, u32, ParallelStore<u64, u32>, true>;
    type VI = SpVec<u32, u32, InlineStore<u32, u32>, true>;

    let mut lcg: u64 = 0x0058_7111;
    let mut next = move || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        lcg >> 1
    };

    for round in 0..200 {
        // Random survivor size, big over-allocation via push-then-pop, and a
        // random (factor, headroom) policy — including factor=0/1 edge cases
        // where the shrink branch always fires.
        let keep = (next() % 200) as usize;
        let excess = 1 + (next() % 2000) as usize;
        let factor = (next() % 5) as usize;
        let headroom = 1 + (next() % 4) as usize;
        let policy = ShrinkPolicy::IfOverallocated { factor, headroom };

        // ParallelStore-backed
        let mut vp: VP = VP::new();
        for _ in 0..keep + excess {
            vp.push(next());
        }
        for _ in 0..excess {
            vp.pop();
        }
        let before: Vec<u64> = (0..keep as u32).map(|i| vp.get_index(i)).collect();
        let _tok = vp.mark(policy); // shrink_vec_capacity fires inside mark
        let after: Vec<u64> = (0..keep as u32).map(|i| vp.get_index(i)).collect();
        assert_eq!(
            before, after,
            "round {round}: ParallelStore shrink changed contents \
             (factor={factor}, headroom={headroom}, keep={keep})"
        );

        // InlineStore-backed (u32 payloads: Tagged repr)
        let keep_i = (next() % 100) as usize;
        let mut vi: VI = VI::new();
        for _ in 0..keep_i + excess {
            vi.push((next() as u32) & 0x7FFF_FFFF);
        }
        for _ in 0..excess {
            vi.pop();
        }
        let before: Vec<u32> = (0..keep_i as u32).map(|i| vi.get_index(i)).collect();
        let _tok = vi.mark(policy);
        let after: Vec<u32> = (0..keep_i as u32).map(|i| vi.get_index(i)).collect();
        assert_eq!(
            before, after,
            "round {round}: InlineStore shrink changed contents"
        );
    }
    println!("shrink_preserves_vec_contents: OK (200 rounds x 2 stores)");
}

#[test]
fn shrink_preserves_aov_contents() {
    use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;

    let mut lcg: u64 = 0x0A05_7A7E;
    let mut next = move || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        lcg >> 1
    };

    for round in 0..200 {
        let n = (next() % 500) as usize;
        let factor = (next() % 5) as usize;
        let headroom = (next() % 4) as usize;

        let mut v: AppendOnlyVec<u64, usize, true> = AppendOnlyVec::new();
        let mut expect = Vec::with_capacity(n);
        for _ in 0..n {
            let x = next();
            v.push(x);
            expect.push(x);
        }
        // shrink_aov_capacity fires inside mark (AOV variant condition
        // `cap > len*factor + headroom`, target `len + headroom`).
        let _tok = v.mark(ShrinkPolicy::IfOverallocated { factor, headroom });
        assert_eq!(v.len(), expect.len(), "round {round}: length changed");
        for (i, e) in expect.iter().enumerate() {
            assert_eq!(
                v.get(i),
                e,
                "round {round}: AOV shrink changed contents at {i}"
            );
        }
    }
    println!("shrink_preserves_aov_contents: OK (200 rounds)");
}
