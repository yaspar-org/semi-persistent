// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Measures the fork-history reclamation (doc 10, goal step 5): the depth-indexed
//! generation stamps hold O(max spine depth) live bytes, NOT O(R) lifetime restores.
//! The deleted branch model (`ForkHistory.origins`) grew one 8-byte entry per
//! restore and never reclaimed, so its size was 8*R; this confirms the replacement's
//! live size after the same R restores is 8*D_max, independent of R. The BEFORE
//! (8*R) is the deleted model's known formula; only the AFTER can be run.

use semi_persistent_containers_verus as verus;
use verus::GenStamps;

// Drive `restores` restore/re-mark cycles at a bounded spine depth and confirm the
// live size tracks depth, not the restore count.
fn live_bytes_after(depth: usize, restores: usize) -> usize {
    let mut g = GenStamps::new(0);
    // Deepen the spine to `depth` once (first time each depth is reached).
    for d in 0..depth {
        g.stamp_at(d);
    }
    let after_deepen = g.heap_bytes();
    // `restores` cycles: restore to the middle of the spine (cut the abandoned
    // future), then re-mark back down to `depth`. In the old model each restore
    // appended an origin (O(R) growth); here bump_from/stamp_at touch existing
    // levels only, so the array never grows past `depth`.
    let mid = depth / 2;
    for _ in 0..restores {
        g.bump_from(mid + 1);
        for d in mid..depth {
            g.stamp_at(d);
        }
    }
    let after_restores = g.heap_bytes();
    // The whole point: restores did not grow the structure.
    assert_eq!(
        after_restores, after_deepen,
        "restores must not grow the stamp array (O(depth), not O(R))"
    );
    after_restores
}

#[test]
fn live_size_is_bounded_by_depth_not_restores() {
    let depth = 1000;
    // Same depth, 100x different restore counts: live size must be identical.
    let few = live_bytes_after(depth, 500);
    let many = live_bytes_after(depth, 50_000);
    assert_eq!(
        few, many,
        "live size must be independent of the restore count"
    );

    // And it is depth-scale: one u64 per depth, capacity within 2x of `depth`.
    assert!(
        many <= 8 * depth * 2,
        "live size {many} bytes should be O(depth) (~8*{depth}), not O(restores)"
    );

    // Concrete contrast with the deleted branch model at an SMT-scale restore count.
    // BEFORE (origins, 8 bytes/restore, never reclaimed): 8 * 10^7 = 80 MB.
    // AFTER (this): the measured `many`, kilobytes.
    let before_bytes = 8usize * 10_000_000;
    assert!(
        before_bytes / many >= 1000,
        "reclamation should be >=1000x (MB -> KB)"
    );
    eprintln!(
        "fork history at depth {depth}, 10^7 restores: before ~{} MB, after {} KB ({}x)",
        before_bytes / 1_000_000,
        many / 1000 + 1,
        before_bytes / many.max(1),
    );
}
