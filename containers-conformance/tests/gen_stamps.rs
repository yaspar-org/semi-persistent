// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exercises the fork-history reclamation core (GenStamps): a diverging restore
//! bumps the deep levels, O(1)-invalidating tokens from the abandoned future
//! while the surviving spine's tokens stay valid. The invalidation is proved
//! (lemma_bump_invalidates); this runs the executable path Verus erases.

use semi_persistent_containers_verus as verus;
use verus::GenStamps;

#[test]
fn bump_invalidates_deep_tokens_keeps_spine() {
    let mut g = GenStamps::new(8);

    // Mint tokens at several depths on the current branch.
    let t2 = g.stamp(2);
    let t5 = g.stamp(5);
    let t6 = g.stamp(6);
    assert!(g.is_valid(2, t2) && g.is_valid(5, t5) && g.is_valid(6, t6));

    // A restore diverges at depth 5: everything at depth >= 5 is abandoned.
    g.bump_from(5);

    // Spine (depth < 5) survives; the abandoned future (depth >= 5) is rejected.
    assert!(g.is_valid(2, t2), "shallow token survives the backjump");
    assert!(!g.is_valid(5, t5), "token at the cut is invalidated");
    assert!(!g.is_valid(6, t6), "deeper token is invalidated");

    // A fresh mint at depth 5 after the cut is valid again (new generation).
    let t5b = g.stamp(5);
    assert!(g.is_valid(5, t5b));
    assert!(
        t5b != t5,
        "the new generation differs from the abandoned one"
    );
}

#[test]
fn out_of_range_depth_is_invalid() {
    let g = GenStamps::new(4);
    assert!(!g.is_valid(4, 1));
    assert!(!g.is_valid(100, 1));
}
