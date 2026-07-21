// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance criteria: AU identity widths follow EGraphConfig.
//!
//! The behavioral contract (`au_identity_width_matches_config64`) checks the
//! id types the PRODUCTION AU path uses under Config64; it stays ignored until
//! the AU subsystem is genericized over `Cfg::Au`. The two family tests only
//! pin the `AuIds` bundles themselves and are supplementary, not a substitute.

use semi_persistent_egraph::config::{AuIds, EGraphConfig};
use semi_persistent_egraph::nodes::{Config64, DefaultConfig};

/// The desired-contract regression: the id types used by production AU code
/// under Config64 must be 8 bytes wide. Production AU instantiates every
/// container through `Cfg::Au`, so the types checked here are exactly the
/// ones a `anti_unify::<Config64, ...>` call allocates: the result's term id,
/// the snapshot's class id, and the search space's node/context ids.
#[test]
fn au_identity_width_matches_config64() {
    use semi_persistent_egraph::au::session::{AuResult, TermOf};

    type G64 = <Config64 as EGraphConfig>::G;
    type Au64 = <Config64 as EGraphConfig>::Au;
    let expected = core::mem::size_of::<G64>();
    assert_eq!(expected, 8);

    // The production result type's term id.
    assert_eq!(core::mem::size_of::<TermOf<Config64>>(), expected);
    // Every id the production containers are keyed by.
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::Class>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::Or>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::Action>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::Context>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::Term>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::OrStats>(), expected);
    assert_eq!(core::mem::size_of::<<Au64 as AuIds>::AndStats>(), expected);
    assert_eq!(
        core::mem::size_of::<<Au64 as AuIds>::OrEdgeStat>(),
        expected
    );
    assert_eq!(
        core::mem::size_of::<<Au64 as AuIds>::AndChildStat>(),
        expected
    );

    // Compile-time proof the production result uses the wide term id: this
    // function only type-checks because AuResult<Config64>::term_id is
    // TermOf<Config64>.
    #[allow(dead_code)]
    fn production_result_term_is_wide(r: &AuResult<Config64>) -> TermOf<Config64> {
        r.term_id
    }
}

/// 31-bit family: every type is 4 bytes (u32 backing).
#[test]
fn au_ids_31_have_u32_width() {
    type A = <DefaultConfig as EGraphConfig>::Au;
    assert_eq!(core::mem::size_of::<<A as AuIds>::Class>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Scc>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Or>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Action>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Context>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Term>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::OrStats>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::AndStats>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::OrEdgeStat>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::AndChildStat>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::SnapshotMember>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::ContextElem>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::TermChild>(), 4);
    assert_eq!(core::mem::size_of::<<A as AuIds>::ReachBlock>(), 4);
}

/// 63-bit family: every type is 8 bytes (u64 backing).
#[test]
fn au_ids_64_have_u64_width() {
    type A = <Config64 as EGraphConfig>::Au;
    assert_eq!(core::mem::size_of::<<A as AuIds>::Class>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Scc>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Or>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Action>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Context>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::Term>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::OrStats>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::AndStats>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::OrEdgeStat>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::AndChildStat>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::SnapshotMember>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::ContextElem>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::TermChild>(), 8);
    assert_eq!(core::mem::size_of::<<A as AuIds>::ReachBlock>(), 8);
}
