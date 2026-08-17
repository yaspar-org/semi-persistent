// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The index families build into recycled span arenas, so a build writes only
//! the keys its own stream carries and leaves an earlier build's keys in the
//! table. These tests fence the two things that makes load-bearing:
//!
//! * a build over a **reused** arena has the same per-key contents as the same
//!   build over a **fresh** one — that is, every key an earlier build wrote and
//!   this one did not reads as empty rather than as the earlier build's bucket;
//! * the arena is genuinely reused, so the span table stops being reallocated
//!   per round.
//!
//! The first is the correctness property the container states in `build_in`'s
//! ensures; this checks the consumer actually gets it, including in the case
//! that would silently pass if stamping were broken — a second build whose key
//! space is *smaller* than the first's, so the stale keys are in range.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::index::{IndexScratch, IndexStore};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Cfg = DefaultConfig;

fn base() -> EG {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op1("g", e, e);
    eg.register_op0("a", e);
    eg.register_op0("b", e);
    eg.register_op0("c", e);
    let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
    let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
    let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
    let fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
    let _fcb = eg.add(eg.ops().id_by_name("f").unwrap(), &[c, b]);
    let _gfab = eg.add(eg.ops().id_by_name("g").unwrap(), &[fab]);
    eg.rebuild();
    eg
}

/// Every family's every key, as the flat list a comparison can be made on.
fn snapshot(ix: &IndexStore<Cfg>) -> Vec<Vec<Vec<usize>>> {
    let fams: [&semi_persistent_containers::DenseSpanMap<
        <Cfg as semi_persistent_egraph::config::EGraphConfig>::G,
    >; 4] = [&ix.by_op, &ix.by_repr, &ix.by_child_pos, &ix.by_contains];
    fams.iter()
        .map(|m| {
            (0..m.len())
                .map(|k| {
                    m.try_get(k)
                        .unwrap_or(&[])
                        .iter()
                        .map(|g| g.to_usize())
                        .collect()
                })
                .collect()
        })
        .collect()
}

/// A build into a reused arena equals the same build into a fresh one.
///
/// The graph shrinks its key space between the two builds on the shared
/// scratch: `merge` collapses classes, so the second build's `by_repr` and
/// `by_child_pos` key bounds fall below the first's and the first build's keys
/// sit *inside* the second's range. A table that were merely overwritten rather
/// than stamped would hand those stale buckets back.
#[test]
fn reused_arena_matches_a_fresh_one() {
    let mut eg = base();
    let mut shared = IndexScratch::<Cfg>::new();

    // Round 1 on the shared scratch: fills the arenas at the wide key space.
    let first = IndexStore::build_with(&eg, &mut shared);
    let first_fresh = IndexStore::build(&eg);
    assert_eq!(
        snapshot(&first),
        snapshot(&first_fresh),
        "first build over a fresh arena must already agree"
    );
    // Keep round 1's contents to prove round 2 really does leave a stale key.
    let first_repr_ref = first_fresh;
    first.recycle_into(&mut shared, true);

    // Collapse classes so the next build touches fewer keys, and lower ones.
    let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
    let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
    let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
    eg.merge(a, b);
    eg.merge(b, c);
    eg.rebuild();

    // Round 2 over the arenas round 1 left populated, against a fresh build.
    let reused = IndexStore::build_with(&eg, &mut shared);
    let fresh = IndexStore::build(&eg);
    // The check is only meaningful if round 1 left a key that round 2 does not
    // write and that is still inside round 2's key range — a key a broken stamp
    // would surface. Assert one exists rather than trusting the shape.
    let (before_repr, after_repr) = (&snapshot(&first_repr_ref)[1], &snapshot(&reused)[1]);
    let stale = (0..after_repr.len())
        .any(|k| after_repr[k].is_empty() && k < before_repr.len() && !before_repr[k].is_empty());
    assert!(
        stale,
        "the merge must leave at least one in-range key occupied in round 1 and empty in round 2, \
         or this test cannot detect a missing stamp check"
    );
    assert_eq!(
        snapshot(&reused),
        snapshot(&fresh),
        "a build over a reused arena must not surface the previous build's keys"
    );
    reused.recycle_into(&mut shared, true);
}

/// The arenas come back and stay back: capacity is held across rounds instead
/// of being reallocated per build.
#[test]
fn arena_capacity_is_retained_across_rounds() {
    let eg = base();
    let mut scratch = IndexScratch::<Cfg>::new();
    assert_eq!(
        scratch.arena_capacity(),
        0,
        "a new scratch holds no span table"
    );

    IndexStore::build_with(&eg, &mut scratch).recycle_into(&mut scratch, true);
    let after_first = scratch.arena_capacity();
    assert!(
        after_first > 0,
        "the first round's span tables must come back to the scratch"
    );

    for _ in 0..8 {
        IndexStore::build_with(&eg, &mut scratch).recycle_into(&mut scratch, true);
    }
    assert_eq!(
        scratch.arena_capacity(),
        after_first,
        "a steady-state graph must not grow the retained span tables per round"
    );
}

/// The full and delta stores draw from separate arena sets, so building both in
/// one round — which semi-naive does — does not hand one table to two live maps.
#[test]
fn full_and_delta_hold_separate_arenas() {
    let mut eg = base();
    let mut scratch = IndexScratch::<Cfg>::new();

    let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
    let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
    eg.merge(a, b);
    eg.rebuild();
    let touched: Vec<_> = eg.touched().to_vec();

    let full = IndexStore::build_with(&eg, &mut scratch);
    let delta = IndexStore::build_delta_with(&eg, &touched, &mut scratch);

    // Both alive at once, and each agrees with the same build made alone.
    let full_alone = IndexStore::build(&eg);
    let delta_alone = IndexStore::build_delta(&eg, &touched);
    assert_eq!(snapshot(&full), snapshot(&full_alone), "full store");
    assert_eq!(snapshot(&delta), snapshot(&delta_alone), "delta store");

    delta.recycle_into(&mut scratch, false);
    full.recycle_into(&mut scratch, true);
    assert!(
        scratch.arena_capacity() > 0,
        "both stores' arenas return to the scratch"
    );
}
