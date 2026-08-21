// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anytime behavior of the exact solver under `AuConfig::exact_deadline`.
//!
//! On a hard instance (the cyclic-class crossover family at cycles=8, whose
//! exact state space dwarfs any tiny deadline), `Some(tiny)` must return
//! quickly with `Completion::BudgetExhausted` and a feasible term — both
//! projections materialize back into the source classes — while `None` (the
//! default, what the differential gate runs) must certify
//! `Completion::Exact` with equal-or-better lexicographic quality on the
//! same instance.

use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

// ---------------------------------------------------------------------------
// Instance: the cyclic-class family of au_scaling_crossover.rs
// `build_instance` at depth 4, width cycles-1 (the sweep's shape), as
// mirrored in au_differential.rs `build_crossover`. cycles=8 is past the
// differential corpus ceiling (cycles<=6): reachable cycle-context pairs
// grow combinatorially in `cycles`, so a completed exact solve does far
// more work than a tiny deadline allows.
// ---------------------------------------------------------------------------

fn build_crossover(cycles: usize) -> (Eg, ENodeId, ENodeId) {
    assert!(cycles >= 2, "hot leaves need two distinct W classes");
    let depth = 4usize;
    let width = cycles - 1;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let f = eg.register_op2("f", sort, sort, sort);
    let b = eg.register_op2("b", sort, sort, sort);
    let h = eg.register_op1("h", sort, sort);
    let p_op = eg.register_op0("p", sort);
    let dl_op = eg.register_op0("dl", sort);
    let dr_op = eg.register_op0("dr", sort);
    let w_ops: Vec<OpId> = (0..cycles)
        .map(|i| eg.register_op0(&format!("w{i}"), sort))
        .collect();
    let tag_ops: Vec<OpId> = (0..cycles)
        .map(|i| eg.register_op0(&format!("t{i}"), sort))
        .collect();

    let w: Vec<ENodeId> = w_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let tags: Vec<ENodeId> = tag_ops.iter().map(|&op| eg.add(op, &[])).collect();
    for &wi in &w {
        let hw = eg.add(h, &[wi]);
        eg.merge(hw, wi);
    }
    let fan = width.min(cycles - 1);
    for (i, &tag) in tags.iter().enumerate() {
        for j in 1..=fan {
            let target = w[(i + j) % cycles];
            let member = eg.add(b, &[target, tag]);
            eg.merge(member, w[i]);
        }
    }
    eg.rebuild();

    let shared = eg.add(p_op, &[]);
    let dl = eg.add(dl_op, &[]);
    let dr = eg.add(dr_op, &[]);
    let n_leaves = 1usize << depth;
    let mut left_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    let mut right_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    for t in 0..n_leaves {
        match t % 4 {
            0 => {
                left_level.push(w[t % cycles]);
                right_level.push(w[(t + 1) % cycles]);
            }
            2 => {
                left_level.push(dl);
                right_level.push(dr);
            }
            _ => {
                left_level.push(shared);
                right_level.push(shared);
            }
        }
    }
    while left_level.len() > 1 {
        left_level = left_level.chunks(2).map(|c| eg.add(f, c)).collect();
        right_level = right_level.chunks(2).map(|c| eg.add(f, c)).collect();
    }
    eg.rebuild();
    (eg, left_level[0], right_level[0])
}

// ---------------------------------------------------------------------------
// Projection validity (pattern from au_differential.rs / au_metamorphic.rs
// check_pair): both projections are Variants-free and materialize back into
// their source classes.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum OwnedTerm {
    App(OpId, Vec<OwnedTerm>),
    Lit(OpId, LitValId),
}

fn own_projected(pool: &TermPool<OpId, LitValId>, id: TermId) -> OwnedTerm {
    match pool.op(id) {
        TermOp::EGraph(op) => OwnedTerm::App(
            *op,
            pool.children(id)
                .iter()
                .map(|&child| own_projected(pool, child))
                .collect(),
        ),
        TermOp::Literal(op, value) => OwnedTerm::Lit(*op, *value),
        TermOp::Variants => panic!("projection still contains Variants"),
    }
}

fn materialize(eg: &mut Eg, term: &OwnedTerm) -> ENodeId {
    match term {
        OwnedTerm::App(op, children) => {
            let child_ids: Vec<ENodeId> = children.iter().map(|c| materialize(eg, c)).collect();
            eg.add(*op, &child_ids)
        }
        OwnedTerm::Lit(op, value) => eg.add_lit(*op, *value),
    }
}

fn assert_valid_projections(
    eg: &mut Eg,
    result: &mut AuResult<semi_persistent_egraph::nodes::DefaultConfig>,
    left: ENodeId,
    right: ENodeId,
    label: &str,
) {
    let l_proj = result.pool.project(result.term_id, 0);
    let r_proj = result.pool.project(result.term_id, 1);
    let (lo, ro) = (
        own_projected(&result.pool, l_proj),
        own_projected(&result.pool, r_proj),
    );
    let pl = materialize(eg, &lo);
    let pr = materialize(eg, &ro);
    eg.rebuild();
    assert_eq!(
        eg.find_const(pl),
        eg.find_const(left),
        "{label}: left projection does not re-evaluate into the left class"
    );
    assert_eq!(
        eg.find_const(pr),
        eg.find_const(right),
        "{label}: right projection does not re-evaluate into the right class"
    );
}

// ---------------------------------------------------------------------------
// The test.
// ---------------------------------------------------------------------------

/// A tiny deadline on a hard instance returns quickly with an uncertified
/// feasible incumbent; no deadline certifies the optimum on the same
/// instance at equal-or-better quality.
#[test]
fn exact_deadline_returns_anytime_incumbent() {
    let (mut eg, left, right) = build_crossover(8);

    // Tiny deadline: the solve is cut off long before completion.
    let mut anytime = {
        let snap = AuSnapshot::new(&eg).unwrap();
        let started = Instant::now();
        let result = anti_unify(
            &snap,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                exact_deadline: Some(Duration::from_millis(5)),
                ..Default::default()
            },
        )
        .unwrap();
        let elapsed = started.elapsed();
        // Overshoot is bounded by one 1024-entry polling window plus the
        // return path (milliseconds even in debug); the 2 s bound absorbs
        // CI noise while still cleanly separating "returned on the
        // deadline" from "ran to completion" (about 10 s debug on this
        // instance, measured 2026-08-15).
        assert!(
            elapsed < Duration::from_secs(2),
            "deadline of 5 ms overshot to {elapsed:?}"
        );
        result
    };
    assert_eq!(anytime.algorithm, AuAlgorithm::Exact);
    assert_eq!(
        anytime.completion,
        Completion::BudgetExhausted { playouts_used: 0 },
        "a tiny deadline on a hard instance must not claim Completion::Exact"
    );
    let anytime_quality = anytime.pool.quality(anytime.term_id);
    assert_valid_projections(&mut eg, &mut anytime, left, right, "anytime incumbent");

    // No deadline (the default, what the differential gate runs): certified
    // optimum, equal-or-better lexicographic quality.
    let mut certified = {
        let snap = AuSnapshot::new(&eg).unwrap();
        anti_unify(
            &snap,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                exact_deadline: None,
                ..Default::default()
            },
        )
        .unwrap()
    };
    assert_eq!(certified.completion, Completion::Exact);
    let certified_quality = certified.pool.quality(certified.term_id);
    assert!(
        certified_quality <= anytime_quality,
        "certified optimum {certified_quality:?} must not be worse than the anytime incumbent \
         {anytime_quality:?}"
    );
    assert_valid_projections(&mut eg, &mut certified, left, right, "certified optimum");
}
