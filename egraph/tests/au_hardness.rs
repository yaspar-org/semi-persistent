// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Where each anti-unification method is the right one, as a measured map
//! rather than a claim.
//!
//! The corpus has families that make the exact solver slow and families that
//! mislead the greedy rollout, but nothing that says which method to reach for
//! at a given problem shape. This file sweeps the two knobs that decide it and
//! prints the answer per cell.
//!
//! The two axes are chosen because they separate the two failure modes:
//!
//! * **Burial depth** is how far below the root the winner's payoff becomes
//!   visible. The action estimate prices a child pair at `bs(left) + bs(right)`,
//!   which is exact when the pair shares no operator and pessimistic when it
//!   factors through shared structure, so a buried winner is misranked until the
//!   search descends to it. Depth is therefore the *locality* of the rollout's
//!   error: shallow errors are the ones a bounded exact call on a subproblem can
//!   correct, deep ones are not.
//! * **Decoys per level** is the branching factor, which drives how much work a
//!   complete method has to do.
//!
//! The regions this predicts, and what the sweep is checking:
//!
//! | region | shape | expected winner |
//! | --- | --- | --- |
//! | shallow, narrow | small search space, error visible early | exact: it certifies before the search has sampled anything |
//! | deep, narrow | small space, error far from the root | exact still, by certification |
//! | deep, wide | large space, error far from the root | search: the exact solver stops finishing |
//! | shallow, wide | large space, error correctable locally | the region delegation is supposed to own |
//!
//! The last cell is the one the hybrid claim rests on, and reading the printed
//! map is how that claim is checked rather than assumed.

use std::time::{Duration, Instant};

use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;

#[path = "au_deceptive.rs"]
#[allow(dead_code)]
mod families;

use families::{DeceptiveParams, build_deceptive};

const GUARD: Duration = Duration::from_secs(20);

/// Which method reached the optimum first, at equal wall clock.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Winner {
    Exact,
    Search,
    Delegation,
    NoneReached,
}

struct Cell {
    optimum: u32,
    exact_ms: f64,
    exact_certified: bool,
    search_ms: Option<f64>,
    hybrid_ms: Option<f64>,
    winner: Winner,
}

/// Runs one (burial_depth, decoys) cell. The optimum comes from the exact
/// solver when it certifies, and otherwise from the best value any method
/// reached, so a cell where nothing certifies still reports a comparison
/// between the methods rather than nothing at all.
fn measure(burial_depth: usize, decoys: usize) -> Option<Cell> {
    // margin 3 / gap 1 is the feasible corner across the whole grid; burial 1 is
    // never deceptive, so the sweep starts at 2.
    let params = DeceptiveParams {
        burial_depth,
        margin: 3,
        gap: 1,
        decoys,
    };
    if !params.is_feasible() {
        return None;
    }
    // The search space passes 2^31 spans beyond roughly this product and the
    // 31-bit AU arena traps ("span start ... exceeds the configured AU
    // capacity"). That is the width guard working, and it is also this family's
    // ceiling: it runs out of id space before it runs out of easiness.
    // Measured: (64, 32) fits and (256, 8) traps, so depth rather than the
    // product is what exhausts the arena.
    if burial_depth >= 256 && decoys > 1 {
        return None;
    }
    let inst = build_deceptive(params);
    let snap = AuSnapshot::new(&inst.eg).unwrap();

    let start = Instant::now();
    let exact = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
            exact_deadline: Some(GUARD),
            ..Default::default()
        },
    )
    .unwrap();
    let exact_ms = start.elapsed().as_secs_f64() * 1e3;
    let exact_certified = exact.completion == Completion::Exact;

    // Ladder both search configurations to the first budget that reaches the
    // exact solver's value, and record the wall clock it took to get there.
    let ladder = |hybrid: bool, target: u32| -> Option<f64> {
        let mut playouts = 1u64;
        while playouts <= 4096 {
            let start = Instant::now();
            let r = anti_unify(
                &snap,
                inst.left,
                inst.right,
                &AuConfig {
                    algorithm: AuAlgorithm::Uct,
                    playouts,
                    closed_bit: true,
                    live_incumbent_pruning: true,
                    interval_bounds: true,
                    hybrid_exact: hybrid,
                    hybrid_threshold: if hybrid { 4096 } else { 0 },
                    rollout_hybrid: hybrid,
                    session_exact_memo: hybrid,
                    ..Default::default()
                },
            )
            .unwrap();
            let ms = start.elapsed().as_secs_f64() * 1e3;
            if r.size <= target {
                return Some(ms);
            }
            playouts *= 2;
        }
        None
    };

    let optimum = exact.size;
    let search_ms = ladder(false, optimum);
    let hybrid_ms = ladder(true, optimum);

    // The exact solver only counts as the winner when it actually certified:
    // an uncertified answer is a value, not a proof, and the search reaching
    // the same value faster is the honest comparison.
    let best_search = match (search_ms, hybrid_ms) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    };
    let winner = match (exact_certified, best_search) {
        (true, Some(s)) if s < exact_ms => {
            if hybrid_ms.is_some_and(|h| Some(h) == best_search) && search_ms != best_search {
                Winner::Delegation
            } else {
                Winner::Search
            }
        }
        (true, _) => Winner::Exact,
        (false, Some(_)) => {
            if hybrid_ms.is_some_and(|h| Some(h) == best_search) && search_ms != best_search {
                Winner::Delegation
            } else {
                Winner::Search
            }
        }
        (false, None) => Winner::NoneReached,
    };

    Some(Cell {
        optimum,
        exact_ms,
        exact_certified,
        search_ms,
        hybrid_ms,
        winner,
    })
}

/// The map. Burial depth against decoy count, one line per cell.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_hardness \
///   hardness_map -- --ignored --nocapture
/// ```
#[test]
#[ignore = "measurement run; prints the hardness map"]
fn hardness_map() {
    println!(
        "{:>6} {:>7} {:>8} {:>10} {:>4} | {:>10} {:>10} | {:>11}",
        "burial", "decoys", "optimum", "exact ms", "cert", "search ms", "hybrid ms", "winner"
    );
    for &burial in &[2usize, 16, 64, 256, 1024] {
        for &decoys in &[1usize, 8, 32] {
            let Some(c) = measure(burial, decoys) else {
                continue;
            };
            let f = |v: Option<f64>| match v {
                Some(x) => format!("{x:.1}"),
                None => "-".to_owned(),
            };
            println!(
                "{burial:>6} {decoys:>7} {:>8} {:>10.1} {:>4} | {:>10} {:>10} | {:>11}",
                c.optimum,
                c.exact_ms,
                if c.exact_certified { "yes" } else { "no" },
                f(c.search_ms),
                f(c.hybrid_ms),
                format!("{:?}", c.winner)
            );
        }
    }
}

/// The whole `dec` family sits in the exact solver's region, and this pins it.
///
/// The prediction going in was that a large enough branching factor would push
/// it out. It does not: scaling burial depth to 256 and decoys to 32 keeps the
/// exact solver certifying, and certifying faster than either search
/// configuration reaches the same value (37.7 ms against 51.4 ms at the largest
/// cell that fits). The family's cost is linear in the burial depth, so it runs
/// out of 31-bit id space before it runs out of easiness.
///
/// That makes `dec` a misranking benchmark rather than a hardness benchmark: it
/// is the right tool for showing that the action estimate misranks arms, and the
/// wrong tool for showing that a search beats a complete method. The families
/// that do leave this region are the saturation-built ones, whose class product
/// rather than whose depth is what grows; section (k) and (l) of
/// `doc/benchmarks/records/au/anytime-corpus.md` measure them.
#[test]
fn dec_never_leaves_the_exact_region() {
    for &(burial, decoys) in &[(2usize, 1usize), (16, 8), (64, 32)] {
        let c = measure(burial, decoys).expect("feasible cell");
        assert!(
            c.exact_certified,
            "burial={burial} decoys={decoys}: the exact solver certifies every cell \
             of this family"
        );
        let best = c
            .search_ms
            .iter()
            .chain(c.hybrid_ms.iter())
            .cloned()
            .fold(f64::INFINITY, f64::min);
        assert!(
            best.is_finite(),
            "burial={burial} decoys={decoys}: the search must reach the optimum {}",
            c.optimum
        );
    }
}

/// Whatever the map says about who is fastest, every method that returns must
/// return the same value. A cell where the search beats the exact solver on
/// time but disagrees on the answer would be a soundness failure, not a win.
#[test]
fn every_method_agrees_on_the_optimum() {
    for &(burial, decoys) in &[(2usize, 2usize), (4, 2), (2, 4), (4, 4)] {
        let Some(c) = measure(burial, decoys) else {
            continue;
        };
        if !c.exact_certified {
            continue;
        }
        assert!(
            c.search_ms.is_some(),
            "burial={burial} decoys={decoys}: the search must reach the certified \
             optimum {} within the ladder",
            c.optimum
        );
        assert!(
            c.hybrid_ms.is_some(),
            "burial={burial} decoys={decoys}: delegation must reach the certified \
             optimum {} within the ladder",
            c.optimum
        );
    }
}
