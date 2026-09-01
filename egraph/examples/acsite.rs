// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Single-site timer for the AC-rewrite workloads of `benches/saturate_bench.rs`.
//!
//! The companion of `complsite.rs`: it reproduces a Criterion delta in a
//! standalone binary before attributing it to code. `complsite` covers the
//! completion path; this covers the `ac_rules` path, which is where the
//! index-build experiments show their gains and therefore where those gains have
//! to be confirmed.
//!
//! One workload, one loop, no criterion, no other bench in the process.
//! Reduced by minimum: the noise is additive, so the fastest run is closest to
//! the code's cost.
//!
//! `cargo run --release --example acsite [width] [reps] [naive|semi]`

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::apply::{PreparedRule, compile_rewrite};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::RuleRegistry;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::saturate::{saturate, saturate_semi};
use semi_persistent_egraph::surface_ast::{SurfaceCommand, SurfacePattern};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Rule = PreparedRule<OpId, SortId, NiraLitVal>;

fn pat(src: &str) -> SurfacePattern {
    let mut p = semi_persistent_egraph::parser::parse_patterns(src).unwrap();
    p.remove(0)
}

fn rhs_of(src: &str) -> semi_persistent_egraph::ast::RhsTerm {
    let wrapped = format!("(rewrite x {src})");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&wrapped).unwrap();
    match cmds.into_iter().next().unwrap() {
        SurfaceCommand::Rewrite { rhs, .. } => rhs,
        _ => unreachable!("wrapped source is a rewrite"),
    }
}

fn mk(eg: &EG, rr: &mut RuleRegistry<false>, lhs: &str, rhs: &str) -> Rule {
    compile_rewrite(
        "site",
        lhs,
        rhs,
        &pat(lhs),
        &rhs_of(rhs),
        &[],
        false,
        eg.ops(),
        eg.sorts(),
        rr,
        &NiraModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("rule must compile")
}

/// Kept in step with `ac_rules` in `benches/saturate_bench.rs`.
fn ac_rules(width: usize) -> (EG, Vec<Rule>) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_mset("add", e, e);
    eg.register_op2("mul", e, e, e);
    let consts: Vec<OpId> = (0..=width)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let add = eg.ops().id_by_name("add").unwrap();
    let mul = eg.ops().id_by_name("mul").unwrap();
    let ids: Vec<ENodeId> = consts.iter().map(|&c| eg.add(c, &[])).collect();
    let muls: Vec<ENodeId> = (0..width)
        .map(|i| eg.add(mul, &[ids[i], ids[i + 1]]))
        .collect();
    eg.add(add, &muls);
    eg.rebuild();

    let mut rr = RuleRegistry::<false>::new();
    let rules = vec![
        mk(
            &eg,
            &mut rr,
            "(add (mul x y) (mul z w) ..r)",
            "(add (mul y x) (mul w z) ..r)",
        ),
        mk(&eg, &mut rr, "(add (mul x y) ..r)", "(add (mul y x) ..r)"),
    ];
    (eg, rules)
}

fn main() {
    let mut a = std::env::args().skip(1);
    let width: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(6);
    let reps: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(200);
    let semi = a.next().map(|s| s == "semi").unwrap_or(false);
    let g = GlobalCtx::<SortId, ENodeId>::new();

    let mut best = f64::INFINITY;
    let mut acc = 0usize;
    for _ in 0..reps {
        let (mut eg, rules) = ac_rules(width);
        let t = std::time::Instant::now();
        // The benchmark's rules are total on their operands; a fault would mean
        // the site itself is malformed, which is not what it measures.
        let r = if semi {
            saturate_semi(&rules, &mut eg, &NiraModel, 4, &g)
        } else {
            saturate(&rules, &mut eg, &NiraModel, 4, &g)
        }
        .expect("benchmark rules are total");
        let dt = t.elapsed().as_secs_f64() * 1e3;
        acc += r.iterations + eg.node_count();
        best = best.min(dt);
    }
    let driver = if semi { "semi" } else { "naive" };
    println!("ac{width}/{driver}: min {best:.4} ms over {reps} reps (checksum {acc})");
}
