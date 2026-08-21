// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Single-site timer for the AC-completion workload of `benches/saturate_bench.rs`.
//!
//! A Criterion gap is reproduced through a standalone binary before it is attributed
//! to code, because criterion's harness fixes neither heap position nor hot-loop
//! alignment. This binary covers the completion path: one workload, one
//! loop, no criterion, no other bench in the process.
//!
//! `cargo run --release --example complsite [pairs] [reps]`

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::saturate::saturate;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

/// Kept in step with `ac_completion` in `benches/saturate_bench.rs`.
fn ac_completion(pairs: usize) -> EG {
    let mut eg = EG::from_model(&NiraModel);
    eg.set_cc(true);
    let e = eg.intern_sort("E");
    eg.register_mset("add", e, e);
    let consts: Vec<OpId> = (0..pairs + 3)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let add = eg.ops().id_by_name("add").unwrap();
    let ids: Vec<ENodeId> = consts.iter().map(|&c| eg.add(c, &[])).collect();
    for i in 0..pairs {
        let s = eg.add(add, &[ids[i], ids[i + 1]]);
        eg.merge(s, ids[i + 2]);
    }
    for i in 0..pairs.saturating_sub(1) {
        eg.add(add, &[ids[i + 2], ids[i + 1]]);
    }
    eg.rebuild();
    eg
}

fn main() {
    let mut a = std::env::args().skip(1);
    let pairs: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(64);
    let reps: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(200);
    let g = GlobalCtx::<SortId, ENodeId>::new();

    // Report the minimum, not the mean: the noise here is additive (scheduler,
    // page faults, frequency), so the fastest observed run is the closest thing
    // to the code's cost. Same reduction `containers-conformance`'s perf gate
    // uses, for the same reason.
    let mut best = f64::INFINITY;
    let mut acc = 0usize;
    for _ in 0..reps {
        let mut eg = ac_completion(pairs);
        let t = std::time::Instant::now();
        let r = saturate(&[], &mut eg, &NiraModel, 1, &g);
        let dt = t.elapsed().as_secs_f64() * 1e3;
        acc += r.iterations + eg.node_count();
        best = best.min(dt);
    }
    println!("accompl{pairs}: min {best:.4} ms over {reps} reps (checksum {acc})");
}
