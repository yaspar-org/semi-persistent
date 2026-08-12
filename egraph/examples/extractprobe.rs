// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Structural counts for the `extract_bench` workloads: class count, fixpoint
//! pass count, and reconstructed term size.
//!
//! The protocol in `doc/perf-results/README.md` requires confirming the
//! mechanism behind a timing delta, and for extraction the mechanism is a ratio
//! between two costs that no timer separates: the `extract_best` fixpoint is
//! O(classes x passes) while `reconstruct` is O(term size), which on a shared
//! DAG is exponentially larger than the class count. These counts say which of
//! the two a given bench row is actually measuring.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::ast::Term;
use semi_persistent_egraph::containers::DenseId;
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::nodes::DefaultConfig;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

fn tree(depth: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let f = eg.ops().id_by_name("f").unwrap();
    let leaves: Vec<OpId> = (0..=depth)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let mut acc = eg.add(leaves[0], &[]);
    for &c in &leaves[1..] {
        let leaf = eg.add(c, &[]);
        acc = eg.add(f, &[acc, leaf]);
    }
    eg.rebuild();
    (eg, acc)
}

fn dag(depth: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let c = eg.register_op0("c", e);
    let f = eg.ops().id_by_name("f").unwrap();
    let mut acc = eg.add(c, &[]);
    for _ in 0..depth {
        acc = eg.add(f, &[acc, acc]);
    }
    eg.rebuild();
    (eg, acc)
}

fn wide(width: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op2("g", e, e, e);
    let f = eg.ops().id_by_name("f").unwrap();
    let g = eg.ops().id_by_name("g").unwrap();
    let leaves: Vec<ENodeId> = (0..width)
        .map(|i| {
            let op = eg.register_op0(&format!("c{i}"), e);
            eg.add(op, &[])
        })
        .collect();
    let mut chain = leaves[0];
    for &l in &leaves[1..] {
        chain = eg.add(g, &[chain, l]);
    }
    let root = eg.add(f, &[leaves[0], chain]);
    for &l in &leaves[1..] {
        let alt = eg.add(f, &[l, chain]);
        eg.merge(root, alt);
    }
    eg.rebuild();
    (eg, root)
}

fn term_size(t: &Term) -> usize {
    match t {
        Term::App { children, .. } => 1 + children.iter().map(term_size).sum::<usize>(),
        _ => 1,
    }
}

/// Replay `extract_best`'s fixpoint to count how many passes it takes. Kept in
/// sync with `extract.rs` by shape, not by sharing code: this is a measurement
/// of the algorithm, and a shared helper would hide a divergence rather than
/// report it.
fn passes(eg: &EG, _root: ENodeId) -> usize {
    let n = eg.len();
    let mut best: Vec<usize> = vec![usize::MAX; n];
    let mut p = 0;
    loop {
        p += 1;
        let mut changed = false;
        for i in 0..n {
            let id = ENodeId::from_usize(i);
            let repr = eg.find_const(id);
            let mut total = 1usize;
            let mut ok = true;
            eg.for_each_child(id, |child, mult| {
                if !ok {
                    return;
                }
                let c = best[eg.find_const(child).to_usize()];
                if c == usize::MAX {
                    ok = false;
                } else {
                    total = total.saturating_add(c.saturating_mul(mult.to_usize()));
                }
            });
            if ok && total < best[repr.to_usize()] {
                best[repr.to_usize()] = total;
                changed = true;
            }
        }
        if !changed {
            return p;
        }
    }
}

fn report(label: &str, eg: &EG, root: ENodeId) {
    let t = extract_best(eg, root).expect("root must extract");
    let p = passes(eg, root);
    let n = eg.len();
    println!(
        "{label:10} classes {n:>7}  passes {p:>3}  scan visits {:>9}  term nodes {:>9}",
        n * p,
        term_size(&t),
    );
}

/// Time extraction against a doubling depth sequence. A left-deep chain's class
/// count and term size are both O(depth), so anything steeper than linear here
/// is a cost the shape does not justify.
fn scaling() {
    println!("\ntree depth scaling (min of 5, us):");
    let mut prev = 0.0f64;
    for d in [25usize, 50, 100, 200, 400] {
        let (eg, root) = tree(d);
        let mut best = f64::INFINITY;
        let mut acc = 0usize;
        for _ in 0..5 {
            let t = std::time::Instant::now();
            let r = extract_best(&eg, root);
            best = best.min(t.elapsed().as_secs_f64() * 1e6);
            acc += r.map_or(0, |t| term_size(&t));
        }
        let ratio = if prev > 0.0 { best / prev } else { 0.0 };
        println!("  depth {d:>4}: {best:>10.1}  x{ratio:.2} vs half depth  (checksum {acc})");
        prev = best;
    }
}

fn main() {
    for d in [20usize, 200, 400] {
        let (eg, root) = tree(d);
        report(&format!("tree{d}"), &eg, root);
    }
    for d in [12usize, 16] {
        let (eg, root) = dag(d);
        report(&format!("dag{d}"), &eg, root);
    }
    for w in [32usize, 128] {
        let (eg, root) = wide(w);
        report(&format!("wide{w}"), &eg, root);
    }
    scaling();
}
