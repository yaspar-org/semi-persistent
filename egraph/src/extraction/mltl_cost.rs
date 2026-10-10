// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The MLTL memory cost, written in Rust: the twin the Roto, ASP, and MiniZinc specifications
//! of `tests/mltl/costs/` are checked against.
//!
//! [`mltl_memory`] is the whole cost function. It is generic over the rung, so the
//! same code extracts with the flat rendering, chains, every unordered tree, every
//! binary tree, or every ordered tree; only the rung it is built on changes. It is
//! a crate of its own so that Semper registers it directly.
//!
//! [`pipeline_registers`] and [`monitor_history`] are the costs of
//! `costs/pipeline_registers.roto` and `costs/monitor_history.roto`, written in
//! Rust for the tests that compare each script with its Rust twin.

use crate::extraction::Cost;
use crate::extraction::graph::Node;
use crate::extraction::oint::Build;
use crate::extraction::rung::Rung;

/// The interval a bounded temporal operator carries, as `(lb, ub)`, clamped below at 0.
/// Exact: an interval bound past `i64` is the number it is.
fn bounds(n: &Node) -> (Cost, Cost) {
    match n.op.as_str() {
        "Global" | "Future" | "Until" | "Release" if n.ints.len() >= 2 => {
            (n.ints[0].max(Cost::ZERO), n.ints[1].max(Cost::ZERO))
        }
        _ => (Cost::ZERO, Cost::ZERO),
    }
}

/// R2U2's minimum monitor memory: per class, the queue an early producer needs
/// while its latest sibling finishes, `max(max sibling wpd − own bpd, 0) + 1`, plus
/// the same for every internal node of a rendered flat node, plus the
/// specification wrapper's queue. A Boolean constant occupies none.
pub fn mltl_memory<R: Rung + ?Sized>(r: &R, b: &mut Build) {
    let wpd = b.rec_max(r, &|n| bounds(n).1);
    let bpd = b.rec_min(r, &|n| bounds(n).0);
    let g = r.graph();
    b.cost_base(1);
    for &c in &r.selection().reachable {
        let mut peers = Vec::new();
        for &n in r.selection().parents(c) {
            for (gates, s) in r.siblings(n, c) {
                peers.push((gates, wpd[s].clone().unwrap()));
            }
        }
        let peers = b.max_of(&peers);
        let queue = b.clamp_sub(&peers, bpd[c].as_ref().unwrap());
        let counted = g
            .candidates(c)
            .next()
            .is_some_and(|n| g.nodes[n].op != "Bool");
        if counted {
            b.cost_if(r.selection().class(c), 1);
            b.cost(&queue);
        }
        for n in g.candidates(c) {
            for inner in r.inner_nodes(n) {
                let with = |gs: &Vec<crate::extraction::Lit>| {
                    let mut v = vec![inner.exists];
                    v.extend(gs.iter().copied());
                    v
                };
                let sibs: Vec<_> = inner
                    .siblings
                    .iter()
                    .map(|(gs, s)| (with(gs), wpd[*s].clone().unwrap()))
                    .collect();
                let mems: Vec<_> = inner
                    .members
                    .iter()
                    .map(|(gs, s)| (with(gs), bpd[*s].clone().unwrap()))
                    .collect();
                let peers = b.max_of(&sibs);
                let own = b.min_of(&mems);
                let q = b.clamp_sub(&peers, &own);
                b.cost_if(inner.exists, 1);
                b.cost(&q);
            }
        }
    }
}

/// The latency of an arithmetic operator, in cycles.
fn latency(n: &Node) -> u64 {
    match n.op.as_str() {
        "Add" | "Neg" => 1,
        "Mul" => 3,
        "Div" => 12,
        "Call1" | "Call2" | "Call3" => 20,
        _ => 0,
    }
}

/// Pipeline register balancing: one unit per operator, plus one delay register per
/// cycle an input waits for the latest input of its operator. The internal nodes
/// of a rendered flat node are partial results of no latency.
pub fn pipeline_registers<R: Rung + ?Sized>(r: &R, b: &mut Build) {
    let late = b.rec_max(r, &latency);
    let early = b.rec_max_down(r, &latency);
    let g = r.graph();
    for &c in &r.selection().reachable {
        let mut peers = Vec::new();
        for &n in r.selection().parents(c) {
            for (gates, s) in r.siblings(n, c) {
                peers.push((gates, late[s].clone().unwrap()));
            }
        }
        let peers = b.max_of(&peers);
        let wait = b.clamp_sub(&peers, early[c].as_ref().unwrap());
        b.cost(&wait);
        let leaf = g
            .candidates(c)
            .next()
            .is_some_and(|n| matches!(g.nodes[n].op.as_str(), "Var" | "Num"));
        if !leaf {
            b.cost_if(r.selection().class(c), 1);
        }
        for n in g.candidates(c) {
            for inner in r.inner_nodes(n) {
                let with = |gs: &Vec<crate::extraction::Lit>| {
                    let mut v = vec![inner.exists];
                    v.extend(gs.iter().copied());
                    v
                };
                let sibs: Vec<_> = inner
                    .siblings
                    .iter()
                    .map(|(gs, s)| (with(gs), late[*s].clone().unwrap()))
                    .collect();
                let mems: Vec<_> = inner
                    .members
                    .iter()
                    .map(|(gs, s)| (with(gs), early[*s].clone().unwrap()))
                    .collect();
                let peers = b.max_of(&sibs);
                let own = b.max_of_down(&mems);
                let q = b.clamp_sub(&peers, &own);
                b.cost(&q);
            }
        }
    }
}

/// The window over which parent `n` needs the history of its child class `c`:
/// `W` for `Formerly(W, c)` and for `Since(W, a, c)`, 0 otherwise.
fn window(n: &Node, c: crate::extraction::graph::ClassId) -> Cost {
    match n.op.as_str() {
        "Formerly" if !n.ints.is_empty() => n.ints[0].max(Cost::ZERO),
        "Since" if !n.ints.is_empty() && n.children.len() >= 2 && n.children[1] == c => {
            n.ints[0].max(Cost::ZERO)
        }
        _ => Cost::ZERO,
    }
}

/// History a past-time monitor keeps: per class, the widest window any selected
/// parent needs of it, plus one unit of evaluation per selected class.
pub fn monitor_history<R: Rung + ?Sized>(r: &R, b: &mut Build) {
    let g = r.graph();
    for &c in &r.selection().reachable {
        let mut uses = Vec::new();
        for &n in r.selection().parents(c) {
            let w = window(&g.nodes[n], c);
            if w > 0 {
                let k = b.constant(w).over();
                uses.push((vec![r.selection().node(n)], k));
            }
        }
        let widest = b.max_of(&uses);
        b.cost(&widest);
        b.cost_if(r.selection().class(c), 1);
    }
}
