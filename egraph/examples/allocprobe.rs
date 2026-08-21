// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Allocation counter for the saturation workloads of `benches/saturate_bench.rs`.
//!
//! Wall-clock on this machine carries two confounds: heap position and hot-loop
//! cache-line alignment, each measured at up to ~18%, so a 3% timing delta is not by
//! itself evidence that a change did what it claimed. Allocation counts are
//! deterministic: they do not move with layout, order, or machine load. When an
//! experiment's stated mechanism is "this removes N allocations per match", this
//! is where that claim is checked.
//!
//! Run with `cargo run --release --example allocprobe`. Reports total
//! allocations, total bytes, and peak live bytes per workload. Counting is
//! process-wide and single-threaded here, so setup is measured separately from
//! saturation by reading the counters on either side.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::apply::{PreparedRule, compile_rewrite};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::RuleRegistry;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::surface_ast::{SurfaceCommand, SurfacePattern};

// ---------------------------------------------------------------------------
// Counting allocator
// ---------------------------------------------------------------------------

static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

struct Counting;

/// Deliberately `Relaxed`: these counters are read only between phases on the
/// same thread, never used to order anything. Stronger ordering would add cost
/// to every allocation in the measured region.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(l.size(), Ordering::Relaxed);
        let live = LIVE.fetch_add(l.size(), Ordering::Relaxed) + l.size();
        PEAK.fetch_max(live, Ordering::Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
    /// Forwarded explicitly rather than left to the default `alloc`+copy+`dealloc`:
    /// a `Vec` growing in place is one allocation event, and counting it as two
    /// (plus a spurious byte total) would misattribute exactly the growth
    /// behavior these experiments are about.
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new_size: usize) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        if new_size > l.size() {
            BYTES.fetch_add(new_size - l.size(), Ordering::Relaxed);
            let live = LIVE.fetch_add(new_size - l.size(), Ordering::Relaxed) + new_size - l.size();
            PEAK.fetch_max(live, Ordering::Relaxed);
        } else {
            LIVE.fetch_sub(l.size() - new_size, Ordering::Relaxed);
        }
        unsafe { System.realloc(p, l, new_size) }
    }
}

#[global_allocator]
static A: Counting = Counting;

#[derive(Copy, Clone)]
struct Snap {
    allocs: usize,
    bytes: usize,
}

fn snap() -> Snap {
    Snap {
        allocs: ALLOCS.load(Ordering::Relaxed),
        bytes: BYTES.load(Ordering::Relaxed),
    }
}

// ---------------------------------------------------------------------------
// Workloads — kept in step with benches/saturate_bench.rs
// ---------------------------------------------------------------------------

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Rule = PreparedRule<OpId, SortId, NiraLitVal>;

fn pat(src: &str) -> SurfacePattern {
    let mut p = semi_persistent_egraph::parser::parse_patterns(src).unwrap();
    assert_eq!(p.len(), 1);
    p.remove(0)
}

fn rhs_of(src: &str) -> semi_persistent_egraph::ast::RhsTerm {
    let wrapped = format!("(rewrite x {src})");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&wrapped).unwrap();
    match cmds.into_iter().next().unwrap() {
        SurfaceCommand::Rewrite { rhs, .. } => rhs,
        _ => unreachable!(),
    }
}

fn mk(eg: &EG, rr: &mut RuleRegistry<false>, lhs: &str, rhs: &str) -> Rule {
    compile_rewrite(
        "probe",
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
    .unwrap()
}

fn plain(leaves: usize) -> (EG, Vec<Rule>) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let consts: Vec<OpId> = (0..leaves)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let f = eg.ops().id_by_name("f").unwrap();
    let mut acc = eg.add(consts[0], &[]);
    for &c in &consts[1..] {
        let leaf = eg.add(c, &[]);
        acc = eg.add(f, &[acc, leaf]);
    }
    eg.rebuild();
    let mut rr = RuleRegistry::<false>::new();
    let rules = vec![
        mk(&eg, &mut rr, "(f a b)", "(f b a)"),
        mk(&eg, &mut rr, "(f (f a b) c)", "(f a (f b c))"),
    ];
    (eg, rules)
}

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

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

fn probe(name: &str, semi: bool, limit: usize, build: impl Fn() -> (EG, Vec<Rule>)) {
    semi_persistent_egraph::ematch::set_match_step_counting(true);
    semi_persistent_egraph::ematch::reset_match_steps();

    let (mut eg, rules) = build();
    let g = GlobalCtx::<SortId, ENodeId>::new();

    // Read the counters *after* setup, so what is reported is saturation only.
    let before = snap();
    let peak_before = PEAK.load(Ordering::Relaxed);
    PEAK.store(LIVE.load(Ordering::Relaxed), Ordering::Relaxed);

    let r = if semi {
        semi_persistent_egraph::saturate::saturate_semi(&rules, &mut eg, &NiraModel, limit, &g)
    } else {
        semi_persistent_egraph::saturate::saturate(&rules, &mut eg, &NiraModel, limit, &g)
    };

    let after = snap();
    let peak = PEAK.load(Ordering::Relaxed);
    let _ = peak_before;

    let steps = r.match_steps.max(1);
    let allocs = after.allocs - before.allocs;
    println!(
        "{name:22} {:>10} allocs  {:>12} B  peak {:>10} B  steps {:>10}  {:>6.2} allocs/step  nodes {}",
        allocs,
        after.bytes - before.bytes,
        peak,
        r.match_steps,
        allocs as f64 / steps as f64,
        eg.node_count(),
    );
}

fn main() {
    println!("--- plain (fixed-arity joins) ---");
    probe("plain7/naive", false, 8, || plain(7));
    probe("plain7/semi", true, 8, || plain(7));

    println!("--- ac (sub-multiset + rest splice) ---");
    probe("ac6/naive", false, 4, || ac_rules(6));
    probe("ac6/semi", true, 4, || ac_rules(6));
    probe("ac10/naive", false, 4, || ac_rules(10));
    probe("ac10/semi", true, 4, || ac_rules(10));

    println!("--- ac completion (cc = true, no rules) ---");
    for pairs in [32usize, 64] {
        probe(&format!("accompl{pairs}"), false, 1, || {
            (ac_completion(pairs), Vec::new())
        });
    }
}
