// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! How the interpreter reports an abstract conflict (abstract-engine-task.md §5, §6).
//!
//! The acceptance programs in `tests/egg/abs-engine/` need the `refine` syntax
//! (#145) and the domain registry (#148). Until both land, these tests install
//! a stand-in interval domain and seed values directly, then run ordinary
//! commands through `run_checked`.

use super::{InterpError, Interpreter};
use crate::egraph::abs_sched::AbsDomain;
use crate::model::{BignumLit, BignumModel};
use crate::nodes::DefaultConfig;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;
type Globals = crate::resolve::GlobalCtx<<DefaultConfig as crate::config::EGraphConfig>::S>;

const TOP: u64 = u64::MAX;

fn interval(lo: i32, hi: i32) -> u64 {
    ((lo as u32 as u64) << 32) | (hi as u32 as u64)
}

/// Intervals over one sort. Only the meet matters here: no operator has a transfer.
struct Interval {
    sort: usize,
}

impl AbsDomain for Interval {
    fn analysed_sort(&self, sort: usize) -> bool {
        sort == self.sort
    }
    fn top(&self, _sort: usize) -> u64 {
        TOP
    }
    fn meet(&self, a: u64, b: u64) -> Option<u64> {
        if a == TOP {
            return Some(b);
        }
        if b == TOP {
            return Some(a);
        }
        let (alo, ahi) = ((a >> 32) as u32 as i32, a as u32 as i32);
        let (blo, bhi) = ((b >> 32) as u32 as i32, b as u32 as i32);
        let (lo, hi) = (alo.max(blo), ahi.min(bhi));
        (lo <= hi).then(|| interval(lo, hi))
    }
    fn forward(&self, _op: usize, _args: &[u64]) -> u64 {
        TOP
    }
    fn backward(&self, _op: usize, _result: u64, _args: &[u64]) -> Option<Vec<u64>> {
        None
    }
}

/// Parses, sortchecks and runs `src` on `interp`, keeping `globals` across calls.
fn exec(interp: &mut Interp, globals: &mut Globals, src: &str) -> Result<(), InterpError> {
    let cmds = crate::parser::parse_program_v2(src).expect("parse");
    let checked = crate::sortcheck::sortcheck_program(cmds, &mut interp.eg, &interp.model, globals)
        .expect("sortcheck");
    interp.run_checked(&checked)
}

/// Declares `a = (A)` and `b = (B)` of sort `S`, followed by `decls`, then installs the interval domain on `S` and seeds `a` with [0, 4]
/// and `b` with [10, 20], so any merge of the two is an empty meet.
fn disjoint_pair(decls: &str) -> (Interp, Globals) {
    let mut interp = Interp::new(BignumModel);
    let mut globals = Globals::new();
    let src =
        format!("(sort S) (function A () S) (function B () S) (let a (A)) (let b (B)) {decls}");
    exec(&mut interp, &mut globals, &src).expect("declarations");
    let sort = interp.eg.intern_sort("S").to_usize();
    interp.eg.set_abs_domain(Box::new(Interval { sort }));
    let a = interp.global_class("a").expect("a");
    let b = interp.global_class("b").expect("b");
    interp.eg.abs_seed(a, interval(0, 4));
    interp.eg.abs_seed(b, interval(10, 20));
    assert!(!interp.eg.abs_has_conflict());
    (interp, globals)
}

fn assert_abs_conflict(r: Result<(), InterpError>) {
    match r {
        Err(e @ InterpError::AbsConflict(_)) => {
            assert!(e.to_string().contains("abstract conflict"), "message: {e}");
        }
        other => panic!("expected an abstract conflict, got {other:?}"),
    }
}

#[test]
fn union_of_disjoint_values_is_an_abstract_conflict() {
    let (mut interp, mut globals) = disjoint_pair("");
    assert_abs_conflict(exec(&mut interp, &mut globals, "(union a b)"));
    // Reported once: the flag is taken, not left for the next command.
    assert!(!interp.eg.abs_has_conflict());
}

#[test]
fn overlapping_values_merge_without_a_conflict() {
    let mut interp = Interp::new(BignumModel);
    let mut globals = Globals::new();
    exec(
        &mut interp,
        &mut globals,
        "(sort S) (function A () S) (function B () S) (let a (A)) (let b (B))",
    )
    .expect("declarations");
    let sort = interp.eg.intern_sort("S").to_usize();
    interp.eg.set_abs_domain(Box::new(Interval { sort }));
    let a = interp.global_class("a").expect("a");
    let b = interp.global_class("b").expect("b");
    interp.eg.abs_seed(a, interval(0, 9));
    interp.eg.abs_seed(b, interval(5, 20));
    exec(&mut interp, &mut globals, "(union a b) (check-eq a b)").expect("no conflict");
    assert_eq!(interp.eg.abs_value(a), Some(interval(5, 9)));
}

/// A rule that merges the pair stops the run on the conflict, at the rebuild after
/// the round that met it. The run's own fault is a placeholder; the interpreter
/// reports the conflict in its place.
#[test]
fn a_run_stops_on_a_conflict_and_reports_it() {
    // `(N k)` gains a node every round, so the node count shows how many rounds ran.
    let decls = "(function N (IBig) S) (rewrite (A) (B)) (rewrite (N k) (N (IBig::+ k 1))) \
                 (let n (N 0))";
    let (mut interp, mut globals) = disjoint_pair(decls);
    assert_abs_conflict(exec(&mut interp, &mut globals, "(run 5)"));

    // The same program without a domain, run for the one round the conflict allows.
    let mut control = Interp::new(BignumModel);
    let mut control_globals = Globals::new();
    let src = format!(
        "(sort S) (function A () S) (function B () S) (let a (A)) (let b (B)) {decls} (run 1)"
    );
    exec(&mut control, &mut control_globals, &src).expect("control run");
    assert_eq!(
        interp.eg.len(),
        control.eg.len(),
        "the run went past the conflict"
    );
}

/// The merge happens only inside the lazy check's transaction (phase 2 runs the
/// rule there). Restore would reset the flag, so the conflict must be taken first;
/// the transaction is still discarded afterwards.
#[test]
fn a_conflict_inside_the_lazy_check_is_reported_before_the_transaction_closes() {
    let (mut interp, mut globals) =
        disjoint_pair("(set-option :check-completion on) (rewrite (A) (B))");
    assert_abs_conflict(exec(&mut interp, &mut globals, "(check-eq a b)"));
    assert!(!interp.eg.abs_has_conflict());
    // The rule's merge was made inside the transaction and rolled back with it.
    let a = interp.global_class("a").expect("a");
    let b = interp.global_class("b").expect("b");
    assert_ne!(interp.eg.find(a), interp.eg.find(b));
}
