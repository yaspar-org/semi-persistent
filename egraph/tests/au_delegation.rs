// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The family where delegating to the exact solver pays, if one exists.
//!
//! Every family measured so far says it does not: the full configuration
//! returns bare search's answer for 3x to 8x the wall clock. Section (l) of the
//! anytime corpus explains why, and the explanation is a specification for the
//! family that would break the pattern.
//!
//! Delegation pays when the subproblem the rollout misjudges is small enough to
//! hand to the exact solver, inside an instance the exact solver cannot finish
//! whole. `blind` misjudges a subproblem but is milliseconds end to end;
//! `sat-decoy` puts the misjudgement at the root, where correcting it means
//! bounding the whole instance. Neither isolates a profitable delegation case.
//!
//! # The gadget
//!
//! One shallow pair whose ranking the action estimate gets wrong. The estimate
//! prices an action at `1 + sum over child pairs of (bs(left) + bs(right))`,
//! exact for a pair sharing no operator and pessimistic for one that factors
//! through shared structure. So:
//!
//! ```text
//!   winner    Wn(g(a), g(a)) against Wn(g(b), g(b))
//!             estimate 1 + 2*(2 + 2) = 9, true cost 1 + 2*3 = 7
//!             (both children are the same pair, solved once, charged twice)
//!   decoy     P(P(P(a))) against Q(Q(Q(b)))
//!             no shared operator, so estimate = truth = 4 + 4 = 8
//! ```
//!
//! The rollout compares 8 against 9 and takes the decoy; the truth is 7 against
//! 8. The gadget is three nodes deep, so the exact solver settles it in
//! microseconds, which is the property `sat-decoy`'s root arm lacked.
//!
//! # The host
//!
//! `n` gadgets hang off a spine above a `sat-ite` instance, so the search meets
//! `n` independent shallow misjudgements and then one subproblem the exact
//! solver cannot finish. Bare search has to sample its way out of each gadget;
//! delegation settles all of them in one pass and leaves the hard part alone.

use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::literal::NiraLitVal;

const GUARD: Duration = Duration::from_secs(30);

struct Instance {
    eg: EGraph31<NiraLitVal, false, false>,
    left: ENodeId,
    right: ENodeId,
}

/// The `sat-ite` host: two ITE encodings of one function in opposite guard
/// orders, which saturation merges and which makes the exact solver's alignment
/// space blow up. `gadgets` shallow misranked pairs hang above it.
fn build(k: usize, edits: usize, cap: usize, gadgets: usize) -> Instance {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;
    use semi_persistent_egraph::nodes::DefaultConfig;

    let leaves = 1usize << k;
    let mut decls =
        String::from("(datatype B (Ite B B B) (Not B) (W B B) (Wn B B) (Gw B) (Pd B) (Qd B)");
    for g in 0..k {
        decls.push_str(&format!(" (G{g})"));
    }
    for a in 0..leaves {
        decls.push_str(&format!(" (A{a})"));
    }
    let edited: Vec<usize> = (0..edits).map(|e| e * (leaves / edits.max(1))).collect();
    for &a in &edited {
        decls.push_str(&format!(" (B{a})"));
    }
    // Per-gadget atoms, so no two gadgets share structure and each is an
    // independent decision.
    for i in 0..gadgets {
        decls.push_str(&format!(" (Ga{i}) (Gb{i})"));
    }
    decls.push_str(")\n");

    let rules = "\
(rewrite (Ite (Not c) t e) (Ite c e t))\n\
(rewrite (Ite c (Ite c t u) e) (Ite c t e))\n\
(rewrite (Ite c t (Ite c u e)) (Ite c t e))\n\
(rewrite (Ite c1 (Ite c2 a b) (Ite c2 x y)) (Ite c2 (Ite c1 a x) (Ite c1 b y)))\n\
(rewrite (Not (Ite c t e)) (Ite c (Not t) (Not e)))\n";

    let asc: Vec<usize> = (0..k).collect();
    let desc: Vec<usize> = (0..k).rev().collect();
    let core_l = sat_ite_term(&asc, 0, 0, &[]);
    let core_r = sat_ite_term(&desc, 0, 0, &edited);

    let mut prog = format!("{decls}{rules}(let CL {core_l})\n(let CR {core_r})\n(run {cap})\n");

    // Each gadget's class holds both representations, so the search has to pick
    // one. The union is after saturation: no rule ever sees a gadget.
    for i in 0..gadgets {
        prog.push_str(&format!(
            "(let WL{i} (Wn (Gw (Ga{i})) (Gw (Ga{i}))))\n\
             (let WR{i} (Wn (Gw (Gb{i})) (Gw (Gb{i}))))\n\
             (let DL{i} (Pd (Pd (Pd (Ga{i})))))\n\
             (let DR{i} (Qd (Qd (Qd (Gb{i})))))\n\
             (union WL{i} DL{i})\n(union WR{i} DR{i})\n"
        ));
    }
    // The spine: every gadget sits above the hard core, so solving the instance
    // means solving all of them and then the core.
    let mut l = String::from("CL");
    let mut r = String::from("CR");
    for i in (0..gadgets).rev() {
        l = format!("(W WL{i} {l})");
        r = format!("(W WR{i} {r})");
    }
    prog.push_str(&format!("(let L {l})\n(let R {r})\n"));

    let cmds =
        semi_persistent_egraph::parser::parse_program_v2(&prog).expect("delegation program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("delegation program sortchecks");
    interp
        .run_checked(&checked)
        .expect("delegation program runs");
    let (left, _) = interp.global("L").expect("global L bound");
    let (right, _) = interp.global("R").expect("global R bound");
    Instance {
        eg: interp.eg,
        left,
        right,
    }
}

fn sat_ite_term(order: &[usize], prefix: usize, level: usize, edited: &[usize]) -> String {
    if level == order.len() {
        if edited.contains(&prefix) {
            format!("(B{prefix})")
        } else {
            format!("(A{prefix})")
        }
    } else {
        let g = order[level];
        let t = sat_ite_term(order, prefix | (1 << g), level + 1, edited);
        let e = sat_ite_term(order, prefix, level + 1, edited);
        format!("(Ite (G{g}) {t} {e})")
    }
}

fn run(inst: &Instance, playouts: u64, delegate: bool) -> (u32, f64) {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
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
            hybrid_exact: delegate,
            hybrid_threshold: if delegate { 4096 } else { 0 },
            rollout_hybrid: delegate,
            session_exact_memo: delegate,
            ..Default::default()
        },
    )
    .unwrap();
    (r.size, start.elapsed().as_secs_f64() * 1e3)
}

/// The gadget alone: the estimate misranks it, and the exact solver settles it
/// immediately.
///
/// Checked without the host, because if this does not hold the rest measures
/// nothing. With no gadgets the two configurations must agree, which is the
/// control.
#[test]
fn the_gadget_is_misranked_and_shallow() {
    let inst = build(2, 1, 6, 1);
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
    assert_eq!(exact.completion, Completion::Exact);
    let (greedy, _) = run(&inst, 1, false);
    assert!(
        greedy > exact.size,
        "the gadget must misrank at one playout: greedy {greedy}, optimum {}",
        exact.size
    );
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "a small host with one gadget must settle quickly"
    );
}

/// Delegation against bare search, at equal playouts and equal wall clock.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_delegation \
///   delegation_ladder -- --ignored --nocapture
/// ```
#[test]
#[ignore = "measurement run; prints the delegation comparison"]
fn delegation_ladder() {
    for &(k, edits, cap, gadgets) in &[
        (8usize, 2usize, 6usize, 0usize),
        (8, 2, 6, 4),
        (8, 2, 6, 8),
        (10, 2, 6, 8),
    ] {
        let inst = build(k, edits, cap, gadgets);
        println!(
            "\nk{k} e{edits} cap{cap} gadgets={gadgets}\n{:>9} | {:>8} {:>9} | {:>8} {:>9}",
            "playouts", "bare", "ms", "delegate", "ms"
        );
        for playouts in [1u64, 4, 16, 64, 256] {
            let (b, bms) = run(&inst, playouts, false);
            let (d, dms) = run(&inst, playouts, true);
            println!("{playouts:>9} | {b:>8} {bms:>9.1} | {d:>8} {dms:>9.1}");
        }
    }
}

/// Wall clock to reach a target value, laddering playouts. `None` if the ladder
/// runs out.
fn time_to_reach(inst: &Instance, target: u32, delegate: bool) -> Option<f64> {
    let mut playouts = 1u64;
    while playouts <= 1024 {
        let (size, ms) = run(inst, playouts, delegate);
        if size <= target {
            return Some(ms);
        }
        playouts *= 2;
    }
    None
}

/// **Delegation pays here, at equal wall clock.**
///
/// This is the case every other family failed to produce. The prediction was
/// that delegation pays when the misjudged subproblem is small enough to hand to
/// the exact solver, inside an instance the exact solver cannot finish whole,
/// and this family is built to that specification.
///
/// Measured at k = 10, two edits, eight gadgets: delegation returns the
/// best-known value at its first playout in about a millisecond, while bare
/// search needs sixty-four playouts and about seventeen to reach the same value.
/// The assertion is on time to equal quality, not on quality at equal playouts,
/// because the latter is the comparison that flattered delegation on every
/// earlier family.
#[test]
fn delegation_reaches_the_same_value_sooner() {
    let inst = build(10, 2, 6, 8);
    // The target is what both configurations converge to, so neither is being
    // asked to beat the other's ceiling.
    let (target, _) = run(&inst, 256, false);
    let bare = time_to_reach(&inst, target, false).expect("bare search reaches its own value");
    let delegated = time_to_reach(&inst, target, true).expect("delegation reaches it too");
    assert!(
        delegated < bare,
        "delegation must reach {target} sooner in wall clock: {delegated:.1} ms against \
         {bare:.1} ms"
    );
}

/// The control: with no gadgets, delegation buys nothing and costs time.
///
/// Without this the previous test could be measuring the machinery rather than
/// the gadgets, and the whole corpus record says delegation is a cost on
/// families that have no shallow misjudgement to correct.
#[test]
fn without_gadgets_delegation_only_costs() {
    let inst = build(8, 2, 6, 0);
    let (bare, bare_ms) = run(&inst, 16, false);
    let (delegated, del_ms) = run(&inst, 16, true);
    assert_eq!(
        bare, delegated,
        "with nothing shallow to correct, delegation must not change the answer"
    );
    assert!(
        del_ms > bare_ms,
        "and it must cost something: {del_ms:.1} ms against {bare_ms:.1} ms"
    );
}
