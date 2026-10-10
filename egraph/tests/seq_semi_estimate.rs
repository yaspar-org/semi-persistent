// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 2 of `doc/goal-semi-naive-sequence-rules.md`: the estimates that choose a
//! sequence rule's strategy for a round, against counts taken by brute force, and the
//! two decisions they must make (a delta equal to the full index chooses naive; a delta
//! of one node chooses the guard).

use semi_persistent_egraph::index::IndexStore;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::resolve::RAtom;
use semi_persistent_egraph::schedule::IndexStats;
use semi_persistent_egraph::sortcheck::CCommand;
use std::collections::BTreeSet;

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;
type Interp = Interpreter<Cfg, MachineLit, MachineModel, true, false>;
type G = semi_persistent_egraph::ENodeId;
type Rule = semi_persistent_egraph::collection::Rule<
    semi_persistent_egraph::OpId,
    semi_persistent_egraph::SortId,
    MachineLit,
>;

/// `n` conjunctions, one in ten with an `F` child, and the rule; the filter `gs` is not
/// required, so part 2 runs and naive assembles every conjunction.
///
/// No class is a child of more than one conjunction. `IndexStats`' `by_contains`
/// fan-out is the bucket a probe lands in, which is size-biased, so one class under
/// every conjunction would raise it to about `n` and make `q` (the fraction of
/// candidates expected to pass) 1 for any delta. The estimates are then pessimistic and
/// every round is naive, which is what `a_hub_class_chooses_semi_filter` tests.
fn program(n: usize) -> (Interp, Rule) {
    let mut src = String::from(
        "(sort E)\n(function a () E)\n(function b () E)\n(function F (E) E)\n(function K (E) E)\n\
         (function G (E) E)\n(function And (E) E :assoc-comm-idem)\n",
    );
    let mut leaf = String::from("(a)");
    for i in 0..n {
        leaf = format!("(K {leaf})");
        let child = if i % 10 == 0 {
            format!("(F {leaf})")
        } else {
            leaf.clone()
        };
        src.push_str(&format!("(let e{i} (And (G {leaf}) {child}))\n"));
    }
    src.push_str("(rewrite (And (..gs (F x)) ..rest) (And ..rest))\n");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let rule = checked
        .iter()
        .find_map(|c| match c {
            CCommand::CollectionRule(r) => Some((**r).clone()),
            _ => None,
        })
        .expect("a sequence rule");
    it.eg.rebuild();
    (it, rule)
}

/// The operator an atom scans, for the atoms that join.
fn atom_op(
    a: &RAtom<semi_persistent_egraph::OpId, semi_persistent_egraph::SortId, MachineLit>,
) -> Option<semi_persistent_egraph::OpId> {
    match a {
        RAtom::Plain { op, .. }
        | RAtom::Lit { op, .. }
        | RAtom::LitBind { op, .. }
        | RAtom::AExact { op, .. }
        | RAtom::APrefix { op, .. }
        | RAtom::ASuffix { op, .. }
        | RAtom::ABoth { op, .. }
        | RAtom::ACExact { op, .. }
        | RAtom::ACSub { op, .. }
        | RAtom::ACIExact { op, .. }
        | RAtom::ACISub { op, .. }
        | RAtom::Collect { op, .. } => Some(*op),
        _ => None,
    }
}

/// The guard estimate by brute force: per item sub-query, per join atom `di`, the least
/// over the join atoms of that atom's relation in variant `di`, counted node by node.
fn brute_guard(it: &Interp, rule: &Rule, delta: &BTreeSet<usize>) -> usize {
    let Some(RAtom::Collect { collect, .. }) = rule.query.atoms.first() else {
        panic!("a Collect atom")
    };
    let live = |n: G| it.eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED == 0;
    let count = |op, in_delta: Option<bool>| {
        it.eg
            .node_ids()
            .filter(|&n| live(n) && it.eg.node_op(n) == op)
            .filter(|n| match in_delta {
                None => true,
                Some(want) => delta.contains(&n.to_usize()) == want,
            })
            .count()
    };
    let mut total = 0;
    for sq in collect.0.filters.iter().chain(&collect.0.ones) {
        if sq.every_class {
            continue;
        }
        let joins: Vec<(usize, semi_persistent_egraph::OpId)> = sq
            .query
            .atoms
            .iter()
            .enumerate()
            .filter_map(|(j, a)| atom_op(a).map(|o| (j, o)))
            .collect();
        for &(di, _) in &joins {
            let least = joins
                .iter()
                .map(|&(j, op)| match j.cmp(&di) {
                    std::cmp::Ordering::Equal => count(op, Some(true)),
                    std::cmp::Ordering::Less => count(op, Some(false)),
                    std::cmp::Ordering::Greater => count(op, None),
                })
                .min()
                .unwrap_or(0);
            total += least + semi_persistent_egraph::seq_engine::GUARD_SETUP;
        }
    }
    total
}

#[test]
fn estimates_equal_brute_force_counts() {
    let (it, rule) = program(50);
    let full = IndexStore::build(&it.eg);
    let stats = IndexStats::from_index(&full);
    let ids: Vec<G> = it.eg.node_ids().collect();
    // Deltas of increasing size: none, the first F node, a quarter, and every node.
    let f = it.eg.op("F").expect("F");
    let first_f = ids
        .iter()
        .copied()
        .find(|&n| it.eg.node_op(n) == f)
        .expect("an F node");
    let quarter: Vec<G> = ids.iter().copied().step_by(4).collect();
    for touched in [vec![], vec![first_f], quarter, ids.clone()] {
        let delta = IndexStore::build_delta(&it.eg, &touched);
        let est = semi_persistent_egraph::seq_engine::semi_estimate(&rule, &full, &delta, &stats)
            .expect("an estimate");
        let set: BTreeSet<usize> = touched.iter().map(|n| n.to_usize()).collect();
        assert_eq!(
            est.guard,
            brute_guard(&it, &rule, &set),
            "guard, delta of {}",
            touched.len()
        );
        let and = rule.root_op();
        let count = |pred: &dyn Fn(G) -> bool| {
            it.eg
                .node_ids()
                .filter(|&n| it.eg.node_op(n) == and && pred(n))
                .count()
        };
        assert_eq!(est.nodes, count(&|_| true));
        assert_eq!(est.delta_nodes, count(&|n| set.contains(&n.to_usize())));
        // The filter is not required, so part 2 runs and naive assembles every node.
        assert_eq!(est.naive_assembly, est.nodes);
    }
    // fan(A): the bucket lengths equal the variadic parents counted node by node
    // (`by_contains` indexes variadic nodes only; here, the root `And`).
    let and = rule.root_op();
    let classes: Vec<G> = ids
        .iter()
        .map(|&n| it.eg.find_const(n))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    for &c in &classes {
        let parents = it
            .eg
            .node_ids()
            .filter(|&p| it.eg.node_op(p) == and)
            .filter(|&p| {
                let mut has = false;
                it.eg
                    .for_each_child(p, |k, _| has |= it.eg.find_const(k) == c);
                has
            })
            .count();
        assert_eq!(
            semi_persistent_egraph::seq_engine::fan_out(&full, std::iter::once(c)),
            parents,
            "fan-out of class {}",
            c.to_usize()
        );
    }
}

/// A delta equal to the full index: every candidate is expected to pass the test, so
/// the guard can save nothing and the round is naive.
#[test]
fn a_full_delta_chooses_naive() {
    let (it, rule) = program(50);
    let full = IndexStore::build(&it.eg);
    let stats = IndexStats::from_index(&full);
    let all: Vec<G> = it.eg.node_ids().collect();
    let delta = IndexStore::build_delta(&it.eg, &all);
    let est = semi_persistent_egraph::seq_engine::semi_estimate(&rule, &full, &delta, &stats)
        .expect("an estimate");
    assert_eq!(est.saving, 0, "{est:?}");
    assert!(!est.guard_pays(), "{est:?}");
}

/// A delta of one `F` node: the guard costs one row, and nearly every conjunction is
/// expected to be skipped, so the guard pays.
#[test]
fn a_one_node_delta_chooses_the_guard() {
    let (it, rule) = program(50);
    let full = IndexStore::build(&it.eg);
    let stats = IndexStats::from_index(&full);
    let f = it.eg.op("F").expect("F");
    let one: Vec<G> = it
        .eg
        .node_ids()
        .filter(|&n| it.eg.node_op(n) == f)
        .take(1)
        .collect();
    let delta = IndexStore::build_delta(&it.eg, &one);
    let est = semi_persistent_egraph::seq_engine::semi_estimate(&rule, &full, &delta, &stats)
        .expect("an estimate");
    // One delta row, plus the fixed cost `semi_estimate` charges per variant.
    assert_eq!(
        est.guard,
        1 + semi_persistent_egraph::seq_engine::GUARD_SETUP,
        "{est:?}"
    );
    assert!(est.guard_pays(), "{est:?}");
}

/// The round's delta after subsuming `node`, as the saturation driver gives it.
fn subsume_round(it: &mut Interp, node: G) -> (Vec<G>, Vec<G>) {
    it.eg.clear_touched();
    it.eg.set_track_merge_members(true);
    it.eg.subsume(node);
    it.eg.rebuild();
    it.eg.set_track_merge_members(false);
    let mut touched: Vec<G> = it.eg.touched().to_vec();
    touched.sort_unstable();
    touched.dedup();
    let subsumed: Vec<G> = touched
        .iter()
        .copied()
        .filter(|&n| it.eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED != 0)
        .collect();
    (touched, subsumed)
}

/// Step 4's hub case: one class with 10^4 conjunction parents and one subsumed row.
/// Every parent must be reassembled, so listing them is no cheaper than naive. The
/// bucket length and the probe's mean fan-out are read, never walked, and send the round
/// away from semi-enumerate; its work stays within twice naive's.
#[test]
fn a_hub_class_chooses_semi_filter() {
    let n = 10_000;
    let mut src = String::from(
        "(sort E)\n(function a () E)\n(function b () E)\n(function F (E) E)\n(function K (E) E)\n\
         (function And (E) E :assoc-comm-idem)\n(let k0 (b))\n(let hub (F (a)))\n",
    );
    for i in 1..=n {
        src.push_str(&format!(
            "(let k{i} (K k{}))\n(let e{i} (And hub k{i}))\n",
            i - 1
        ));
    }
    src.push_str("(rewrite (And (..gs (F x)) ..rest) (And ..rest))\n");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let rule = checked
        .iter()
        .find_map(|c| match c {
            CCommand::CollectionRule(r) => Some((**r).clone()),
            _ => None,
        })
        .expect("a sequence rule");
    it.eg.rebuild();
    let f = it.eg.op("F").expect("F");
    let hub = it
        .eg
        .node_ids()
        .find(|&x| it.eg.node_op(x) == f)
        .expect("the F node");
    let (touched, subsumed) = subsume_round(&mut it, hub);
    assert_eq!(subsumed, vec![hub]);
    let full = IndexStore::build(&it.eg);
    let delta = IndexStore::build_delta(&it.eg, &touched);
    let rd = semi_persistent_egraph::saturate::RoundDelta {
        index: &delta,
        touched: &touched,
        subsumed: &subsumed,
    };
    let (choice, semi, naive) =
        semi_persistent_egraph::seq_engine::semi_choice(&rule, &it.eg, &full, &rd, it.globals());
    eprintln!("hub: {choice}, {semi} match steps against naive's {naive}");
    // The hub's parents are never listed: with the guard's per-variant cost charged
    // (`GUARD_SETUP`), the estimate declines the guard altogether here, which costs
    // naive's work exactly. Semi-filter would also be admissible, within twice naive.
    assert_ne!(choice, "enumerate");
    assert!(semi <= naive.saturating_mul(2), "{semi} > 2 × {naive}");
}

/// A delta of one new conjunction among 50: semi-enumerate lists it alone.
#[test]
fn a_small_delta_chooses_semi_enumerate() {
    let (mut it, rule) = program(50);
    it.eg.clear_touched();
    it.eg.set_track_merge_members(true);
    let src = "(let fresh (And (F (b)) (a)))\n";
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    it.eg.rebuild();
    it.eg.set_track_merge_members(false);
    let mut touched: Vec<G> = it.eg.touched().to_vec();
    touched.sort_unstable();
    touched.dedup();
    let full = IndexStore::build(&it.eg);
    let delta = IndexStore::build_delta(&it.eg, &touched);
    let rd = semi_persistent_egraph::saturate::RoundDelta {
        index: &delta,
        touched: &touched,
        subsumed: &[],
    };
    let (choice, semi, naive) =
        semi_persistent_egraph::seq_engine::semi_choice(&rule, &it.eg, &full, &rd, it.globals());
    eprintln!("small delta: {choice}, {semi} match steps against naive's {naive}");
    assert_eq!(choice, "enumerate");
    assert!(semi < naive, "{semi} >= {naive}");
}

/// Step 5: two rules whose filters share one base run its free-root plan once per
/// round. 50 conjunctions with 5 `F` children make the filter drive the cost model's
/// choice, so each rule's drive lists the base's rows.
#[test]
fn two_rules_on_one_base_share_its_rows() {
    let mut src = String::from(
        "(sort E)\n(function a () E)\n(function b () E)\n(function F (E) E)\n(function K (E) E)\n\
         (function And (E) E :assoc-comm-idem)\n",
    );
    let mut leaf = String::from("(a)");
    for i in 0..50 {
        leaf = format!("(K {leaf})");
        let child = if i % 10 == 0 {
            format!("(F {leaf})")
        } else {
            leaf.clone()
        };
        src.push_str(&format!("(let e{i} (And (b) {child}))\n"));
    }
    src.push_str("(rewrite (And (..gs (F x)) ..rest) (And ..rest))\n");
    src.push_str("(rewrite (And (..hs (F y)) ..more) (And ..hs))\n");
    src.push_str("(run 1)\n");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    let before = semi_persistent_egraph::seq_engine::free_row_runs();
    it.run_checked(&checked).expect("run");
    let runs = semi_persistent_egraph::seq_engine::free_row_runs() - before;
    assert_eq!(
        runs, 1,
        "the shared base's free-root plan ran {runs} times in one round"
    );
}
