// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-naive matching of sequence rules (task 6 of
//! `doc/goal-flatten-and-engine-completion.md`): coverage of `Δ_collect`.
//!
//! A program is run to a snapshot `t0`, where every root node's matches are taken. The
//! touched log is cleared, the graph is changed (merges, new nodes, subsumptions, and,
//! for `:flatten` rules, nesting), and rebuilt to `t1`. `seq_engine::delta_nodes` then
//! gives `Δ_collect` from the round's delta, as the saturation driver computes it. The
//! coverage property: a root node outside `Δ_collect` has no match at `t1` that it did
//! not have at `t0` (classes compared through the union-find at `t1`). Semi-naive
//! assembles only the nodes of `Δ_collect`, so together with the earlier rounds'
//! matches it then has every match naive matching finds.

use semi_persistent_egraph::DenseId;
use semi_persistent_egraph::index::IndexStore;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::sortcheck::CCommand;
use std::collections::{BTreeMap, BTreeSet};

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;
type Interp = Interpreter<Cfg, MachineLit, MachineModel, true, false>;
type G = semi_persistent_egraph::ENodeId;
type Rule = semi_persistent_egraph::collection::Rule<
    semi_persistent_egraph::OpId,
    semi_persistent_egraph::SortId,
    MachineLit,
>;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

const DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function K (E E) E)
(function P0 () E)
(function P1 () E)
(function And (E) E :assoc-comm-idem)
(function Plus (E) E :assoc-comm)
(function Cat (E) E :assoc)
(let ga a)
";

const TERMS: &[&str] = &[
    "(a)",
    "(b)",
    "(c)",
    "(F (a))",
    "(F (b))",
    "(G (a))",
    "(G (F (a)))",
    "(K (a) (b))",
    "(K (b) (b))",
];

/// Run `src`'s commands in `it`, keeping the global context `sg`.
fn run(
    it: &mut Interp,
    sg: &mut semi_persistent_egraph::resolve::GlobalCtx<semi_persistent_egraph::SortId>,
    src: &str,
) -> Vec<CCommand<semi_persistent_egraph::OpId, semi_persistent_egraph::SortId, MachineLit>> {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src)
        .unwrap_or_else(|e| panic!("parse: {e}\n{src}"));
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, sg)
            .unwrap_or_else(|e| panic!("sortcheck: {e}\n{src}"));
    it.run_checked(&checked)
        .unwrap_or_else(|e| panic!("run: {e}\n{src}"));
    checked
}

/// Every root node's matches, rendered by `seq_engine::matches_at`.
fn snapshot(it: &Interp, rule: &Rule) -> BTreeMap<usize, BTreeSet<String>> {
    let mut out = BTreeMap::new();
    for n in it.eg.node_ids() {
        if it.eg.node_op(n) != rule.root_op()
            || it.eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED != 0
        {
            continue;
        }
        let ms = semi_persistent_egraph::seq_engine::matches_at(&it.eg, it.globals(), rule, n);
        out.insert(
            n.to_usize(),
            ms.into_iter().map(|m| format!("{m:?}")).collect(),
        );
    }
    out
}

/// A rendered match with every class `c<id>` replaced by its class at `t1`.
fn remap(it: &Interp, m: &str) -> String {
    let mut out = String::new();
    let mut chars = m.chars().peekable();
    while let Some(ch) = chars.next() {
        out.push(ch);
        if ch == 'c'
            && out.len() >= 2
            && !out[..out.len() - 1].ends_with(|p: char| p.is_alphanumeric())
        {
            let mut digits = String::new();
            while let Some(d) = chars.peek().copied().filter(|d| d.is_ascii_digit()) {
                digits.push(d);
                chars.next();
            }
            if digits.is_empty() {
                continue;
            }
            let id: usize = digits.parse().expect("an id");
            let g = G::from_usize(id);
            out.push_str(&it.eg.find_const(g).to_usize().to_string());
        }
    }
    out
}

/// The nodes naive offered and semi-filter assembled, over every `check`: the
/// equivalence must not hold vacuously.
static SEMI_OFFERED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static SEMI_ASSEMBLED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Check coverage from `t0` to `t1` for one program and change. Returns the root nodes
/// whose matches changed and the nodes of `Δ_collect` (`None` on the naive fallback).
fn check(
    prog: &str,
    pre: impl FnOnce(&mut Interp),
    change: &str,
    mutate: impl FnOnce(&mut Interp),
) -> (Vec<usize>, Option<Vec<usize>>) {
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = run(&mut it, &mut sg, prog);
    let rule = checked
        .iter()
        .find_map(|c| match c {
            CCommand::CollectionRule(r) => Some(r.clone()),
            _ => None,
        })
        .expect("a sequence rule");
    pre(&mut it);
    it.eg.rebuild();
    let before = snapshot(&it, &rule);
    it.eg.clear_touched();
    // As inside a semi-naive run: merges log their absorbed members.
    it.eg.set_track_merge_members(true);
    if !change.is_empty() {
        run(&mut it, &mut sg, change);
    }
    mutate(&mut it);
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
    let full = IndexStore::build(&it.eg);
    let delta = IndexStore::build_delta(&it.eg, &touched);
    let rd = semi_persistent_egraph::saturate::RoundDelta {
        index: &delta,
        touched: &touched,
        subsumed: &subsumed,
    };
    let mut pool = semi_persistent_egraph::ematch::MatchPool::new();
    let dn = semi_persistent_egraph::seq_engine::delta_nodes(
        &rule,
        &it.eg,
        &full,
        &rd,
        it.globals(),
        &mut pool,
    )
    .map(|v| v.iter().map(|n| n.to_usize()).collect::<Vec<_>>());
    // Semi-filter (step 3 of `doc/goal-semi-naive-sequence-rules.md`) assembles exactly
    // the nodes of `Δ_collect` among those naive's query offers.
    let trace = semi_persistent_egraph::seq_engine::semi_trace(
        &rule,
        &it.eg,
        &full,
        &rd,
        it.globals(),
        false,
    );
    // Semi-enumerate (step 4) assembles the same nodes with the same matches, from the
    // root drive and probed rows.
    let listed = semi_persistent_egraph::seq_engine::semi_trace(
        &rule,
        &it.eg,
        &full,
        &rd,
        it.globals(),
        true,
    );
    match (&trace, &listed) {
        (Some((_, a1, m1)), Some((_, a2, m2))) => {
            let (mut a1, mut a2) = (a1.clone(), a2.clone());
            a1.sort_unstable();
            a2.sort_unstable();
            assert_eq!(
                a1, a2,
                "semi-enumerate's nodes differ from semi-filter's\n{prog}\nchange:\n{change}"
            );
            assert_eq!(
                m1, m2,
                "semi-enumerate's matches differ from semi-filter's\n{prog}\nchange:\n{change}"
            );
        }
        (None, None) => {}
        _ => panic!("semi-enumerate and semi-filter disagree on the fallback"),
    }
    assert_eq!(
        trace.is_some(),
        dn.is_some(),
        "semi-filter and Δ_collect disagree on the fallback"
    );
    if let (Some((offered, assembled, _)), Some(d)) = (&trace, &dn) {
        let d: BTreeSet<usize> = d.iter().copied().collect();
        let mut want: Vec<usize> = offered
            .iter()
            .map(|n| n.to_usize())
            .filter(|n| d.contains(n))
            .collect();
        let mut got: Vec<usize> = assembled.iter().map(|n| n.to_usize()).collect();
        want.sort_unstable();
        got.sort_unstable();
        assert_eq!(
            got, want,
            "semi-filter's nodes are not Δ_collect ∩ naive's\n{prog}\nchange:\n{change}"
        );
        SEMI_OFFERED.fetch_add(offered.len(), std::sync::atomic::Ordering::Relaxed);
        SEMI_ASSEMBLED.fetch_add(got.len(), std::sync::atomic::Ordering::Relaxed);
    }
    let after = snapshot(&it, &rule);
    let mut changed = Vec::new();
    for (n, ms) in &after {
        let old: BTreeSet<String> = before
            .get(n)
            .map(|s| s.iter().map(|m| remap(&it, m)).collect())
            .unwrap_or_default();
        let new_matches: Vec<&String> = ms.iter().filter(|m| !old.contains(*m)).collect();
        if !new_matches.is_empty() || !before.contains_key(n) {
            changed.push(*n);
        }
        if let Some(d) = &dn {
            assert!(
                new_matches.is_empty() || d.contains(n),
                "node {n} has new matches {new_matches:?} and is not in Δ_collect {d:?}\n{prog}\nchange:\n{change}"
            );
        }
    }
    (changed, dn)
}

/// Random programs: untagged and `:flatten` rules over ACI, AC, and A roots; changes by
/// merges, new nodes, subsumptions, and (under `:flatten`) nesting.
#[test]
fn delta_collect_covers_every_new_match() {
    let mut rng = Rng(0x5e41_c0de);
    let (mut cases, mut changed_nodes, mut fallbacks, mut delta_sizes, mut roots) = (0, 0, 0, 0, 0);
    for _ in 0..400 {
        let op = *rng.pick(&["And", "Plus", "Cat"]);
        let flatten = rng.below(2) == 0;
        let mut prog = String::from(DECLS);
        prog.push_str("(let p0 (P0))\n(let p1 (P1))\n");
        let node = |rng: &mut Rng| {
            let k = 2 + rng.below(3);
            let kids: Vec<String> = (0..k)
                .map(|_| {
                    if rng.below(4) == 0 {
                        format!("p{}", rng.below(2))
                    } else {
                        rng.pick(TERMS).to_string()
                    }
                })
                .collect();
            format!("({op} {})", kids.join(" "))
        };
        for t in 0..4 {
            let n = node(&mut rng);
            prog.push_str(&format!("(let e{t} {n})\n"));
        }
        let base = *rng.pick(&["(F x0)", "(G x0)", "(K x0 y0)", "(F ga)"]);
        // `:except` is an AC and ACI construct.
        let except = if op != "Cat" && rng.below(3) == 0 {
            " (..g1 (G z1) :except g0)"
        } else {
            ""
        };
        let rest = if rng.below(2) == 0 { " ..rest" } else { "" };
        let tag = if flatten { " :flatten" } else { "" };
        prog.push_str(&format!(
            "(rewrite ({op} (..g0 {base}){except}{rest}) ({op} ..g0){tag})\n"
        ));
        let mut change = String::new();
        for _ in 0..rng.below(4) {
            match rng.below(4) {
                0 => change.push_str(&format!(
                    "(union {} {})\n",
                    rng.pick(TERMS),
                    rng.pick(TERMS)
                )),
                1 => {
                    let n = node(&mut rng);
                    change.push_str(&format!("(let n{} {n})\n", rng.next() % 1000));
                }
                2 => change.push_str(&format!("(union p{} {})\n", rng.below(2), node(&mut rng))),
                _ => change.push_str(&format!("(union p{} {})\n", rng.below(2), rng.pick(TERMS))),
            }
        }
        let subsume = rng.below(3) == 0;
        let pick = rng.next();
        let (changed, dn) = check(
            &prog,
            |_| {},
            &change,
            |it| {
                if subsume {
                    // Subsume one base-operator node: a filter row may disappear.
                    let fs: Vec<G> = it
                        .eg
                        .node_ids()
                        .filter(|&n| matches!(it.eg.node_op_name(n), "F" | "G" | "K"))
                        .collect();
                    if !fs.is_empty() {
                        it.eg.subsume(fs[(pick % fs.len() as u64) as usize]);
                    }
                }
            },
        );
        cases += 1;
        changed_nodes += changed.len();
        // A base naming the global `ga` needs the naive path (`needs_naive_match`);
        // nothing else may fall back, since the default fraction never triggers.
        match dn {
            None => {
                assert!(base.contains("ga"), "an unexpected naive fallback:\n{prog}");
                fallbacks += 1;
            }
            Some(d) => delta_sizes += d.len(),
        }
        roots += 1;
    }
    eprintln!(
        "coverage: {cases} programs, {changed_nodes} root nodes with new matches, {fallbacks} naive fallbacks, \
         Δ_collect total {delta_sizes} over {roots} rounds"
    );
    assert!(
        changed_nodes > 200,
        "too few changed nodes to test coverage: {changed_nodes}"
    );
    assert!(fallbacks < cases, "every program fell back: {fallbacks}");
    let offered = SEMI_OFFERED.load(std::sync::atomic::Ordering::Relaxed);
    let assembled = SEMI_ASSEMBLED.load(std::sync::atomic::Ordering::Relaxed);
    eprintln!("semi-filter: {assembled} of {offered} offered nodes assembled");
    assert!(
        0 < assembled && assembled < offered,
        "semi-filter's equivalence is vacuous: {assembled} of {offered}"
    );
}

/// One program per cause of a new match. Each asserts that the cause did change the
/// root's matches (or the test proves nothing), that the root is in `Δ_collect`, and
/// coverage at every other node.
#[test]
fn delta_collect_each_cause() {
    let cases: &[(&str, &str, &str, bool)] = &[
        // A new root node.
        (
            "new root",
            "(rewrite (And (..g0 (F x0)) ..rest) (And ..g0))",
            "(let e1 (And (F (b)) (c)))",
            false,
        ),
        // A child class gains a member matching the filter (a new row).
        (
            "new row by merge",
            "(rewrite (And (..g0 (F x0)) ..rest) (And ..g0))",
            "(union (c) (F (b)))",
            false,
        ),
        // A row's sub-term changes below the root of the row: (F (G y)) gains a G child.
        (
            "new row two levels down",
            "(rewrite (And (..g0 (F (G y0))) ..rest) (And ..g0))",
            "(union (a) (G (b)))",
            false,
        ),
        // A new row of an excepted filter moves a child out of the other filter.
        (
            "excepted filter",
            "(rewrite (And (..g0 (F x0)) (..g1 (F (b)) :except g0) ..rest) (And ..g1))",
            "(union (c) (F (b)))",
            false,
        ),
        // Under `:flatten`, a child class becomes nested during the round.
        (
            "nesting",
            "(rewrite (And (..g0 (F x0)) ..rest) (And ..g0) :flatten)",
            "(union p0 (And (F (b)) (b)))",
            false,
        ),
        // (A former cause, a class of conjunctions only that gains another member and so
        // becomes keepable whole, no longer exists: under the demand rule of
        // `doc/goal-canonical-flatten-views.md` any class may be kept whole, so a member
        // of another operator changes no view.)
        // A subsumed node removes a row; with `:except`, the excepted filter gains it.
        (
            "subsumption",
            "(rewrite (And (..g0 (F (a))) (..g1 (F x1) :except g0) ..rest) (And ..g1))",
            "",
            true,
        ),
    ];
    for (name, rule, change, subsume) in cases {
        let mut prog = String::from(DECLS);
        prog.push_str("(function Q0 () E)\n(let p0 (P0))\n(let q0 (Q0))\n");
        prog.push_str("(let e0 (And (F (a)) (G (a)) p0 q0))\n");
        prog.push_str("(union q0 (And (F (a)) (c)))\n");
        prog.push_str(rule);
        prog.push('\n');
        let keepable = *name == "keepable";
        let (changed, dn) = check(
            &prog,
            |it| {
                // `q0`'s placeholder leaves it: its only matchable member is then the
                // conjunction, so it is opened and never kept whole.
                if keepable {
                    let q = it
                        .eg
                        .node_ids()
                        .find(|&n| it.eg.node_op_name(n) == "Q0")
                        .expect("Q0");
                    it.eg.subsume(q);
                }
            },
            change,
            |it| {
                if *subsume {
                    let f = it
                        .eg
                        .node_ids()
                        .find(|&n| {
                            it.eg.node_op_name(n) == "F"
                                && it.eg.node_ids().any(|m| {
                                    it.eg.node_op_name(m) == "a"
                                        && it.eg.find_const(m)
                                            == it.eg.find_const(it.eg.child_at(n, 0))
                                })
                        })
                        .expect("(F (a))");
                    it.eg.subsume(f);
                }
            },
        );
        let dn = dn.unwrap_or_else(|| panic!("{name}: the naive fallback hides the cause"));
        assert!(
            !changed.is_empty(),
            "{name}: the change did not change any root's matches"
        );
        for n in &changed {
            assert!(
                dn.contains(n),
                "{name}: node {n} changed and is not in Δ_collect {dn:?}"
            );
        }
    }
}
