// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anti-unification on a synthetic auto-formalization corpus.
//!
//! The application claim behind the solver is that when several formalizations
//! of one natural-language statement differ in inessential ways, anti-unifying
//! them recovers the stable core and marks exactly where they genuinely differ.
//! Every other family in the corpus is structural and says nothing about that
//! claim. This one is shaped like the application while keeping ground truth:
//! the changes are planted, so the oracle is known by construction.
//!
//! One statement family, parameterized by size. Informally, for `n` conditions:
//!
//! ```text
//!   "A registration is permitted when the applicant is enrolled, has
//!    cleared prerequisite 1 ... prerequisite n, and is not flagged."
//! ```
//!
//! Two candidate formalizations of it are built as two terms in one e-graph,
//! the way two formalizers would render the same sentence. They differ in three
//! separable ways, and separating them is the point:
//!
//! | class of difference | recovered by | reported as |
//! | --- | --- | --- |
//! | conjunct order, repeated conjunct | canonization (ACI) | absorbed |
//! | a condition replaced by another | the search | `Variants` nodes |
//! | negation pushed over a disjunction | saturation, then the search | absorbed only with rules |
//!
//! The first class costs nothing: with `And` declared `:assoc-comm-idem`, a
//! reordered and duplicated conjunction is the same e-node, so the two
//! formalizations land in one class and the anti-unifier is the whole term.
//! Reporting it separately is what stops a run from claiming the search
//! recovered variability that canonization had already erased.
//!
//! The second class is the oracle. Planting `k` replaced conditions means the
//! optimal anti-unifier generalizes exactly those `k` positions, so
//! `variants == k` is a check, not a measurement.
//!
//! The third class is the one that needs an e-graph rather than two terms.
//! One formalizer writes `Not(Or(a, b))` and the other `And(Not(a), Not(b))`.
//! As terms these share no structure at that position and anti-unification must
//! generalize it, paying both sides. Saturating De Morgan first puts them in one
//! class, and the same search then recovers the position. The measurement is the
//! same pair of formalizations with the rules off and on.

use std::time::Duration;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::terms::TermOp;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::DefaultConfig;

const GUARD: Duration = Duration::from_secs(60);

struct Case {
    eg: EGraph31<NiraLitVal, false, false>,
    left: ENodeId,
    right: ENodeId,
    /// Conditions replaced in the second formalization: the number of
    /// positions the optimal anti-unifier must generalize.
    planted: usize,
}

/// The natural-language statement this size stands for. Kept next to the
/// formalizations because the corpus is only meaningful as a pair of renderings
/// of one sentence, and a reader has to be able to see the sentence.
fn statement(n: usize) -> String {
    let mut s = String::from(
        "A registration is permitted when the applicant is enrolled, has cleared prerequisite 1",
    );
    for i in 2..=n {
        s.push_str(&format!(", prerequisite {i}"));
    }
    s.push_str(", and is not flagged.");
    s
}

/// Builds one case. `n` is the number of prerequisite conditions, `changes` how
/// many of them the second formalization renders with a different predicate,
/// and `demorgan` selects the negated-disjunction rendering that only matches
/// after saturation. `rules` turns the De Morgan rewrites on.
fn build(n: usize, changes: usize, demorgan: bool, rules: bool) -> Case {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;

    assert!(changes <= n, "cannot plant more changes than conditions");

    // Vocabulary: one predicate per condition, plus the two the flag clause
    // needs. `And` and `Or` are ACI, which is what makes conjunct order and a
    // repeated conjunct free rather than something the search has to undo.
    let mut decls = String::from(
        "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) (Implies F F) (Clause F)\n  (Enrolled) (Permitted) (Flagged) (Suspended)",
    );
    for i in 0..n {
        decls.push_str(&format!(" (Prereq{i}) (Alt{i})"));
    }
    decls.push_str(")\n");

    let rewrites = if rules {
        // De Morgan, both directions, so saturation closes the pair regardless
        // of which rendering each formalizer chose.
        "(rewrite (Not (Or a b)) (And (Not a) (Not b)))\n\
         (rewrite (And (Not a) (Not b)) (Not (Or a b)))\n"
    } else {
        ""
    };

    // The flag clause: one formalizer negates the disjunction, the other
    // distributes the negation. With `demorgan` off both render it the same way,
    // so the position is shared without any rule.
    // Wrapped in `Clause` so the inner conjunction survives. `And` is AC, so a
    // bare `And` nested directly under the top-level conjunction would flatten
    // into it, leaving no binary node for De Morgan to match and dissolving the
    // very position this case is about.
    let (flag_left, flag_right) = if demorgan {
        (
            "(Clause (Not (Or (Flagged) (Suspended))))",
            "(Clause (And (Not (Flagged)) (Not (Suspended))))",
        )
    } else {
        ("(Clause (Not (Flagged)))", "(Clause (Not (Flagged)))")
    };

    // Formalization A: conditions in order.
    let mut left = String::from("(And (Enrolled)");
    for i in 0..n {
        left.push_str(&format!(" (Prereq{i})"));
    }
    left.push_str(&format!(" {flag_left})"));

    // Formalization B: the same conditions in reverse order, with the first
    // repeated (both absorbed by ACI), and `changes` of them replaced by a
    // different predicate, which is the genuine drift the search must find.
    let mut right = String::from("(And (Enrolled) (Enrolled)");
    for i in (0..n).rev() {
        if i < changes {
            right.push_str(&format!(" (Alt{i})"));
        } else {
            right.push_str(&format!(" (Prereq{i})"));
        }
    }
    right.push_str(&format!(" {flag_right})"));

    let program = format!(
        "{decls}{rewrites}(let L (Implies {left} (Permitted)))\n\
         (let R (Implies {right} (Permitted)))\n\
         (run {})\n",
        if rules { 6 } else { 0 }
    );

    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .expect("formalization program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("formalization program sortchecks");
    interp
        .run_checked(&checked)
        .expect("formalization program runs");
    let (l, _) = interp.global("L").expect("global L bound");
    let (r, _) = interp.global("R").expect("global R bound");
    Case {
        eg: interp.eg,
        left: l,
        right: r,
        planted: changes,
    }
}

/// Runs the exact solver and returns `(size, variants)`, where `variants` counts
/// the positions the anti-unifier generalized. That count is what the planted
/// changes predict.
fn solve(case: &Case) -> (u32, usize) {
    let snap = AuSnapshot::new(&case.eg).unwrap();
    let r = anti_unify(
        &snap,
        case.left,
        case.right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            exact_pruning: true,
            context_subsumption: true,
            exact_deadline: Some(GUARD),
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(
        r.completion,
        Completion::Exact,
        "exact solver must certify at this size"
    );
    // Count `Variants` nodes reachable from the root: each is one position where
    // the two formalizations genuinely disagree.
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![r.term_id];
    let mut variants = 0usize;
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(r.pool.op(t), TermOp::Variants) {
            variants += 1;
        }
        stack.extend_from_slice(r.pool.children(t));
    }
    (r.size, variants)
}

/// Class one: conjunct order and a repeated conjunct are canonization, not
/// search. With `And` declared ACI the two formalizations are the same e-node,
/// so the anti-unifier is the whole statement and generalizes nothing.
///
/// This is the check that keeps the other numbers honest: variability absorbed
/// here must never be counted as variability the search recovered.
#[test]
fn aci_variation_is_absorbed_by_canonization() {
    for n in [1usize, 2, 4, 8] {
        let mut case = build(n, 0, false, false);
        assert_eq!(
            case.eg.find(case.left),
            case.eg.find(case.right),
            "n={n}: reordering and repeating conjuncts must canonize to one class, \
             so the two formalizations are the same term"
        );
        let (_, variants) = solve(&case);
        assert_eq!(
            variants, 0,
            "n={n}: nothing is left for the search to generalize"
        );
    }
}

/// Class two: every planted change, and only a planted change, becomes a
/// generalized position. This is an oracle rather than a measurement, which is
/// what makes the family usable for scoring a formalizer later.
#[test]
fn planted_changes_equal_generalized_positions() {
    for n in [2usize, 4, 8, 12] {
        for changes in 0..=3.min(n) {
            let case = build(n, changes, false, false);
            let (_, variants) = solve(&case);
            assert_eq!(
                variants, case.planted,
                "n={n} changes={changes}: the anti-unifier must generalize exactly \
                 the planted positions"
            );
        }
    }
}

/// Class three: the case that needs the e-graph. One formalizer writes
/// `Not(Or(a, b))` and the other `And(Not(a), Not(b))`. As terms those share
/// nothing at that position; after saturating De Morgan they are one class.
///
/// The assertion is the comparison, not an absolute size: with the rules off the
/// solver must generalize the flag clause, and with them on it must not.
#[test]
fn rewrite_rules_recover_a_position_terms_cannot() {
    for n in [2usize, 4, 8] {
        let (size_off, variants_off) = solve(&build(n, 0, true, false));
        let (size_on, variants_on) = solve(&build(n, 0, true, true));
        assert!(
            variants_off > 0,
            "n={n}: without rules the two renderings of the flag clause share no \
             structure, so the position must be generalized"
        );
        assert_eq!(
            variants_on, 0,
            "n={n}: saturating De Morgan puts the two renderings in one class, so \
             the position is recovered"
        );
        assert!(
            size_on < size_off,
            "n={n}: recovering the position must produce a strictly better \
             anti-unifier ({size_on} against {size_off})"
        );
    }
}

/// The corpus table: statement size against what each class of difference costs.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_formalization \
///   formalization_corpus -- --ignored --nocapture
/// ```
#[test]
#[ignore = "measurement run; prints the auto-formalization corpus"]
fn formalization_corpus() {
    println!("{}\n", statement(3));
    println!(
        "{:>4} {:>8} {:>9} | {:>8} {:>9} | {:>8} {:>9} | {:>8} {:>9}",
        "n", "0 chg", "variants", "1 chg", "variants", "2 chg", "variants", "3 chg", "variants"
    );
    for n in [2usize, 4, 8, 12, 16] {
        let mut cells = Vec::new();
        for changes in 0..=3 {
            let (size, variants) = solve(&build(n, changes.min(n), false, false));
            cells.push((size, variants));
        }
        println!(
            "{n:>4} {:>8} {:>9} | {:>8} {:>9} | {:>8} {:>9} | {:>8} {:>9}",
            cells[0].0,
            cells[0].1,
            cells[1].0,
            cells[1].1,
            cells[2].0,
            cells[2].1,
            cells[3].0,
            cells[3].1
        );
    }
    println!("\nDe Morgan clause, rules off against rules on:");
    println!(
        "{:>4} {:>10} {:>9} | {:>10} {:>9}",
        "n", "off", "variants", "on", "variants"
    );
    for n in [2usize, 4, 8, 16] {
        let (off, voff) = solve(&build(n, 0, true, false));
        let (on, von) = solve(&build(n, 0, true, true));
        println!("{n:>4} {off:>10} {voff:>9} | {on:>10} {von:>9}");
    }
}

// ---------------------------------------------------------------------------
// Paraphrase operators, classified by whether their effect propagates
// ---------------------------------------------------------------------------
//
// The corpus above plants only LOCAL differences: a condition is swapped, the
// structure above it still matches, and the anti-unifier grows by one position
// per change. That is the ambiguity-BLOCKING case, and it makes change count
// look like a proxy for how far apart two formalizations are.
//
// It is the wrong case to generalize from. When two formalizations disagree
// about how a variable is determined rather than about a leaf, the
// undecidedness propagates to everything depending on that variable instead of
// being contained at the point of disagreement. One edit then costs whatever
// the downstream cone costs.
//
// Three operator classes, ordered by reach:
//
//   `Local`         one leaf predicate differs. Contained: the cone above it
//                   still matches structurally.
//   `Scoped`        a priority edge is present on one side only. A priority
//                   relation is declared pairwise and is deliberately not
//                   closed under transitivity, because a derived edge would
//                   suppress a rule in disputes the two rules never have, so
//                   one formalizer writing the derived edge and the other not
//                   is a real disagreement. Semantically its reach is exactly
//                   the pairs that edge decides. Structurally it changes the
//                   ARITY of the conjunction, which is the most destructive of
//                   the three UNLESS the operator declares its unit: with
//                   `:identity` the padding evens the two sides and the cost
//                   collapses to a constant. See
//                   `declaring_the_unit_recovers_an_arity_mismatch`.
//   `Propagating`   the two sides determine a variable differently: one lets
//                   the default apply, the other reifies the conflict and
//                   leaves the variable undetermined. Every consumer of the
//                   variable is then built differently, so the reach is the
//                   whole cone.
//
// The measurement is whether counting edits predicts anti-unifier cost. It does
// not, and `one_propagating_edit_outcosts_many_local_ones` is the assertion.

/// Which paraphrase operator distinguishes the two formalizations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operator {
    /// The two formalizations are identical. The baseline every other operator
    /// is priced against: without it the shared structure, which grows with the
    /// cone, drowns out the price of the disagreement.
    None,
    /// One leaf predicate replaced. Reach: that leaf.
    Local,
    /// The derived priority edge `a > c` written on one side only. Reach: the
    /// disputes that edge decides.
    Scoped,
    /// One side lets the default apply, the other reifies the conflict. Reach:
    /// every consumer of the variable.
    Propagating,
}

/// Builds a policy with `consumers` downstream uses of one decided variable,
/// rendered two ways under `op`. Exactly one textual edit separates the two
/// formalizations in every case, which is what makes the cost comparison fair.
fn build_operator(consumers: usize, op: Operator) -> Case {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;

    let mut decls = String::from(
        "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) (Clause F)\n  \
         (Rule F F) (Beats F F) (Det F F) (Undet F) (Use F F)\n  \
         (RuleA) (RuleB) (RuleC) (Grant) (Deny) (Var) (Alt)",
    );
    for i in 0..consumers {
        decls.push_str(&format!(" (Site{i})"));
    }
    decls.push_str(")\n");

    // The policy both sides agree on: three rules and the two declared edges.
    let base_rules = "(And (Rule (RuleA) (Grant)) (Rule (RuleB) (Deny)) (Rule (RuleC) (Grant)) \
                      (Beats (RuleA) (RuleB)) (Beats (RuleB) (RuleC)))";

    // How each side determines the variable, and how each site consumes it.
    let (extra_l, extra_r, det_l, det_r, leaf_l, leaf_r) = match op {
        // No disagreement: both sides render the policy the same way.
        Operator::None => (
            "",
            "",
            "(Det (Var) (Grant))",
            "(Det (Var) (Grant))",
            "(Grant)",
            "(Grant)",
        ),
        // Reach: one leaf. Both sides determine the variable identically.
        Operator::Local => (
            "",
            "",
            "(Det (Var) (Grant))",
            "(Det (Var) (Grant))",
            "(Grant)",
            "(Alt)",
        ),
        // Reach: the pairs the derived edge decides. The right-hand side closes
        // the declared edges transitively; the left does not.
        Operator::Scoped => (
            "",
            " (Beats (RuleA) (RuleC))",
            "(Det (Var) (Grant))",
            "(Det (Var) (Grant))",
            "(Grant)",
            "(Grant)",
        ),
        // Reach: every consumer. One side's unresolved conflict lets the
        // default stand; the other leaves the variable undetermined, so each
        // site is built around a different node.
        Operator::Propagating => (
            "",
            "",
            "(Det (Var) (Grant))",
            "(Undet (Var))",
            "(Grant)",
            "(Grant)",
        ),
    };

    let sites = |det: &str, leaf: &str| -> String {
        let mut out = String::from("(And");
        for i in 0..consumers {
            // The last site is where the Local operator plants its leaf, so the
            // three operators all differ by exactly one edit.
            let payload = if i + 1 == consumers { leaf } else { "(Grant)" };
            out.push_str(&format!(" (Use (Site{i}) (And {det} {payload}))"));
        }
        out.push(')');
        out
    };

    let left = format!("(And {base_rules}{extra_l} {})", sites(det_l, leaf_l));
    let right = format!("(And {base_rules}{extra_r} {})", sites(det_r, leaf_r));
    let program = format!("{decls}(let L {left})\n(let R {right})\n(run 0)\n");

    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .expect("operator program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("operator program sortchecks");
    interp.run_checked(&checked).expect("operator program runs");
    let (l, _) = interp.global("L").expect("global L bound");
    let (r, _) = interp.global("R").expect("global R bound");
    Case {
        eg: interp.eg,
        left: l,
        right: r,
        planted: 1,
    }
}

/// One edit is not one unit of disagreement.
///
/// All three operators separate the two formalizations by exactly one textual
/// edit. The local one stays flat as the number of consumers grows, because the
/// structure above the changed leaf still matches. The propagating one grows
/// with the consumers, because each is built around a different determination.
/// So a corpus that scores formalizations by counting edits, which is what the
/// planted-change oracle above does, measures the wrong thing on exactly the
/// differences that matter.
#[test]
fn one_propagating_edit_outcosts_many_local_ones() {
    let (small_local, _) = solve(&build_operator(2, Operator::Local));
    let (large_local, _) = solve(&build_operator(16, Operator::Local));
    let (small_prop, _) = solve(&build_operator(2, Operator::Propagating));
    let (large_prop, _) = solve(&build_operator(16, Operator::Propagating));

    let local_growth = large_local as i64 - small_local as i64;
    let prop_growth = large_prop as i64 - small_prop as i64;
    assert!(
        prop_growth > local_growth,
        "a propagating edit must cost more as the cone widens: local grew by \
         {local_growth} ({small_local} to {large_local}), propagating by \
         {prop_growth} ({small_prop} to {large_prop})"
    );
}

/// The ranking for an encoding that does NOT declare the conjunction's unit: an
/// edit changing arity costs more than one making a variable undetermined, which
/// costs more than one replacing a leaf.
///
/// The prediction going in was that the derived priority edge would sit between
/// the other two, since semantically its reach is only the disputes it decides.
/// It is the most expensive here, and the cause is arity rather than priority.
/// `declaring_the_unit_recovers_an_arity_mismatch` shows the ranking is a
/// property of the declaration and not of the operator: with `:identity` on the
/// conjunction, the arity term collapses to a constant and this ordering no
/// longer holds.
#[test]
fn arity_change_costs_more_than_propagation_costs_more_than_a_leaf() {
    let n = 16;
    let (base, _) = solve(&build_operator(n, Operator::None));
    let (local, _) = solve(&build_operator(n, Operator::Local));
    let (scoped, _) = solve(&build_operator(n, Operator::Scoped));
    let (prop, _) = solve(&build_operator(n, Operator::Propagating));
    let ex = |v: u32| v as i64 - base as i64;
    assert!(
        ex(local) < ex(prop),
        "a leaf edit must be cheaper than an undetermined variable: {} against {}",
        ex(local),
        ex(prop)
    );
    assert!(
        ex(prop) < ex(scoped),
        "an undetermined variable must be cheaper than an arity change: {} against {}",
        ex(prop),
        ex(scoped)
    );
}

/// Declaring the unit is what makes a dropped or added clause recoverable.
///
/// Anti-unifying two ACI conjunctions of different arity has no structural match
/// available on its own: a generalization must instantiate to both sides, and no
/// fixed-arity pattern does, since a variable standing for "one more conjunct
/// here" would have to vanish under the substitution producing the shorter side.
/// Without a unit the node is therefore generalized whole and both sides' mass
/// is paid, at `2n + 3` against `n` shared members: the anti-unifier roughly
/// doubles, at every width.
///
/// With the operator's identity declared, `pad_pair` pads the shorter monomial
/// with identity copies until the totals agree, the members that match do match,
/// and the excess is a constant 3 independent of `n`. The mismatch is fully
/// recovered.
///
/// | shared members | no `:identity` | with `:identity` |
/// | --- | --- | --- |
/// | 2 | 7 | 3 |
/// | 4 | 11 | 3 |
/// | 8 | 19 | 3 |
/// | 16 | 35 | 3 |
///
/// The consequence for a formalization corpus is the useful part, and it is a
/// statement about the encoding rather than about anti-unification: a policy
/// conjunction that declares its unit lets two formalizations differing over
/// whether a clause is present at all still share everything else, while one
/// that does not turns a single dropped clause into a total loss of sharing.
#[test]
fn declaring_the_unit_recovers_an_arity_mismatch() {
    for n in [2usize, 4, 8, 16] {
        let (bare_same, _) = solve(&build_conjunction_pair(n, n, false));
        let (bare_plus, _) = solve(&build_conjunction_pair(n, n + 1, false));
        assert_eq!(
            bare_plus as i64 - bare_same as i64,
            2 * n as i64 + 3,
            "n={n}: without a unit, one extra conjunct costs both sides' mass"
        );

        let (unit_same, _) = solve(&build_conjunction_pair(n, n, true));
        let (unit_plus, _) = solve(&build_conjunction_pair(n, n + 1, true));
        assert_eq!(
            unit_plus as i64 - unit_same as i64,
            3,
            "n={n}: with the unit declared, identity padding recovers the mismatch \
             at constant cost ({unit_same} to {unit_plus})"
        );
    }
}

/// Two ACI conjunctions with `left` and `right` members drawn from one pool.
/// `unit` declares the operator's identity, which is what lets `pad_pair` even
/// the two monomials.
fn build_conjunction_pair(left: usize, right: usize, unit: bool) -> Case {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;

    let hi = left.max(right);
    // `:identity` is a declaration tag on `function`, not on a `datatype`
    // constructor, so the operator is declared separately from the sort.
    let mut decls = String::from("(datatype F (P F) (Top)");
    for i in 0..hi {
        decls.push_str(&format!(" (A{i})"));
    }
    decls.push_str(")\n");
    decls.push_str(if unit {
        "(function And (F) F :assoc-comm-idem :identity (Top))\n"
    } else {
        "(function And (F) F :assoc-comm-idem)\n"
    });
    let members = |k: usize| {
        let mut s = String::from("(And");
        for i in 0..k {
            s.push_str(&format!(" (P (A{i}))"));
        }
        s.push(')');
        s
    };
    let program = format!(
        "{decls}(let L {})\n(let R {})\n(run 0)\n",
        members(left),
        members(right)
    );
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .expect("conjunction program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("conjunction program sortchecks");
    interp
        .run_checked(&checked)
        .expect("conjunction program runs");
    let (l, _) = interp.global("L").expect("global L bound");
    let (r, _) = interp.global("R").expect("global R bound");
    Case {
        eg: interp.eg,
        left: l,
        right: r,
        planted: 1,
    }
}

/// The operator table: cost against cone width, one line per operator.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_formalization \
///   paraphrase_operators -- --ignored --nocapture
/// ```
#[test]
#[ignore = "measurement run; prints the paraphrase-operator table"]
fn paraphrase_operators() {
    println!(
        "{:>9} {:>9} | {:>7} {:>7} | {:>7} {:>7} | {:>7} {:>7}",
        "consumers", "agreed", "local", "excess", "scoped", "excess", "propag", "excess"
    );
    for n in [2usize, 4, 8, 16, 32] {
        let (base, _) = solve(&build_operator(n, Operator::None));
        let (l, _) = solve(&build_operator(n, Operator::Local));
        let (sc, _) = solve(&build_operator(n, Operator::Scoped));
        let (p, _) = solve(&build_operator(n, Operator::Propagating));
        println!(
            "{n:>9} {base:>9} | {l:>7} {:>7} | {sc:>7} {:>7} | {p:>7} {:>7}",
            l as i64 - base as i64,
            sc as i64 - base as i64,
            p as i64 - base as i64
        );
    }
    println!(
        "\nEvery column is one textual edit; `excess` is its price over two \
         formalizations that agree.\nVariant count is not shown because it is 1 \
         for all three: hash-consing shares the differing\nsubterm, so counting \
         generalized positions cannot see how far a disagreement reaches."
    );
}
