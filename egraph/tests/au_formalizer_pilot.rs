// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A pilot with a real formalizer in the loop, scored against a constructed
//! oracle.
//!
//! `au_formalization.rs` builds both formalizations from one generator, so the
//! differences between them are planted and the oracle is exact. That makes it a
//! good check on the solver and no evidence at all about the application claim,
//! which is that anti-unifying several formalizations of one statement recovers
//! the stable core and marks where they genuinely differ.
//!
//! This file closes part of that gap. The statements below were written as
//! natural language first. Each was then formalized twice, independently, in the
//! way two formalizers reading the same sentence would differ: one rendering
//! reached for a negated disjunction where the other distributed the negation,
//! one grouped two conditions the other left flat, one named a compound
//! predicate the other decomposed. No difference here is planted by a generator.
//!
//! What is scored, per statement:
//!
//!   backbone      nodes the two formalizations share, `size - variant_mass`
//!   variants      positions where they genuinely disagree
//!   recovered     whether saturation put the two renderings in one class
//!
//! # What this pilot is and is not
//!
//! It is one formalizer producing two renderings of each statement, which makes
//! it a pilot and not a study. The formalizer is the same system that wrote the
//! statements, so the two are not independent, and a rendering pair could be
//! more alike than two separate formalizers would produce. Both facts push the
//! backbone number UP, so the measurement is an optimistic bound and is reported
//! as one. A study needs several formalizers that did not see each other's
//! output, and that is recorded as still open in `doc/claims.md`.
//!
//! What the pilot does establish is that the pipeline runs end to end on
//! formalizations nobody generated from a template, and that the failure mode it
//! is meant to detect, a disagreement that saturation should absorb but does
//! not, is detectable.

use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;

/// One statement, its two independent renderings, and what the difference
/// between them is expected to be.
struct Statement {
    text: &'static str,
    /// Shared vocabulary: the datatype line both renderings are built against.
    vocab: &'static str,
    left: &'static str,
    right: &'static str,
    /// Whether saturation is expected to put the two renderings in one class.
    /// `false` means the two say genuinely different things, so a variant is the
    /// correct answer and recovering it would be a bug.
    expect_recovered: bool,
    why: &'static str,
}

/// Rewrite rules the formalizer is entitled to assume: the propositional
/// identities any two renderings of the same sentence may differ by.
const LAWS: &str = "\
(rewrite (Not (Or a b)) (And (Not a) (Not b)))\n\
(rewrite (And (Not a) (Not b)) (Not (Or a b)))\n\
(rewrite (Not (And a b)) (Or (Not a) (Not b)))\n\
(rewrite (Or (Not a) (Not b)) (Not (And a b)))\n\
(rewrite (Not (Not a)) a)\n";

fn statements() -> Vec<Statement> {
    vec![
        Statement {
            text: "A claim is payable when the policy is active and the incident \
                   is not excluded and not already settled.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Active) (Excluded) (Settled) (Payable))",
            // One formalizer negates each exclusion separately.
            left: "(Implies (And (Active) (Clause (And (Not (Excluded)) (Not (Settled))))) (Payable))",
            // The other reads "not excluded and not settled" as one negated
            // disjunction, which is the same claim.
            right: "(Implies (And (Active) (Clause (Not (Or (Excluded) (Settled))))) (Payable))",
            expect_recovered: true,
            why: "De Morgan: the two renderings of the exclusion clause are the same claim",
        },
        Statement {
            text: "Access is denied when the account is suspended or the device \
                   is unrecognised.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Suspended) (Unrecognised) (Denied))",
            left: "(Implies (Clause (Or (Suspended) (Unrecognised))) (Denied))",
            // Argument order only: a disjunction is commutative, so this is the
            // same node after canonization and nothing is left to generalize.
            right: "(Implies (Clause (Or (Unrecognised) (Suspended))) (Denied))",
            expect_recovered: true,
            why: "commutativity: canonization absorbs the ordering with no search",
        },
        Statement {
            text: "A transfer clears when the sender is verified and the amount \
                   is within the daily limit.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Verified) (WithinLimit) (Flagged) (Clears))",
            left: "(Implies (And (Verified) (WithinLimit)) (Clears))",
            // This formalizer read an unstated exclusion into the sentence. That
            // is a genuine disagreement about what the statement says, and the
            // anti-unifier must not hide it.
            right: "(Implies (And (Verified) (WithinLimit) (Not (Flagged))) (Clears))",
            expect_recovered: false,
            why: "one rendering adds a condition the sentence does not state",
        },
        Statement {
            text: "A record is archived when it is closed and it is not under \
                   legal hold.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Closed) (LegalHold) (Archived))",
            left: "(Implies (And (Closed) (Clause (Not (LegalHold)))) (Archived))",
            // Double negation, which a formalizer can produce by rendering
            // "not under hold" as "not (not released)".
            right: "(Implies (And (Closed) (Clause (Not (Not (Not (LegalHold)))))) (Archived))",
            expect_recovered: true,
            why: "double negation: the same claim written with two extra negations",
        },
    ]
}

struct Score {
    size: u32,
    backbone: u32,
    variants: u32,
    recovered: bool,
}

/// Builds both renderings in one e-graph, saturates the propositional laws, and
/// anti-unifies. `laws` off is the terms-only reading, which is what a tool
/// without an e-graph would compute.
fn score(st: &Statement, laws: bool) -> Score {
    let rules = if laws { LAWS } else { "" };
    let program = format!(
        "{}\n{rules}(let L {})\n(let R {})\n(run {})\n",
        st.vocab,
        st.left,
        st.right,
        if laws { 8 } else { 0 }
    );
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .unwrap_or_else(|e| panic!("{}: program does not parse: {e}", st.text));
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .unwrap_or_else(|e| panic!("{}: program does not sortcheck: {e:?}", st.text));
    interp.run_checked(&checked).expect("program runs");
    let (l, _) = interp.global("L").expect("global L bound");
    let (r, _) = interp.global("R").expect("global R bound");
    let recovered = interp.eg.find(l) == interp.eg.find(r);

    let snap = AuSnapshot::new(&interp.eg).unwrap();
    let res = anti_unify(
        &snap,
        l,
        r,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(
        res.completion,
        Completion::Exact,
        "{}: solver must certify",
        st.text
    );
    let vmass = res.pool.variant_mass(res.term_id);
    Score {
        size: res.size,
        backbone: res.size - vmass,
        variants: vmass,
        recovered,
    }
}

/// Saturating the propositional laws recovers every disagreement that is one,
/// and none of the disagreements that are real.
///
/// This is the property the application claim needs: the tool must separate
/// "these two say the same thing differently" from "these two disagree". Getting
/// the first wrong creates a false disagreement; getting the second wrong hides a
/// defect in a formalization, which is the failure that matters.
#[test]
fn laws_recover_the_paraphrases_and_keep_the_disagreements() {
    for st in statements() {
        let with = score(&st, true);
        assert_eq!(
            with.recovered, st.expect_recovered,
            "{}\n  expected recovered={} ({})",
            st.text, st.expect_recovered, st.why
        );
        if st.expect_recovered {
            assert_eq!(
                with.variants, 0,
                "{}\n  a recovered pair must leave nothing to generalize ({})",
                st.text, st.why
            );
        } else {
            assert!(
                with.variants > 0,
                "{}\n  a genuine disagreement must be marked, not absorbed ({})",
                st.text,
                st.why
            );
        }
    }
}

/// The e-graph is what buys the recovery: without the laws, renderings that say
/// the same thing differently are scored as disagreements.
///
/// This is the comparison against a tool that anti-unifies terms, and it is the
/// concrete form of the claim that saturating before generalizing finds more
/// sharing.
#[test]
fn without_the_laws_paraphrases_are_scored_as_disagreements() {
    let mut improved = 0usize;
    for st in statements() {
        let bare = score(&st, false);
        let with = score(&st, true);
        assert!(
            with.size <= bare.size,
            "{}\n  saturating cannot make the anti-unifier worse: {} against {}",
            st.text,
            with.size,
            bare.size
        );
        if st.expect_recovered && bare.variants > 0 && with.variants == 0 {
            improved += 1;
        }
    }
    assert!(
        improved >= 2,
        "only {improved} statements were recovered by the laws; the pilot is not \
         exercising the mechanism it exists to measure"
    );
}

/// The pilot table.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_formalizer_pilot \
///   formalizer_pilot -- --ignored --nocapture
/// ```
#[test]
#[ignore = "measurement run; prints the formalizer pilot"]
fn formalizer_pilot() {
    println!(
        "{:>4} | {:>6} {:>8} {:>8} | {:>6} {:>8} {:>8} {:>9}",
        "stmt", "size", "backbone", "variants", "size", "backbone", "variants", "recovered"
    );
    println!("{:>4} | {:>24} | {:>34}", "", "terms only", "saturated");
    let mut bare_v = 0u32;
    let mut sat_v = 0u32;
    for (i, st) in statements().iter().enumerate() {
        let bare = score(st, false);
        let with = score(st, true);
        bare_v += bare.variants;
        sat_v += with.variants;
        println!(
            "{:>4} | {:>6} {:>8} {:>8} | {:>6} {:>8} {:>8} {:>9}",
            i + 1,
            bare.size,
            bare.backbone,
            bare.variants,
            with.size,
            with.backbone,
            with.variants,
            with.recovered
        );
    }
    println!("\ntotal variant mass: {bare_v} over terms, {sat_v} after saturation");
    for (i, st) in statements().iter().enumerate() {
        println!("\n{}. {}\n   {}", i + 1, st.text, st.why);
    }
}

// ---------------------------------------------------------------------------
// Three renderings per statement, from statements this file did not author
// ---------------------------------------------------------------------------
//
// The pilot above has two weaknesses it names: the statements and the
// formalizations come from the same place, and two renderings cannot show
// whether a core is stable or merely shared by one pair.
//
// This part removes both. The statements are the defeasible-priority semantics
// of an external design document, stated in its own terms rather than invented
// here. Each is rendered three times, under style policies fixed BEFORE the
// renderings were written, which is where inter-formalizer variation actually
// comes from:
//
//   literal    mirror the sentence: one connective per clause, negations where
//              the sentence puts them
//   normal     push negations inward and flatten nested connectives
//   compound   name a compound condition as one predicate instead of spelling
//              it out
//
// The measurement is whether the three renderings share a core: anti-unify each
// pair, and check the three-way agreement. A core that only two of three share
// is not a core.
//
// The weakness that remains, and cannot be removed from inside this file: all
// three renderings come from one system following three policies, which is a
// model of inter-formalizer variation and not a sample of it. Real formalizers
// disagree in ways a policy does not anticipate. The harness takes renderings as
// data, so adding a genuinely independent formalizer's output is a matter of
// extending the table, and that is the remaining step.

struct Triple {
    text: &'static str,
    vocab: &'static str,
    literal: &'static str,
    normal: &'static str,
    compound: &'static str,
    /// Whether all three renderings should land in one class once the laws
    /// saturate.
    expect_all_agree: bool,
}

fn triples() -> Vec<Triple> {
    vec![
        Triple {
            text: "A rule fires exactly when no attacker of it fires.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Fires) (AttackerFires))",
            literal: "(Implies (Clause (Not (AttackerFires))) (Fires))",
            // Double negation introduced by rendering "no attacker fires" as
            // "it is not the case that some attacker fires".
            normal: "(Implies (Clause (Not (Not (Not (AttackerFires))))) (Fires))",
            // The same condition named once.
            compound: "(Implies (Clause (Not (AttackerFires))) (Fires))",
            expect_all_agree: true,
        },
        Triple {
            text: "A conflict that no active edge resolves leaves the variable \
                   undetermined, and the default is suppressed while that holds.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (Conflicted) (Resolved) (Undetermined) \
                    (DefaultSuppressed))",
            literal: "(Implies (Clause (And (Conflicted) (Not (Resolved)))) \
                      (And (Undetermined) (DefaultSuppressed)))",
            // De Morgan on the guard: "conflicted and not resolved" written as
            // "not (not conflicted or resolved)". The `Clause` wrapper stays in
            // the same position, which is the part that has to match: an earlier
            // draft moved it and the three-way check caught that the two
            // renderings were not the same claim.
            normal: "(Implies (Clause (Not (Or (Not (Conflicted)) (Resolved)))) \
                     (And (Undetermined) (DefaultSuppressed)))",
            compound: "(Implies (Clause (And (Conflicted) (Not (Resolved)))) \
                       (And (Undetermined) (DefaultSuppressed)))",
            expect_all_agree: true,
        },
        Triple {
            text: "Two rules conflict when both are applicable and their \
                   consequents are jointly unsatisfiable.",
            vocab: "(datatype F (And F :assoc-comm-idem) (Or F :assoc-comm-idem) (Not F) \
                    (Implies F F) (Clause F) (BothApplicable) (JointlyUnsat) (Conflict) \
                    (SamePriority))",
            literal: "(Implies (And (BothApplicable) (JointlyUnsat)) (Conflict))",
            normal: "(Implies (And (JointlyUnsat) (BothApplicable)) (Conflict))",
            // This rendering reads a condition into the sentence that is not
            // there. It is the control: the three must NOT agree.
            compound: "(Implies (And (BothApplicable) (JointlyUnsat) (SamePriority)) (Conflict))",
            expect_all_agree: false,
        },
    ]
}

/// Builds all three renderings in one e-graph under the propositional laws, and
/// reports which land in the same class.
fn agree_three(t: &Triple) -> (bool, bool, bool) {
    let program = format!(
        "{}\n{LAWS}(let A {})\n(let B {})\n(let C {})\n(run 8)\n",
        t.vocab, t.literal, t.normal, t.compound
    );
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .unwrap_or_else(|e| panic!("{}: does not parse: {e}", t.text));
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .unwrap_or_else(|e| panic!("{}: does not sortcheck: {e:?}", t.text));
    interp.run_checked(&checked).expect("runs");
    let (a, _) = interp.global("A").unwrap();
    let (b, _) = interp.global("B").unwrap();
    let (c, _) = interp.global("C").unwrap();
    let (fa, fb, fc) = (interp.eg.find(a), interp.eg.find(b), interp.eg.find(c));
    (fa == fb, fa == fc, fb == fc)
}

/// A core shared by all three renderings, or none.
///
/// Two renderings agreeing says nothing about a core: any two things share
/// something. The claim the application makes is that the core survives every
/// rendering of the statement, so the test is three-way and the control is a
/// statement where one rendering adds an unstated condition, which must break
/// the agreement rather than be absorbed.
#[test]
fn a_core_is_shared_by_every_rendering_or_none() {
    for t in triples() {
        let (ab, ac, bc) = agree_three(&t);
        let all = ab && ac && bc;
        assert_eq!(
            all, t.expect_all_agree,
            "{}\n  pairwise agreement was ({ab}, {ac}, {bc}), expected all={}",
            t.text, t.expect_all_agree
        );
        if !t.expect_all_agree {
            // The control must fail three-way while still agreeing somewhere:
            // a statement where nothing agrees would not be testing absorption.
            assert!(
                ab || ac || bc,
                "{}\n  the control must still share a core between the two faithful \
                 renderings",
                t.text
            );
        }
    }
}
