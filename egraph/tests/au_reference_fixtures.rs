// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated/public fixture corpus for the future `au` module. These tests intentionally
// validate the corpus schema before the AU implementation exists. The implementation
// tests will iterate `AU_CASES` and apply the expectations below.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expectation {
    NonEmpty,
    Identical,
    CommutativeEquivalent,
    ProjectionPair,
    RegressionNoPanic,
}

#[derive(Clone, Copy, Debug)]
pub struct AuCase {
    pub id: &'static str,
    pub variables: &'static [&'static str],
    pub declarations: &'static str,
    pub left: &'static str,
    pub right: &'static str,
    pub eqsat_iterations: u32,
    pub rollouts: u32,
    pub expected: Expectation,
}

pub const AU_CASES: &[AuCase] = &[
    AuCase {
        id: "au_001_conflicting_thresholds",
        variables: &["v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8"],
        declarations: "v1:S1 v2:S2 v3:Int v4:Bool v5:Bool v6:Bool v7:Bool v8:Real",
        left: "(=> (and (= v1 c1) (= v2 c2) (= v3 28) v4 v5 (= v3 32)) (not v7))",
        right: "(=> (and (= v1 c1) (= v2 c2) (= v8 20.0) v4 v5 (= v3 32) v6) (not v7))",
        eqsat_iterations: 3,
        rollouts: 3,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_002_strict_inequality",
        variables: &["v1", "v2", "v3"],
        declarations: "v1:Real v2:Real v3:Bool",
        left: "(=> (<= v1 v2) (not v3))",
        right: "(=> (< v1 v2) (not v3))",
        eqsat_iterations: 4,
        rollouts: 20,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_003_disparate_rules",
        variables: &["v1", "v2", "v3", "v4"],
        declarations: "v1:S1 v2:Int v3:Real v4:S2",
        left: "(=> (and (= v1 c1) (= v2 2) (= v2 4)) (= v3 0.0))",
        right: "(=> (= v4 c2) true)",
        eqsat_iterations: 4,
        rollouts: 20,
        expected: Expectation::NonEmpty,
    },
    AuCase {
        id: "au_004_parallel_constants",
        variables: &["v1", "v2"],
        declarations: "v1:Int v2:Int",
        left: "(=> true (= v1 10))",
        right: "(=> true (= v2 10))",
        eqsat_iterations: 4,
        rollouts: 1,
        expected: Expectation::RegressionNoPanic,
    },
    AuCase {
        id: "au_005_bounded_window",
        variables: &["v1", "v2", "v3", "v4", "v5"],
        declarations: "v1:S1 v2:Int v3:Real v4:Real v5:Bool",
        left: "(=> (and (= v1 c1) (= v2 20)) (and (= v3 75.0) (= v4 25.0) v5))",
        right: "(=> (= v2 20) (and (= v3 75.0) (= v4 25.0) v5 (>= v2 15) (< v2 120)))",
        eqsat_iterations: 4,
        rollouts: 100,
        expected: Expectation::RegressionNoPanic,
    },
    AuCase {
        id: "au_006_cost_components",
        variables: &["v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8"],
        declarations: "v1:Bool v2:Bool v3:Bool v4:Bool v5:Real v6:Real v7:Real v8:Real",
        left: "(=> (and v1 v2 (not v3)) (and (> v5 0) (> v6 0) (> v7 0)))",
        right: "(=> (and v1 v4) (and (> v5 0) (> v8 0) (> v7 0)))",
        eqsat_iterations: 4,
        rollouts: 100,
        expected: Expectation::RegressionNoPanic,
    },
    AuCase {
        id: "au_007_shared_result_add",
        variables: &["v1", "v2", "v3"],
        declarations: "v1:Int v2:Int v3:Int",
        left: "(= v3 (+ v1 1))",
        right: "(= v3 (+ v2 1))",
        eqsat_iterations: 4,
        rollouts: 10,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_008_distinct_results_add",
        variables: &["v1", "v2", "v3", "v4"],
        declarations: "v1:Int v2:Int v3:Int v4:Int",
        left: "(= v3 (+ v1 1))",
        right: "(= v4 (+ v2 1))",
        eqsat_iterations: 4,
        rollouts: 10,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_009_identical",
        variables: &["v1"],
        declarations: "v1:Int",
        left: "(= v1 5)",
        right: "(= v1 5)",
        eqsat_iterations: 0,
        rollouts: 1,
        expected: Expectation::Identical,
    },
    AuCase {
        id: "au_010_commutative_add",
        variables: &["v1", "v2", "v3"],
        declarations: "v1:Int v2:Int v3:Int",
        left: "(= v3 (+ v1 v2))",
        right: "(= v3 (+ v2 v1))",
        eqsat_iterations: 5,
        rollouts: 5,
        expected: Expectation::CommutativeEquivalent,
    },
    AuCase {
        id: "au_011_commutative_and",
        variables: &["v1", "v2"],
        declarations: "v1:Bool v2:Bool",
        left: "(and v1 v2)",
        right: "(and v2 v1)",
        eqsat_iterations: 5,
        rollouts: 5,
        expected: Expectation::CommutativeEquivalent,
    },
    AuCase {
        id: "au_012_double_negation",
        variables: &["v1"],
        declarations: "v1:Bool",
        left: "v1",
        right: "(not (not v1))",
        eqsat_iterations: 5,
        rollouts: 10,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_013_boolean_opposites",
        variables: &["v1"],
        declarations: "v1:Bool",
        left: "v1",
        right: "(not v1)",
        eqsat_iterations: 1,
        rollouts: 10,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_014_shared_antecedent",
        variables: &["v1", "v2", "v3"],
        declarations: "v1:Bool v2:Bool v3:Bool",
        left: "(=> v1 (and v2 v3))",
        right: "(=> v1 v3)",
        eqsat_iterations: 4,
        rollouts: 20,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_015_liability_shape",
        variables: &["v1", "v2", "v3", "v4"],
        declarations: "v1:Bool v2:Bool v3:Real v4:Real",
        left: "(=> v1 (= v3 v4))",
        right: "(=> (not v2) (> v3 0.0))",
        eqsat_iterations: 4,
        rollouts: 20,
        expected: Expectation::RegressionNoPanic,
    },
    AuCase {
        id: "au_016_multiple_assertion_shape",
        variables: &["v1", "v2", "v3", "v4"],
        declarations: "v1:S1 v2:S2 v3:Bool v4:Real",
        left: "(and (=> (= v1 c1) v3) (=> (= v1 c1) (= v4 0.0)))",
        right: "(and (=> (and (= v2 c2) (= v1 c1)) (= v4 0.0)) (=> (and (= v2 c2) (= v1 c1)) v3))",
        eqsat_iterations: 5,
        rollouts: 1000,
        expected: Expectation::NonEmpty,
    },
    AuCase {
        id: "au_017_arithmetic_compression",
        variables: &["v1", "v2", "v3", "v4"],
        declarations: "v1:Int v2:Int v3:Int v4:Int",
        left: "(= v4 (+ (* v1 v1) v2))",
        right: "(= v4 (+ v3 (* v1 v3)))",
        eqsat_iterations: 4,
        rollouts: 100,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_018_distinct_constants",
        variables: &["v1"],
        declarations: "v1:Int",
        left: "(= v1 1)",
        right: "(= v1 2)",
        eqsat_iterations: 4,
        rollouts: 10,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_019_few_shot_shape",
        variables: &["v1", "v2"],
        declarations: "v1:Int v2:Int",
        left: "(+ v1 1)",
        right: "(+ v2 1)",
        eqsat_iterations: 0,
        rollouts: 0,
        expected: Expectation::ProjectionPair,
    },
    AuCase {
        id: "au_020_rollout_shape",
        variables: &["v1", "v2", "v3"],
        declarations: "v1:Bool v2:Bool v3:Bool",
        left: "(and v1 v2)",
        right: "(and v1 v3)",
        eqsat_iterations: 0,
        rollouts: 1,
        expected: Expectation::ProjectionPair,
    },
];

#[derive(Clone, Copy, Debug)]
struct VariantCase {
    expression: &'static str,
    variables: &'static [&'static str],
    expected_left: &'static str,
    expected_right: &'static str,
}

const VARIANT_CASE: VariantCase = VariantCase {
    expression: "(or (not (variants (<= v1 v2) (< v1 v2))) (not v3))",
    variables: &["v1", "v2", "v3"],
    expected_left: "(or (not (<= v1 v2)) (not v3))",
    expected_right: "(or (not (< v1 v2)) (not v3))",
};

#[derive(Clone, Copy, Debug)]
struct VoteCase {
    votes: &'static [usize],
    expected: &'static [(usize, f64)],
}

const SINGLE_VOTES: VoteCase = VoteCase {
    votes: &[0, 1, 0, 2, 0],
    expected: &[(0, 0.6), (1, 0.2), (2, 0.2)],
};

const RANKED_RESPONSES: &[&[usize]] = &[&[0, 1, 2], &[0, 2, 1], &[1, 0, 2]];

fn identifiers(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|s| !s.is_empty())
}

fn is_vn(s: &str) -> bool {
    s.strip_prefix('v').is_some_and(|tail| {
        !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()) && tail != "0"
    })
}

#[test]
fn fixture_corpus_is_anonymous_and_well_formed() {
    assert!(AU_CASES.len() >= 20);
    let mut ids = std::collections::BTreeSet::new();
    for case in AU_CASES {
        assert!(ids.insert(case.id), "duplicate fixture id: {}", case.id);
        assert!(!case.left.is_empty() && !case.right.is_empty());
        assert!(case.rollouts > 0 || case.id == "au_019_few_shot_shape");
        for (i, &var) in case.variables.iter().enumerate() {
            assert_eq!(var, format!("v{}", i + 1));
            assert!(is_vn(var));
            assert!(
                identifiers(case.left)
                    .chain(identifiers(case.right))
                    .any(|x| x == var)
            );
        }
        let combined = format!(
            "{} {} {} {}",
            case.id, case.declarations, case.left, case.right
        )
        .to_ascii_lowercase();
        for forbidden in ["group_", "source_repo", "private_model", "private_path"] {
            assert!(
                !combined.contains(forbidden),
                "non-anonymous token {forbidden} in {}",
                case.id
            );
        }
        let _ = (case.eqsat_iterations, case.expected);
    }
}

#[test]
fn variant_projection_fixture_is_exact() {
    assert_eq!(VARIANT_CASE.variables, &["v1", "v2", "v3"]);
    assert!(VARIANT_CASE.expression.contains("(variants "));
    assert!(!VARIANT_CASE.expected_left.contains("variants"));
    assert!(!VARIANT_CASE.expected_right.contains("variants"));
    assert_ne!(VARIANT_CASE.expected_left, VARIANT_CASE.expected_right);
}

#[test]
fn empirical_single_vote_distribution_is_exact() {
    let mut counts = std::collections::BTreeMap::<usize, usize>::new();
    for &vote in SINGLE_VOTES.votes {
        *counts.entry(vote).or_default() += 1;
    }
    for &(index, expected) in SINGLE_VOTES.expected {
        let actual = *counts.get(&index).unwrap_or(&0) as f64 / SINGLE_VOTES.votes.len() as f64;
        assert!((actual - expected).abs() < f64::EPSILON);
    }
}

#[test]
fn inverse_rank_weights_match_fixture() {
    let mut weights = [0.0_f64; 3];
    for response in RANKED_RESPONSES {
        for (rank, &index) in response.iter().enumerate() {
            weights[index] += 1.0 / (rank as f64 + 1.0);
        }
    }
    let total: f64 = weights.iter().sum();
    let normalized = weights.map(|x| x / total);
    assert!((normalized[0] - 5.0 / 11.0).abs() < 1e-12);
    assert!((normalized[1] - 1.0 / 3.0).abs() < 1e-12);
    assert!((normalized[2] - 7.0 / 33.0).abs() < 1e-12);
}
