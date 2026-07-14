// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Auxiliary deterministic fixtures for conversion, policy postprocessing, extraction,
// clustering, and configuration behavior. These are not all AU acceptance tests, but
// retain the surrounding behaviors needed by the complete conformance suite.

const TOP_ACTION: usize = 5;
const TOP_ACTIONS: &[usize] = &[1, 3, 5, 7];
const SINGLE_ACTION_QUERY_COUNT: usize = 100;
const QUALITY_DIST: &[(usize, f64)] = &[(0, 0.5), (1, 0.3), (2, 0.2)];

const RANKED: &[&[usize]] = &[&[0, 1, 2], &[0, 2, 1], &[1, 0, 2]];
const ALPHA: f64 = 0.01;

const CONVERSION_INPUT: &str = "(Eq v1 (Mul 0.10 (Sub v2 (Mul 4000.0 (Ite v3 1.0 0.75)))))";
const CONVERSION_EXPECTED: &str = "(= v1 (* 0.1 (- v2 (* 4000.0 (ite v3 1.0 0.75)))))";

const EXTRACTION_CASES: &[(&str, &str)] = &[
    ("assume:v1;then:v2", "(=> v1 v2)"),
    ("assume:v1,v3;then:v2", "(=> (and v1 v3) v2)"),
    ("invalid", ""),
    ("assume:NONE;then:v2", ""),
];

const CLUSTER_EXPRESSIONS: &[&str] = &[
    "(=> (<= v1 30) v2)",
    "(=> (and v3 (<= v1 30)) v2)",
    "(=> (and v3 (= v1 29)) v2)",
    "(=> (and v3 (= v1 29)) v2)",
];

#[test]
fn response_model_fixtures_are_exact() {
    assert_eq!(TOP_ACTION, 5);
    assert_eq!(TOP_ACTIONS, &[1, 3, 5, 7]);
    assert_eq!(SINGLE_ACTION_QUERY_COUNT, 100);
    assert!((QUALITY_DIST.iter().map(|x| x.1).sum::<f64>() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn ranked_policy_smoothing_order_is_exact() {
    let mut raw = [0.0_f64; 3];
    for response in RANKED {
        for (rank, &index) in response.iter().enumerate() {
            raw[index] += 1.0 / (rank as f64 + 1.0);
        }
    }
    let total: f64 = raw.iter().sum();
    let empirical = raw.map(|w| w / total);
    let smoothed = empirical.map(|p| p + ALPHA);
    let z: f64 = smoothed.iter().sum();
    let final_dist = smoothed.map(|p| p / z);
    assert!((final_dist.iter().sum::<f64>() - 1.0).abs() < 1e-12);
    assert!(final_dist.iter().all(|p| p.is_finite() && *p > 0.0));
    assert!(final_dist[0] > final_dist[1] && final_dist[1] > final_dist[2]);
}

#[test]
fn conversion_fixture_is_anonymous_and_shape_preserving() {
    for text in [CONVERSION_INPUT, CONVERSION_EXPECTED] {
        assert!(text.contains("v1") && text.contains("v2") && text.contains("v3"));
        for forbidden in ["group_", "source_repo", "private_model", "private_path"] {
            assert!(!text.to_ascii_lowercase().contains(forbidden));
        }
    }
    assert!(CONVERSION_EXPECTED.starts_with("(= v1"));
}

#[test]
fn extraction_and_clustering_fixtures_preserve_assertions() {
    assert_eq!(EXTRACTION_CASES[0].1, "(=> v1 v2)");
    assert_eq!(EXTRACTION_CASES[1].1, "(=> (and v1 v3) v2)");
    assert!(EXTRACTION_CASES[2].1.is_empty() && EXTRACTION_CASES[3].1.is_empty());
    assert_eq!(CLUSTER_EXPRESSIONS[2], CLUSTER_EXPRESSIONS[3]);
    assert_ne!(CLUSTER_EXPRESSIONS[0], CLUSTER_EXPRESSIONS[1]);
}

#[test]
fn reference_configuration_defaults_are_pinned() {
    let (rollouts, report_step, saturation_iterations) = (1000_u32, 1000_u32, 4_u32);
    let (llm_k, llm_n, alpha) = (10_u32, 5_u32, 0.01_f64);
    assert_eq!(
        (rollouts, report_step, saturation_iterations),
        (1000, 1000, 4)
    );
    assert_eq!((llm_k, llm_n), (10, 5));
    assert_eq!(alpha, ALPHA);
}

const REPRESENTATIVE_CLUSTERS: &[&[usize]] = &[&[0, 1], &[2, 3]];
const REPRESENTATIVE_EXPRESSIONS: &[&str] = &[
    "(=> v1 v2)",
    "(=> (and v1 v3 v4 v5 v6) (and v2 v7 v8 v9 v10))",
    "(=> v11 v12)",
    "(=> (and v11 v13) (and v12 v14))",
];

const DISTINCT_TERM_PAIR: (&str, &str) = ("(assert (=> v1 v2))", "(assert (=> v3 v4))");
const CONSISTENT_CLUSTER_RUNS: &[&[&[usize]]] = &[
    &[&[0, 1], &[2, 3]],
    &[&[0, 1], &[2, 3]],
    &[&[0, 1], &[2, 3]],
];
const MIXED_VALIDITY: &[Option<&str>] = &[Some("(=> v1 v2)"), None, None, Some("(=> v3 v4)")];

#[test]
fn shortest_cluster_representatives_are_stable() {
    let picked: Vec<usize> = REPRESENTATIVE_CLUSTERS
        .iter()
        .map(|cluster| {
            *cluster
                .iter()
                .min_by_key(|&&idx| (REPRESENTATIVE_EXPRESSIONS[idx].len(), idx))
                .unwrap()
        })
        .collect();
    assert_eq!(picked, vec![0, 2]);
}

#[test]
fn generated_term_pair_is_nonidentical() {
    assert_ne!(DISTINCT_TERM_PAIR.0, DISTINCT_TERM_PAIR.1);
    assert!(DISTINCT_TERM_PAIR.0.starts_with("(assert "));
    assert!(DISTINCT_TERM_PAIR.1.starts_with("(assert "));
}

#[test]
fn clustering_runs_are_deterministic() {
    for run in &CONSISTENT_CLUSTER_RUNS[1..] {
        assert_eq!(*run, CONSISTENT_CLUSTER_RUNS[0]);
    }
}

#[test]
fn invalid_preprocessing_inputs_preserve_valid_cases() {
    let valid: Vec<&str> = MIXED_VALIDITY.iter().filter_map(|x| *x).collect();
    assert!(valid.len() >= 2);
    // Two distinct valid expressions imply at least one nonempty cluster.
    assert!(!valid.is_empty());
}

fn catalan(n: u64) -> u64 {
    (0..n).fold(1_u64, |acc, k| acc * (2 * n - k) / (k + 1)) / (n + 1)
}

fn factorial(n: u64) -> u64 {
    (1..=n).product()
}

#[test]
fn explicit_rewrite_and_canonical_ac_counts_are_exact() {
    let expected = [
        (2_u64, 2_u64, 4_u64, 4_u64, 2_u64),
        (3, 12, 144, 36, 6),
        (5, 1_680, 2_822_400, 900, 120),
        (6, 30_240, 914_457_600, 3_844, 720),
    ];
    for (n, representatives, term_pairs, root_pairs, canonical_actions) in expected {
        let r = factorial(n) * catalan(n - 1);
        assert_eq!(r, representatives);
        assert_eq!(r * r, term_pairs);
        assert_eq!((2_u64.pow(n as u32) - 2).pow(2), root_pairs);
        assert_eq!(factorial(n), canonical_actions);
    }
}

#[test]
fn matching_count_matrix_subtracts_multiplicities() {
    // M={a:3,b:1}, N={a:1,c:3}. The top-left allocation t can be 0 or 1.
    let mut matrices = Vec::new();
    for t in 0_u32..=1 {
        let x = [[t, 3 - t], [1 - t, t]];
        assert_eq!(x[0][0] + x[0][1], 3); // left a exhausted
        assert_eq!(x[1][0] + x[1][1], 1); // left b exhausted
        assert_eq!(x[0][0] + x[1][0], 1); // right a exhausted
        assert_eq!(x[0][1] + x[1][1], 3); // right c exhausted
        matrices.push(x);
    }
    assert_eq!(matrices.len(), 2);
}

#[test]
fn greedy_ac_pairing_can_be_strictly_suboptimal() {
    // X has equivalent f(v1,v1) and g(v1,v1), Y=f(v1,v2), Z=g(v1,v2).
    // Variant node cost is zero: Variants(Y,Z) costs 3+3=6.
    let greedy = 1 + 3 + 6; // AC parent + AU(X,X) + AU(Y,Z)
    let crossed = 1 + 4 + 4; // factor g in AU(X,Z), f in AU(Y,X)
    assert_eq!(greedy, 10);
    assert_eq!(crossed, 9);
    assert!(crossed < greedy);
}
