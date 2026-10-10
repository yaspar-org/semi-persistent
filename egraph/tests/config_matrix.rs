// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The multiplicity fixtures under both built configurations (`--bits 32`, u32 counts, and
//! `--bits 64`, u64 counts; `doc/goal-counted-multiplicities.md`, step 5). A count's width
//! decides the outcome, so the expectation is per configuration: a sum past 2^32 is an
//! error at 32 bits and exact at 64, and a count past 2^64 is an error at both. Every
//! error a fixture expects from a count is reported as a multiplicity overflow.

use std::process::Command;

/// What a run ended in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    Ok,
    Error,
    SortError,
    CheckFailed,
}
use Outcome::*;

const CONFIGS: [&[&str]; 2] = [&["--bits", "32"], &["--bits", "64"]];

fn run(file: &str, flags: &[&str]) -> (Outcome, String) {
    let path = format!("{}/tests/egg/{file}.egg", env!("CARGO_MANIFEST_DIR"));
    // The fixture's own completion directives, as the egg_tests harness reads them.
    let src = std::fs::read_to_string(&path).unwrap_or_default();
    let mut extra: Vec<&str> = Vec::new();
    for line in src.lines().take(10) {
        match line.trim() {
            ";; DERIVE_AC_EQS: on" => extra.push("--derive-ac-eqs"),
            ";; LAZY_AC_EQS: on" => extra.push("--lazy-ac-eqs"),
            _ => {}
        }
    }
    let out = Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
        .arg(&path)
        .args(["--types", "machine"])
        .args(flags)
        .args(&extra)
        .output()
        .expect("run the binary");
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let outcome = if out.status.success() {
        Ok
    } else if stderr.contains("sort error") {
        SortError
    } else if stderr.contains("check failed") {
        CheckFailed
    } else {
        Error
    };
    (outcome, stderr)
}

/// Each fixture's outcome under `--bits 32` and `--bits 64`.
#[test]
fn every_multiplicity_fixture_under_every_configuration() {
    let table: &[(&str, [Outcome; 2])] = &[
        ("mult_rhs_max_width", [Ok, Ok]),
        ("mult_rhs_splice_rest", [Ok, Ok]),
        ("mult_build_flatten_product", [Ok, Ok]),
        // 2^32 fits 64 bits.
        ("mult_rhs_sum_overflow", [Error, Ok]),
        ("mult_rhs_splice_overflow", [Error, Ok]),
        ("mult_rhs_computed_too_wide", [Error, Ok]),
        ("mult_build_flatten_overflow", [Error, Ok]),
        // k*k*k at 2^32 - 1 is about 2^96: past both widths.
        ("mult_rhs_u64_overflow", [Error, Error]),
        // At 32 bits the view does not fit and the node is skipped; wider, the rule
        // fires on it, which the fixture's `!=` check records.
        ("mult_flatten_view_overflow", [Ok, CheckFailed]),
        ("mult_rhs_underflow_two_vars", [Error, Error]),
        ("ground_mult_kinds", [Ok, Ok]),
        ("ground_mult_full_width", [Ok, Ok]),
        ("ground_mult_extract_roundtrip", [Ok, Ok]),
        ("ground_mult_overflow", [Error, Ok]),
        ("ground_mult_too_wide", [Error, Ok]),
        ("ground_mult_not_variadic", [SortError, SortError]),
        ("ground_mult_zero", [SortError, SortError]),
        // Past 2^64.
        ("mult_ground_past_u64", [Error, Error]),
        ("mult_rule_past_u64", [Error, Error]),
        // The integer audit's reproductions (doc/goal-counted-multiplicities.md, step 5b).
        ("audit_union_coalesce_overflow", [Error, Ok]),
        ("audit_completion_sum_overflow", [Error, Ok]),
        ("audit_completion_rewrite_batch", [Ok, Ok]),
        ("audit_extract_saturated_cost", [Ok, Ok]),
        ("audit_au_large_count", [Ok, Ok]),
        ("audit_gt_u64_max", [SortError, SortError]),
        ("audit_mset_into_positional", [Error, Error]),
        ("audit_seq_count_past_u64", [Error, Error]),
        ("audit_merge_monomial_overflow", [Error, Ok]),
    ];
    // Fixtures whose error is a count past the width: each must say so in the same words.
    let overflow = |file: &str| {
        file.contains("overflow")
            || file.contains("too_wide")
            || file.contains("past_u64")
            || file == "mult_rhs_computed_too_wide"
    };
    let mut failures = Vec::new();
    for (file, want) in table {
        for (flags, &w) in CONFIGS.iter().zip(want) {
            let (got, stderr) = run(file, flags);
            if got != w {
                failures.push(format!(
                    "{file} {flags:?}: want {w:?}, got {got:?}: {stderr}"
                ));
            } else if got == Error && overflow(file) && !stderr.contains("multiplicity overflow") {
                failures.push(format!(
                    "{file} {flags:?}: an overflow not reported as one: {stderr}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `--mult-bits` is gone: the multiplicity width follows `--bits`. `--id-bits 31|63`, the
/// earlier spelling, still selects a preset.
#[test]
fn the_width_follows_the_preset_and_the_old_spelling_is_accepted() {
    let (got, stderr) = run("ground_mult_kinds", &["--bits", "32", "--mult-bits", "64"]);
    assert_eq!(got, Error, "{stderr}");
    assert!(stderr.contains("--mult-bits"), "{stderr}");
    assert_eq!(run("ground_mult_too_wide", &["--id-bits", "31"]).0, Error);
    assert_eq!(run("ground_mult_too_wide", &["--id-bits", "63"]).0, Ok);
}
