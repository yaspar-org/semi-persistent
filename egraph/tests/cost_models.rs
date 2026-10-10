// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `(cost-model …)` and `(extract … :cost …)`, through the binary.
//!
//! - A Roto cost script that subtracts an over-estimate is rejected when the
//!   program is checked, with the script's line and the command's.
//! - The MLTL memory cost as a script and as the registered Rust cost extract the
//!   same cost at every rung.

use std::process::Command;

/// Whether `program` runs. A test that needs an external solver returns early, saying
/// so, when it is absent: CI installs none of them.
fn installed(program: &str) -> bool {
    let ok = std::process::Command::new(program)
        .arg("--version")
        .output()
        .is_ok();
    if !ok {
        eprintln!("{program} not installed: this test did not run");
    }
    ok
}

/// RoundingSat and VeriPB, where `a_proof_is_kept_and_verifies` runs them.
fn proof_tools() -> bool {
    let home = std::env::var("HOME").unwrap_or_default();
    installed(&format!("{home}/.local/bin/roundingsat"))
        && installed(&format!("{home}/.local/bin/veripb"))
}

const PRELUDE: &str = r#"
(sort IntervalSort)
(function Interval (i64 i64) IntervalSort)
(sort MLTL)
(function Bool (bool) MLTL)
(function Var (String) MLTL)
(function Not (MLTL) MLTL)
(function And (MLTL) MLTL :assoc-comm-idem :identity (Bool true))
(function Or (MLTL) MLTL :assoc-comm-idem :identity (Bool false))
(function Global (IntervalSort MLTL) MLTL)
(function Future (IntervalSort MLTL) MLTL)
(let e0 (Var "a0"))
(let e1 (Var "a1"))
(let e2 (Global (Interval 0 9) e0))
(let e3 (Future (Interval 2 3) e1))
(let e4 (Global (Interval 1 4) e1))
(let e5 (Future (Interval 0 7) e0))
(let e6 (And e2 e3 e4 e5))
"#;

fn run(program: &str) -> (bool, String, String) {
    let dir = std::env::temp_dir().join(format!(
        "semper_cost_{}_{}",
        std::process::id(),
        program.len()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("p.egg");
    std::fs::write(&path, program).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
        .arg(&path)
        .args(["--types", "machine"])
        .output()
        .unwrap();
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into(),
        String::from_utf8_lossy(&out.stderr).into(),
    )
}

fn script() -> String {
    format!(
        "{}/tests/mltl/costs/mltl_memory.roto",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn a_polarity_error_is_a_program_error_with_its_line() {
    let bad = std::env::temp_dir().join(format!("semper_bad_{}.roto", std::process::id()));
    std::fs::write(
        &bad,
        "fn cost(g: Graph) {\n    let wpd = g.attribute_max(g.node_values());\n    let a = wpd.of(g.root());\n    if g.nodes().len() > 1000000 {\n        a.minus(wpd.of(g.root())).charge();\n    }\n}\n",
    )
    .unwrap();
    // The extract after the model never runs: the program is rejected when checked.
    let program = format!(
        "{PRELUDE}\n(cost-model bad :script \"{}\")\n(extract e6 :cost bad)\n",
        bad.display()
    );
    let (ok, stdout, stderr) = run(&program);
    let _ = std::fs::remove_file(&bad);
    assert!(!ok, "accepted: {stdout}");
    assert!(stdout.is_empty(), "something ran: {stdout}");
    assert!(stderr.contains(".roto:5:"), "no script line: {stderr}");
    assert!(stderr.contains("cost-model bad"), "no command: {stderr}");
    eprintln!("{stderr}");
}

#[test]
fn the_script_and_the_rust_cost_agree_at_every_rung() {
    let mut program = format!(
        "{PRELUDE}\n(cost-model roto :script \"{}\")\n(cost-model native :rust \"mltl-memory\")\n",
        script()
    );
    for rung in ["selection", "levels", "splits", "binary", "orders"] {
        program += &format!(
            "(extract e6 :cost roto :rung {rung})\n(extract e6 :cost native :rung {rung})\n"
        );
    }
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let costs: Vec<&str> = stdout.lines().filter(|l| l.starts_with("; cost")).collect();
    assert_eq!(costs.len(), 10, "{stdout}");
    for pair in costs.chunks(2) {
        let figure = |l: &str| l.split(" (").next().unwrap().to_string();
        assert_eq!(figure(pair[0]), figure(pair[1]), "{stdout}");
        assert!(pair[0].contains(" proved "), "{stdout}");
    }
    eprintln!("{stdout}");
}

#[test]
fn an_unknown_model_or_rung_is_rejected() {
    let (ok, _, stderr) = run(&format!("{PRELUDE}\n(extract e6 :cost nowhere)\n"));
    assert!(
        !ok && stderr.contains("no cost model named 'nowhere'"),
        "{stderr}"
    );
    let (ok, _, stderr) = run(&format!(
        "{PRELUDE}\n(cost-model n :rust \"mltl-memory\")\n(extract e6 :cost n :rung trees)\n"
    ));
    assert!(!ok && stderr.contains("unknown rung 'trees'"), "{stderr}");
}

#[test]
fn an_ac_operand_keeps_its_multiplicity_in_every_output() {
    // `Add` is AC with multiplicities, and `G[1,4] a1` occurs twice. Under the memory
    // cost the splits optimum groups it with `F[2,3] a1`; it is written once with its
    // count, `:2`, in the text and in the JSON (`"mults"`), and the count is not lost.
    let dir = std::env::temp_dir().join(format!("semper_mult_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let json = dir.join("t.json");
    let program = format!(
        "{PRELUDE}\n(function Add (MLTL) MLTL :assoc-comm)\n\
         (let g (Global (Interval 1 4) e1))\n\
         (let s (Add e2 e3 g g e5))\n(cost-model m :script \"{}\")\n\
         (extract s :cost m :rung selection)\n(extract s :cost m :rung splits :file \"{}\")\n",
        script(),
        json.display()
    );
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    eprintln!("{stdout}");
    let terms: Vec<&str> = stdout.lines().filter(|l| l.starts_with("(Add")).collect();
    assert_eq!(terms.len(), 2, "{stdout}");
    assert!(
        terms[1].matches("(Add").count() > 1,
        "the splits optimum is regrouped: {}",
        terms[1]
    );
    for t in &terms {
        assert_eq!(t.matches("(Global 1 4").count(), 1, "written once: {t}");
        assert!(
            t.contains("(Global 1 4 (Var \"a1\")):2"),
            "the count was dropped: {t}"
        );
    }
    let text = std::fs::read_to_string(&json).unwrap();
    let refs = count_refs(&text, "Global", "1,4");
    assert_eq!(refs, 2, "{text}");
}

/// The total count of references, among children lists, to the class of the node with
/// `op` and ints `ints` (written compactly, as `1,4`): each reference weighted by its
/// entry in the node's `"mults"`, 1 where the node has none. The JSON is read with
/// whitespace removed; node keys are `cN` or `cN.M` and no string in it contains a space.
fn count_refs(json: &str, op: &str, ints: &str) -> usize {
    let flat: String = json.chars().filter(|c| !c.is_whitespace()).collect();
    let want_op = format!("\"op\":\"{op}\"");
    let want_ints = format!("\"ints\":[{ints}]");
    let mut key = None;
    for (at, _) in flat.match_indices("\":{") {
        let start = flat[..at].rfind('"').unwrap() + 1;
        let body = &flat[at + 3..at + 3 + flat[at + 3..].find('}').unwrap()];
        if body.contains(&want_op) && body.contains(&want_ints) {
            key = Some(flat[start..at].to_string());
        }
    }
    let key = key.expect("node present");
    let quoted = format!("\"{key}\"");
    let list = |body: &str, field: &str| -> Vec<String> {
        body.find(&format!("\"{field}\":["))
            .map(|i| &body[i + field.len() + 4..])
            .and_then(|r| r.split(']').next())
            .map(|r| {
                r.split(',')
                    .filter(|x| !x.is_empty())
                    .map(str::to_string)
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut total = 0;
    for (at, _) in flat.match_indices("\":{") {
        let body = &flat[at + 3..at + 3 + flat[at + 3..].find('}').unwrap()];
        let (kids, mults) = (list(body, "children"), list(body, "mults"));
        for (i, k) in kids.iter().enumerate() {
            if *k == quoted {
                total += mults.get(i).map_or(1, |m| m.parse::<usize>().unwrap());
            }
        }
    }
    total
}

#[test]
fn the_asp_solver_proves_the_same_optima() {
    if !installed("clingo") {
        return;
    }
    // The MLTL script on clingo equals it on the internal solver, at every rung.
    let mut program = format!("{PRELUDE}\n(cost-model roto :script \"{}\")\n", script());
    for rung in ["selection", "levels", "splits", "binary", "orders"] {
        program += &format!(
            "(extract e6 :cost roto :rung {rung})\n(extract e6 :cost roto :rung {rung} :solver (asp \"clingo\"))\n"
        );
    }
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let costs: Vec<&str> = stdout.lines().filter(|l| l.starts_with("; cost")).collect();
    assert_eq!(costs.len(), 10, "{stdout}");
    for pair in costs.chunks(2) {
        let figure = |l: &str| l.split(" (").next().unwrap().to_string();
        assert_eq!(figure(pair[0]), figure(pair[1]), "{stdout}");
    }
}

#[test]
fn a_proof_is_kept_and_verifies() {
    if !proof_tools() {
        return;
    }
    let home = std::env::var("HOME").unwrap();
    let dir = std::env::temp_dir().join(format!("semper_proof_{}", std::process::id()));
    let program = format!(
        "{PRELUDE}\n(cost-model roto :script \"{}\")\n\
         (extract e6 :cost roto :rung splits :solver (opb \"{home}/.local/bin/roundingsat\" \"--print-sol=1\" \"--verbosity=0\") :proof \"{}\")\n",
        script(),
        dir.display()
    );
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let line = stdout
        .lines()
        .find(|l| l.starts_with("; certificate"))
        .expect("a certificate line");
    let mut parts = line.rsplit(' ');
    let (proof, instance) = (parts.next().unwrap(), parts.next().unwrap());
    let v = Command::new(format!("{home}/.local/bin/veripb"))
        .args([instance, proof])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&v.stdout).contains("s VERIFIED"),
        "{}",
        String::from_utf8_lossy(&v.stdout)
    );
    let (ok, _, stderr) = run(&format!(
        "{PRELUDE}\n(cost-model roto :script \"{}\")\n(extract e6 :cost roto :proof \"/tmp/x\")\n",
        script()
    ));
    assert!(!ok && stderr.contains(":proof needs"), "{stderr}");
}

/// The book's cost-model examples (`doc/book/examples/cost-models/`), run from
/// their own directory so their script paths resolve: each prints exactly its
/// `.out` file, or, marked `;; EXPECT: sort-error`, is rejected naming its script.
#[test]
fn book_cost_model_examples() {
    let dir = std::path::Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../doc/book/examples/cost-models"
    ));
    let mut n = 0;
    for e in std::fs::read_dir(dir).unwrap().flatten() {
        let p = e.path();
        if p.extension().is_none_or(|x| x != "egg") {
            continue;
        }
        let src = std::fs::read_to_string(&p).unwrap();
        // An example that needs a solver CI does not install is skipped, saying so.
        if (src.contains("(asp \"clingo\")") && !installed("clingo"))
            || (src.contains("(minizinc \"") && !installed("minizinc"))
        {
            continue;
        }
        let out = Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
            .current_dir(dir)
            .arg(&p)
            .args(["--types", "machine"])
            .output()
            .unwrap();
        let (stdout, stderr) = (
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        );
        if src.contains(";; EXPECT: sort-error") {
            assert!(
                !out.status.success() && stderr.contains("sort error") && stderr.contains(".roto:"),
                "{}: {stderr}",
                p.display()
            );
        } else {
            assert!(out.status.success(), "{}: {stderr}", p.display());
            let want = std::fs::read_to_string(p.with_extension("out")).unwrap();
            assert_eq!(stdout, want, "{}", p.display());
        }
        n += 1;
    }
    assert!(n >= 3, "only {n} examples");
}

/// An associative sequence is bracketed at the tree rungs, and the printed term
/// keeps its operand order: a cost rewarding internal nodes makes the binary rung's
/// optimum a full bracketing of `a b c d`, and the splits rung's the same count.
#[test]
fn an_associative_sequence_is_bracketed_in_order() {
    let dir = std::env::temp_dir().join(format!("semper_seq_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let script = dir.join("inner.roto");
    std::fs::write(&script, "fn cost(g: Graph) {\n    for n in g.nodes() {\n        for t in n.inner_nodes() {\n            t.exists().times(1).neg().charge();\n        }\n    }\n}\n").unwrap();
    let program = format!(
        "(sort E)\n(function a () E)\n(function b () E)\n(function c () E)\n(function d () E)\n(function Cat (E) E :assoc)\n\
         (let e0 (Cat a b c d))\n(cost-model m :script \"{}\")\n\
         (extract e0 :cost m :rung selection)\n(extract e0 :cost m :rung binary)\n(extract e0 :cost m :rung splits)\n",
        script.display()
    );
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    let costs: Vec<&str> = lines
        .iter()
        .copied()
        .filter(|l| l.starts_with("; cost"))
        .collect();
    assert_eq!(costs.len(), 3, "{stdout}");
    // Flat at the selection rung; two internal nodes at binary and at splits.
    assert!(costs[0].starts_with("; cost 0 "), "{stdout}");
    assert!(costs[1].starts_with("; cost -2 "), "{stdout}");
    assert!(costs[2].starts_with("; cost -2 "), "{stdout}");
    for (i, l) in lines.iter().enumerate() {
        if !l.starts_with("; cost") {
            continue;
        }
        let term = lines[i + 1];
        let at = |x: &str| {
            term.find(x)
                .unwrap_or_else(|| panic!("{x} missing in {term}"))
        };
        assert!(
            at("(a)") < at("(b)") && at("(b)") < at("(c)") && at("(c)") < at("(d)"),
            "operands out of order: {term}"
        );
    }
    assert_eq!(
        lines[lines.iter().position(|l| l == &costs[1]).unwrap() + 1]
            .matches("(Cat")
            .count(),
        3,
        "{stdout}"
    );
}

/// A cost model written in ASP extracts through clingo with the Rust cost's optimum
/// at every rung, and naming it with a non-ASP solver is a sort error naming it.
#[test]
fn an_asp_cost_model_extracts_and_needs_clingo() {
    if !installed("clingo") {
        return;
    }
    let lp = format!(
        "{}/tests/mltl/costs/mltl_memory.lp",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut program = format!(
        "{PRELUDE}\n(cost-model asp :asp \"{lp}\")\n(cost-model native :rust \"mltl-memory\")\n"
    );
    for rung in ["selection", "levels", "splits", "binary", "orders"] {
        program += &format!(
            "(extract e6 :cost asp :rung {rung} :solver (asp \"clingo\"))\n(extract e6 :cost native :rung {rung})\n"
        );
    }
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let costs: Vec<&str> = stdout.lines().filter(|l| l.starts_with("; cost")).collect();
    assert_eq!(costs.len(), 10, "{stdout}");
    for pair in costs.chunks(2) {
        let figure = |l: &str| l.split(" (").next().unwrap().to_string();
        assert_eq!(figure(pair[0]), figure(pair[1]), "{stdout}");
    }
    let (ok, stdout, stderr) = run(&format!(
        "{PRELUDE}\n(cost-model asp :asp \"{lp}\")\n(extract e6 :cost asp)\n"
    ));
    assert!(!ok && stdout.is_empty(), "{stdout}");
    assert!(
        stderr.contains("cost-model asp is written in ASP"),
        "{stderr}"
    );
}

/// A cost model written in MiniZinc extracts through `minizinc` with the Rust
/// cost's optimum at every rung, and a mismatch between a MiniZinc model and its
/// solver is a sort error naming the model.
#[test]
fn a_minizinc_cost_model_extracts_and_needs_minizinc() {
    if !installed("minizinc") {
        return;
    }
    let mzn = format!(
        "{}/tests/mltl/costs/mltl_memory.mzn",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut program = format!(
        "{PRELUDE}\n(cost-model mzn :minizinc \"{mzn}\")\n(cost-model native :rust \"mltl-memory\")\n"
    );
    for rung in ["selection", "levels", "splits", "binary", "orders"] {
        program += &format!(
            "(extract e6 :cost mzn :rung {rung} :solver (minizinc \"cp-sat\"))\n(extract e6 :cost native :rung {rung})\n"
        );
    }
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let costs: Vec<&str> = stdout.lines().filter(|l| l.starts_with("; cost")).collect();
    assert_eq!(costs.len(), 10, "{stdout}");
    for pair in costs.chunks(2) {
        let figure = |l: &str| l.split(" (").next().unwrap().to_string();
        assert_eq!(figure(pair[0]), figure(pair[1]), "{stdout}");
    }
    let (ok, stdout, stderr) = run(&format!(
        "{PRELUDE}\n(cost-model mzn :minizinc \"{mzn}\")\n(extract e6 :cost mzn)\n"
    ));
    assert!(!ok && stdout.is_empty(), "{stdout}");
    assert!(
        stderr.contains("cost-model mzn is written in MiniZinc"),
        "{stderr}"
    );
    let (ok, _, stderr) = run(&format!(
        "{PRELUDE}\n(cost-model native :rust \"mltl-memory\")\n(extract e6 :cost native :solver (minizinc \"cp-sat\"))\n"
    ));
    assert!(
        !ok && stderr.contains("cost-model native is not written in MiniZinc"),
        "{stderr}"
    );
}

/// A `:band` bound is exact. It was cast with `as i64`, so `:band 0 18446744073709551615`
/// became `[0, -1]` and listed no term; a bound above every cost is the same band as
/// one at `i64::MAX`.
#[test]
fn a_band_bound_past_i64_is_exact() {
    let program = format!(
        "{PRELUDE}\n(let t (And e1 e2))\n(cost-model n :rust \"mltl-memory\")\n\
         (extract t :cost n :band 0 9223372036854775807)\n\
         (extract t :cost n :band 0 18446744073709551615)\n"
    );
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    let count = |hi: &str| {
        let line = stdout
            .lines()
            .find(|l| l.ends_with(&format!("cost in [0, {hi}] at rung selection")))
            .unwrap_or_else(|| panic!("{stdout}"));
        line.split_whitespace().nth(1).unwrap().to_string()
    };
    assert_eq!(
        count("9223372036854775807"),
        count("18446744073709551615"),
        "{stdout}"
    );
    assert_ne!(count("18446744073709551615"), "0", "{stdout}");
}

/// `--cost-bits` (`doc/goal-counted-multiplicities.md`, step 6, bug #6): nested
/// `Future[0, i64::MAX]` makes the MLTL memory cost's attribute 2^64 - 2. At 64 bits
/// that is a reported error, where it wrapped to `Proved -2`; unbounded, the cost is
/// exact; any other width is refused by the parser.
#[test]
fn the_cost_width_is_a_flag() {
    let program = format!(
        "{PRELUDE}\n(cost-model n :rust \"mltl-memory\")\n\
         (extract (Future (Interval 0 9223372036854775807) (Future (Interval 0 9223372036854775807) e0)) :cost n)\n"
    );
    let dir = std::env::temp_dir().join(format!("semper_cost_bits_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("p.egg");
    std::fs::write(&path, &program).unwrap();
    let run_bits = |bits: &str| {
        let out = Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
            .arg(&path)
            .args(["--types", "machine", "--cost-bits", bits])
            .output()
            .unwrap();
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).to_string(),
            String::from_utf8_lossy(&out.stderr).to_string(),
        )
    };
    let (ok, _, stderr) = run_bits("64");
    assert!(
        !ok && stderr.contains("outside the 64-bit cost range"),
        "{stderr}"
    );
    let (ok, stdout, stderr) = run_bits("big");
    assert!(ok, "{stderr}");
    assert!(stdout.contains("; cost 4 proved"), "{stdout}");
    // The default is `big` (`doc/goal-arbitrary-precision-costs.md`, step 5).
    let (ok, stdout, stderr) = run(&program);
    assert!(ok, "{stderr}");
    assert!(stdout.contains("; cost 4 proved"), "{stdout}");
    let (ok, _, stderr) = run_bits("128");
    assert!(
        !ok && stderr.contains("expected '32', '64', or 'big'"),
        "{stderr}"
    );
}

/// An `IBig` interval bound past `i64` reaches the cost as the number it is
/// (`doc/goal-arbitrary-precision-costs.md`, step 2). It used to arrive as a string, so the
/// MLTL memory cost read the interval as `[0, 0]`. `(And (Global [0, 2^70] a) b)` costs
/// 1 (the specification) + 4 (one per counted class) + 2^70 (`b`'s queue while `Global`
/// finishes) = 2^70 + 5, proved.
#[test]
fn a_bignum_bound_past_i64_is_exact() {
    let program = r#"
(sort IntervalSort)
(function Interval (IBig IBig) IntervalSort)
(sort MLTL)
(function Bool (bool) MLTL)
(function Var (String) MLTL)
(function And (MLTL) MLTL :assoc-comm-idem :identity (Bool true))
(function Global (IntervalSort MLTL) MLTL)
(cost-model n :rust "mltl-memory")
(extract (And (Global (Interval 0 1180591620717411303424) (Var "a")) (Var "b")) :cost n)
"#;
    let dir = std::env::temp_dir().join(format!("semper_bignum_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("p.egg");
    std::fs::write(&path, program).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
        .arg(&path)
        .args(["--types", "machine,bignum", "--cost-bits", "big"])
        .output()
        .unwrap();
    let (stdout, stderr) = (
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    assert!(out.status.success(), "{stderr}");
    assert!(
        stdout.contains("; cost 1180591620717411303429 proved"),
        "{stdout}"
    );
}
