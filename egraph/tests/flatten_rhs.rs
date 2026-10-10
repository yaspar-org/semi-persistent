// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `--flatten-rhs`: a rewrite's AC result gets a flat alternative for a same-op
//! child that canonization keeps nested because its class is used elsewhere.
//!
//! `b + c` is a child of `a·(b + c)`, so its class is atomic, and the rule's result
//! `(b + c) + d` keeps it nested. With the flag, `b + c + d` is in the graph after the
//! same single round; without it, it is not. An operator with `:inverse` is left
//! alone: its cancellation depends on the nesting.

use std::process::Command;

const PROGRAM: &str = r#"
(sort E)
(function V (String) E)
(function Add (E) E :assoc-comm)
(function Mul (E) E :assoc-comm)
(let s (Add (V "b") (V "c")))
(let t (Mul (V "a") s))
(let e (W s))
(rewrite (W x) (Add x (V "d")))
(run 1)
(check (= e (Add (V "b") (V "c") (V "d"))))
"#;

fn run(flag: bool, program: &str) -> bool {
    let path = std::env::temp_dir().join(format!("flatten_rhs_{}_{flag}.egg", std::process::id()));
    std::fs::write(&path, program).unwrap();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_semi-persistent"));
    cmd.arg(&path).args(["--types", "machine"]);
    if flag {
        cmd.arg("--flatten-rhs");
    }
    let ok = cmd.output().unwrap().status.success();
    let _ = std::fs::remove_file(&path);
    ok
}

#[test]
fn a_rewrite_result_gets_its_flat_alternative_only_with_the_flag() {
    let p = PROGRAM.replace("(let e (W s))", "(function W (E) E)\n(let e (W s))");
    assert!(
        run(true, &p),
        "with --flatten-rhs the flat sum is equal to the rewrite's result"
    );
    assert!(!run(false, &p), "without it the atomic child stays nested");
}
