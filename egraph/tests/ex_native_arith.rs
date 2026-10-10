// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A cost script may not use Roto's own arithmetic operators, which wrap on overflow
//! and abort on division by zero (`extraction::script::reject_native_arithmetic`).

use semi_persistent_egraph::extraction::script::{Script, reject_native_arithmetic};

fn refused(src: &str) -> String {
    reject_native_arithmetic(src).expect_err(src)
}

#[test]
fn every_arithmetic_operator_is_refused_with_its_position() {
    for (src, op, pos) in [
        (
            "fn cost(g: Graph) {\n    g.charge_const(k + 2);\n}",
            "`+`",
            "2:22",
        ),
        ("let a = b - c;", "`-`", "1:11"),
        ("let a = b * c;", "`*`", "1:11"),
        ("let a = b / c;", "`/`", "1:11"),
        ("let a = b % c;", "`%`", "1:11"),
        ("a += 1;", "`+=`", "1:3"),
        ("a -= 1;", "`-=`", "1:3"),
        ("a *= 1;", "`*=`", "1:3"),
        ("a /= 1;", "`/=`", "1:3"),
        ("a %= 1;", "`%=`", "1:3"),
        ("a--;", "`--`", "1:2"),
        ("let a = -x;", "`-`", "1:9"),
        ("let a = k -1;", "`-`", "1:11"),
        ("let a = f(1) - 2;", "`-`", "1:14"),
        ("let s = f\"{a + b}\";", "`+`", "1:14"),
    ] {
        let e = refused(src);
        assert!(e.starts_with(&format!("{pos}: {op} ")), "{src:?}: {e}");
        assert!(e.contains("exact methods"), "{e}");
    }
}

#[test]
fn literals_comments_strings_and_arrows_are_allowed() {
    for src in [
        "// k + 1 in a comment\nfn cost(g: Graph) {}",
        "let s = \"a + b * c / d % e - f\";",
        "let s = \"an escaped \\\" quote + \";",
        "let c = '+'; let d = '\\'';",
        "fn f(x: u64) -> u64 { x }",
        "match x { A => 1, B => 2 }",
        "let x = g.int([-9223372036854775807, 9223372036854775807]);",
        "let b = g.ibig(-3);",
        "let a = -3;",
        "return -3;",
        "f(a, -1);",
        "if a <= b && b >= c || a != b { }",
    ] {
        assert_eq!(reject_native_arithmetic(src), Ok(()), "{src:?}");
    }
}

#[test]
fn compile_names_the_file_and_refuses_before_roto_runs() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("ex_native_arith");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("wrap.roto");
    std::fs::write(
        &path,
        "fn cost(g: Graph) {\n    let k: i64 = 9223372036854775807;\n    g.charge_const(k + 2);\n}\n",
    )
    .unwrap();
    let e = match Script::compile(path.to_str().unwrap()) {
        Ok(_) => panic!("a script with `+` compiled"),
        Err(e) => e,
    };
    assert!(e.contains("wrap.roto:3:22: `+`"), "{e}");
    // The same cost through the exact methods compiles.
    std::fs::write(
        &path,
        "fn cost(g: Graph) {\n    let k = g.ibig(9223372036854775807);\n    g.charge_const_big(k.plus(g.ibig(2)));\n}\n",
    )
    .unwrap();
    if let Err(e) = Script::compile(path.to_str().unwrap()) {
        panic!("the exact spelling did not compile: {e}");
    }
}
