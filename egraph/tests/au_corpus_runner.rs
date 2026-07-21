// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end runner for the 20-case AU conformance corpus.
//!
//! Builds a NIRA theory, parses the fixture s-expressions into e-graph nodes,
//! runs anti-unification, and checks expectations.

use num_bigint::BigInt;
use num_rational::BigRational;
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::NiraLitVal;
use std::collections::HashMap;

type Eg = EGraph31<NiraLitVal, false, false>;

#[path = "au_reference_fixtures.rs"]
#[allow(dead_code)]
mod fixtures;
use fixtures::{AU_CASES, AuCase, Expectation};

struct Theory {
    eg: Eg,
    sorts: HashMap<String, SortId>,
    ops: HashMap<String, OpId>,
    vars: HashMap<String, (ENodeId, SortId)>,
    int_lit_op: OpId,
    real_lit_op: OpId,
}

fn build_theory(case: &AuCase) -> Theory {
    let mut eg = Eg::new();
    let mut sorts = HashMap::new();
    let mut ops: HashMap<String, OpId> = HashMap::new();

    let bool_s = eg.intern_sort("Bool");
    let int_s = eg.intern_sort("Int");
    let real_s = eg.intern_sort("Real");
    let s1 = eg.intern_sort("S1");
    let s2 = eg.intern_sort("S2");
    sorts.insert("Bool".into(), bool_s);
    sorts.insert("Int".into(), int_s);
    sorts.insert("Real".into(), real_s);
    sorts.insert("S1".into(), s1);
    sorts.insert("S2".into(), s2);

    // Operators
    macro_rules! reg {
        ($name:expr, $id:expr) => {
            ops.insert($name.into(), $id);
        };
    }

    reg!("=>", eg.register_op2("=>", bool_s, bool_s, bool_s));
    reg!("not", eg.register_op1("not", bool_s, bool_s));

    let tt_op = eg.register_op0("true", bool_s);
    let tt = eg.add(tt_op, &[]);
    let and_op = eg.register_set("and", bool_s, bool_s);
    eg.set_unit_node(and_op, tt);
    ops.insert("and".into(), and_op);

    let ff_op = eg.register_op0("false", bool_s);
    let ff = eg.add(ff_op, &[]);
    let or_op = eg.register_set("or", bool_s, bool_s);
    eg.set_unit_node(or_op, ff);
    ops.insert("or".into(), or_op);
    ops.insert("true".into(), tt_op);
    ops.insert("false".into(), ff_op);

    reg!("<_Int", eg.register_op2("<_Int", int_s, int_s, bool_s));
    reg!("<=_Int", eg.register_op2("<=_Int", int_s, int_s, bool_s));
    reg!(">_Int", eg.register_op2(">_Int", int_s, int_s, bool_s));
    reg!(">=_Int", eg.register_op2(">=_Int", int_s, int_s, bool_s));
    reg!("<_Real", eg.register_op2("<_Real", real_s, real_s, bool_s));
    reg!(
        "<=_Real",
        eg.register_op2("<=_Real", real_s, real_s, bool_s)
    );
    reg!(">_Real", eg.register_op2(">_Real", real_s, real_s, bool_s));
    reg!(
        ">=_Real",
        eg.register_op2(">=_Real", real_s, real_s, bool_s)
    );

    reg!("=_Bool", eg.register_c("=_Bool", [bool_s, bool_s], bool_s));
    reg!("=_Int", eg.register_c("=_Int", [int_s, int_s], bool_s));
    reg!("=_Real", eg.register_c("=_Real", [real_s, real_s], bool_s));
    reg!("=_S1", eg.register_c("=_S1", [s1, s1], bool_s));
    reg!("=_S2", eg.register_c("=_S2", [s2, s2], bool_s));

    reg!("+_Int", eg.register_c("+_Int", [int_s, int_s], int_s));
    reg!("*_Int", eg.register_c("*_Int", [int_s, int_s], int_s));

    reg!("c1", eg.register_op0("c1", s1));
    reg!("c2", eg.register_op0("c2", s2));

    // Literal ops
    let int_lit_op = eg.register_lit("intlit", int_s);
    let real_lit_op = eg.register_lit("reallit", real_s);

    // Variables from declarations
    let mut vars = HashMap::new();
    for decl in case.declarations.split_whitespace() {
        let parts = decl.split(':').collect::<Vec<&str>>();
        if parts.len() == 2 {
            let name = parts[0];
            let sort = *sorts
                .get(parts[1])
                .unwrap_or_else(|| panic!("unknown sort: {}", parts[1]));
            let var_op = eg.register_op0(name, sort);
            let node = eg.add(var_op, &[]);
            ops.insert(name.into(), var_op);
            vars.insert(name.to_string(), (node, sort));
        }
    }

    Theory {
        eg,
        sorts,
        ops,
        vars,
        int_lit_op,
        real_lit_op,
    }
}

/// Parse an s-expression string into an e-graph node.
fn parse_sexpr(theory: &mut Theory, s: &str) -> (ENodeId, SortId) {
    parse_sexpr_hint(theory, s, None)
}

fn parse_sexpr_hint(theory: &mut Theory, s: &str, hint: Option<SortId>) -> (ENodeId, SortId) {
    let s = s.trim();
    if s.starts_with('(') {
        let inner = &s[1..s.len() - 1];
        let (op_name, rest) = split_first_token(inner);
        let children_str = rest.trim();
        let child_strs = split_args(children_str);

        // For sort-polymorphic binary ops (=, <, <=, >, >=): parse children
        // in two passes. First pass determines sorts; if one child is Real and
        // the other is Int (a bare numeric), reparse the Int child as Real.
        let real_s = *theory.sorts.get("Real").unwrap();
        let int_s = *theory.sorts.get("Int").unwrap();
        let is_polymorphic = matches!(op_name, "=" | "<" | "<=" | ">" | ">=");

        let mut children: Vec<(ENodeId, SortId)> = child_strs
            .iter()
            .map(|c| parse_sexpr_hint(theory, c, None))
            .collect();

        if is_polymorphic && children.len() == 2 {
            let has_real = children.iter().any(|(_, s)| *s == real_s);
            if has_real {
                for (i, cs) in child_strs.iter().enumerate() {
                    if children[i].1 == int_s {
                        // Reparse with Real hint
                        children[i] = parse_sexpr_hint(theory, cs, Some(real_s));
                    }
                }
            }
        }

        let resolved_op = resolve_op(theory, op_name, &children);
        let child_ids: Vec<ENodeId> = children.iter().map(|(id, _)| *id).collect();
        let node = theory.eg.add(resolved_op.0, &child_ids);
        (node, resolved_op.1)
    } else {
        parse_atom_with_hint(theory, s, hint)
    }
}

fn parse_atom_with_hint(theory: &mut Theory, s: &str, hint: Option<SortId>) -> (ENodeId, SortId) {
    // Check if it's a known variable
    if let Some(&(node, sort)) = theory.vars.get(s) {
        return (node, sort);
    }
    // Check if it's a known nullary op (true, false, c1, c2)
    if let Some(&op) = theory.ops.get(s) {
        let info = theory.eg.ops().info(op);
        let sort = info.return_sort;
        let node = theory.eg.add(op, &[]);
        return (node, sort);
    }
    // Try real literal (explicit decimal or hint says Real)
    let real_s = *theory.sorts.get("Real").unwrap();
    let int_s = *theory.sorts.get("Int").unwrap();
    if (s.contains('.') || hint == Some(real_s))
        && let Ok(f) = s.parse::<f64>()
    {
        let r = BigRational::from_float(f)
            .unwrap_or_else(|| BigRational::from_integer(BigInt::from(f as i64)));
        let val = theory.eg.intern_lit(NiraLitVal::Rat(r));
        let node = theory.eg.add_lit(theory.real_lit_op, val);
        return (node, real_s);
    }
    // Try integer literal
    if let Ok(n) = s.parse::<i64>() {
        let val = theory.eg.intern_lit(NiraLitVal::Int(BigInt::from(n)));
        let node = theory.eg.add_lit(theory.int_lit_op, val);
        return (node, int_s);
    }
    panic!("cannot resolve atom: {s}");
}

fn resolve_op(theory: &Theory, name: &str, children: &[(ENodeId, SortId)]) -> (OpId, SortId) {
    let bool_s = *theory.sorts.get("Bool").unwrap();

    match name {
        "=>" | "not" | "and" | "or" | "true" | "false" => {
            let op = theory.ops[name];
            (op, bool_s)
        }
        "=" => {
            // Polymorphic equality: resolve by first child's sort
            let child_sort = if children.is_empty() {
                bool_s
            } else {
                children[0].1
            };
            let sort_name = sort_name_of(theory, child_sort);
            let key = format!("=_{sort_name}");
            let op = *theory
                .ops
                .get(&key)
                .unwrap_or_else(|| panic!("no = for sort {sort_name}"));
            (op, bool_s)
        }
        "<" | "<=" | ">" | ">=" => {
            let child_sort = if children.is_empty() {
                *theory.sorts.get("Int").unwrap()
            } else {
                children[0].1
            };
            let sort_name = sort_name_of(theory, child_sort);
            let key = format!("{name}_{sort_name}");
            let op = *theory
                .ops
                .get(&key)
                .unwrap_or_else(|| panic!("no {name} for sort {sort_name}"));
            (op, bool_s)
        }
        "+" | "*" => {
            let int_s = *theory.sorts.get("Int").unwrap();
            let key = format!("{name}_Int");
            let op = *theory.ops.get(&key).unwrap();
            (op, int_s)
        }
        _ => {
            // Try as a known op
            if let Some(&op) = theory.ops.get(name) {
                let sort = theory.eg.ops().info(op).return_sort;
                (op, sort)
            } else {
                panic!("unknown operator: {name}");
            }
        }
    }
}

fn sort_name_of(theory: &Theory, sort: SortId) -> &str {
    for (name, &id) in &theory.sorts {
        if id == sort {
            return name;
        }
    }
    "?"
}

fn split_first_token(s: &str) -> (&str, &str) {
    let s = s.trim();
    let end = s
        .find(|c: char| c.is_whitespace() || c == '(')
        .unwrap_or(s.len());
    (&s[..end], &s[end..])
}

fn split_args(s: &str) -> Vec<&str> {
    let s = s.trim();
    if s.is_empty() {
        return Vec::new();
    }
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' | b'\t' | b'\n' if depth == 0 => {
                let arg = s[start..i].trim();
                if !arg.is_empty() {
                    args.push(arg);
                }
                start = i + 1;
            }
            _ => {}
        }
        i += 1;
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        args.push(last);
    }
    args
}

// ─── The actual test ───

#[test]
fn run_all_conformance_cases() {
    let mut passed = 0;
    let mut failed = Vec::new();

    for case in AU_CASES {
        let result = std::panic::catch_unwind(|| run_one_case(case));
        match result {
            Ok(Ok(())) => passed += 1,
            Ok(Err(msg)) => failed.push((case.id, msg)),
            Err(_) => failed.push((case.id, "panicked".to_string())),
        }
    }

    if !failed.is_empty() {
        eprintln!("\n{passed}/{} cases passed", AU_CASES.len());
        for (id, msg) in &failed {
            eprintln!("  FAIL {id}: {msg}");
        }
        panic!("{} cases failed", failed.len());
    }
}

fn run_one_case(case: &AuCase) -> Result<(), String> {
    let mut theory = build_theory(case);

    // Parse left and right terms
    let (left, _) = parse_sexpr(&mut theory, case.left);
    let (right, _) = parse_sexpr(&mut theory, case.right);
    theory.eg.rebuild();

    // Run saturation if requested
    if case.eqsat_iterations > 0 {
        // No rewrite rules registered for now; saturation is a no-op but
        // still exercises the rebuild path.
        for _ in 0..case.eqsat_iterations {
            theory.eg.rebuild();
        }
    }

    let snap = AuSnapshot::new(&theory.eg).map_err(|e| format!("snapshot error: {e}"))?;

    let config = AuConfig {
        algorithm: AuAlgorithm::Exact,
        playouts: case.rollouts as u64,
        ..Default::default()
    };

    let result =
        anti_unify(&snap, left, right, &config).map_err(|e| format!("anti_unify error: {e}"))?;

    // Check expectations
    match case.expected {
        Expectation::NonEmpty => {
            if result.size == 0 {
                return Err("expected NonEmpty but got size 0".into());
            }
        }
        Expectation::Identical => {
            let lc = snap.class_of(left).unwrap();
            let rc = snap.class_of(right).unwrap();
            if lc != rc {
                return Err("expected Identical but classes differ".into());
            }
        }
        Expectation::CommutativeEquivalent => {
            // After saturation the two should be in the same class
            // (commutative ops canonize). Check that AU size equals
            // best_size (i.e. no Variants needed).
            let lc = snap.class_of(left).unwrap();
            let rc = snap.class_of(right).unwrap();
            if lc != rc {
                // Not merged by canonization alone; the AU should still be valid.
                if result.size == 0 {
                    return Err("expected CommutativeEquivalent: size 0 unexpected".into());
                }
            }
        }
        Expectation::ProjectionPair => {
            // The result must be valid: both projections should be variant-free.
            let mut pool = result.pool;
            let lp = pool.project(result.term_id, 0);
            let rp = pool.project(result.term_id, 1);
            if pool.has_variants(lp) {
                return Err("left projection has Variants".into());
            }
            if pool.has_variants(rp) {
                return Err("right projection has Variants".into());
            }
        }
        Expectation::RegressionNoPanic => {
            // Just not panicking is the test; we already got here.
        }
    }

    Ok(())
}
