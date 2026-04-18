// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tests for parser: AC patterns, A patterns, ACI patterns,
//! multiplicity specs, rest variables, and RHS comprehensions.

use semi_persistent_egraph::ast::*;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::surface_ast::*;

fn parse_ok(src: &str) -> Vec<SurfaceCommand> {
    parse_program_v2(src).unwrap_or_else(|e| panic!("parse failed: {e}\nsrc: {src}"))
}

fn first_rewrite(cmds: &[SurfaceCommand]) -> (&SurfacePattern, &RhsTerm) {
    match &cmds[cmds.len() - 1] {
        SurfaceCommand::Rewrite { lhs, rhs, .. } => (lhs, rhs),
        other => panic!("expected Rewrite, got: {other:?}"),
    }
}

fn app_children(pat: &SurfacePattern) -> &[SurfacePatChild] {
    match pat {
        SurfacePattern::App { children, .. } => children,
        _ => panic!("expected App, got: {pat:?}"),
    }
}

fn app_prefix(pat: &SurfacePattern) -> Option<&str> {
    match pat {
        SurfacePattern::App {
            prefix: Some((n, _)),
            ..
        } => Some(n.as_str()),
        SurfacePattern::App { prefix: None, .. } => None,
        _ => panic!("expected App"),
    }
}

fn app_suffix(pat: &SurfacePattern) -> Option<&str> {
    match pat {
        SurfacePattern::App {
            suffix: Some((n, _)),
            ..
        } => Some(n.as_str()),
        SurfacePattern::App { suffix: None, .. } => None,
        _ => panic!("expected App"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// AC patterns: multiplicity specs
// ═══════════════════════════════════════════════════════════════════

#[test]
fn ac_implicit_mult() {
    let cmds = parse_ok("(rewrite (Add x y) z)");
    let (lhs, _) = first_rewrite(&cmds);
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 2);
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Var(n, _)) if n == "x"));
    assert!(matches!(&ch[1], SurfacePatChild::Elem(SurfacePattern::Var(n, _)) if n == "y"));
}

#[test]
fn ac_exact_mult() {
    let cmds = parse_ok("(rewrite (Add x:2) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 1);
    assert!(matches!(&ch[0], SurfacePatChild::ElemMult(
        SurfacePattern::Var(n, _), MultSpec::Exact(2)
    ) if n == "x"));
}

#[test]
fn ac_bind_mult() {
    let cmds = parse_ok("(rewrite (Add x:k) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(&ch[0], SurfacePatChild::ElemMult(
        SurfacePattern::Var(n, _),
        MultSpec::Var { name, constraint: None }
    ) if n == "x" && name == "k"));
}

#[test]
fn ac_constrained_ge() {
    let cmds = parse_ok("(rewrite (Add x:k>=2) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(&ch[0], SurfacePatChild::ElemMult(
        SurfacePattern::Var(n, _),
        MultSpec::Var { name, constraint: Some((CmpOp::Ge, 2)) }
    ) if n == "x" && name == "k"));
}

#[test]
fn ac_constrained_le() {
    let cmds = parse_ok("(rewrite (Add x:k<=5) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Le, 5)),
                ..
            }
        )
    ));
}

#[test]
fn ac_constrained_gt() {
    let cmds = parse_ok("(rewrite (Add x:k>1) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Gt, 1)),
                ..
            }
        )
    ));
}

#[test]
fn ac_constrained_lt() {
    let cmds = parse_ok("(rewrite (Add x:k<10) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Lt, 10)),
                ..
            }
        )
    ));
}

#[test]
fn ac_constrained_eq() {
    let cmds = parse_ok("(rewrite (Add x:k==4) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Eq, 4)),
                ..
            }
        )
    ));
}

#[test]
fn ac_constrained_ne() {
    let cmds = parse_ok("(rewrite (Add x:k!=1) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Ne, 1)),
                ..
            }
        )
    ));
}

// ═══════════════════════════════════════════════════════════════════
// Rest variables
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rest_suffix() {
    let cmds = parse_ok("(rewrite (Add (Zero) ..rest) (Add ..rest))");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert_eq!(app_suffix(lhs), Some("rest"));
    assert!(app_prefix(lhs).is_none());
}

#[test]
fn rest_prefix() {
    let cmds = parse_ok("(rewrite (Seq ..pre x) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert_eq!(app_prefix(lhs), Some("pre"));
    assert!(app_suffix(lhs).is_none());
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Var(n, _)) if n == "x"));
}

#[test]
fn rest_both() {
    let cmds = parse_ok("(rewrite (Seq ..pre x ..suf) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert_eq!(app_prefix(lhs), Some("pre"));
    assert_eq!(app_suffix(lhs), Some("suf"));
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Var(n, _)) if n == "x"));
}

#[test]
fn ac_mult_with_rest() {
    let cmds = parse_ok("(rewrite (Add x:k>=2 ..rest) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert!(matches!(&ch[0], SurfacePatChild::ElemMult(..)));
    assert_eq!(app_suffix(lhs), Some("rest"));
}

#[test]
fn ac_multiple_elems_with_rest() {
    let cmds = parse_ok("(rewrite (Add x:2 y:k>=1 ..rest) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 2);
    assert!(matches!(
        &ch[0],
        SurfacePatChild::ElemMult(_, MultSpec::Exact(2))
    ));
    assert!(matches!(
        &ch[1],
        SurfacePatChild::ElemMult(
            _,
            MultSpec::Var {
                constraint: Some((CmpOp::Ge, 1)),
                ..
            }
        )
    ));
    assert_eq!(app_suffix(lhs), Some("rest"));
}

// ═══════════════════════════════════════════════════════════════════
// ACI patterns (no mult allowed)
// ═══════════════════════════════════════════════════════════════════

#[test]
fn aci_plain_elems() {
    let cmds = parse_ok("(rewrite (Or x y) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 2);
}

#[test]
fn aci_with_rest() {
    let cmds = parse_ok("(rewrite (Or x ..rest) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert_eq!(app_suffix(lhs), Some("rest"));
}

// ═══════════════════════════════════════════════════════════════════
// A patterns (sequence)
// ═══════════════════════════════════════════════════════════════════

#[test]
fn a_exact() {
    let cmds = parse_ok("(rewrite (Seq x y z) w)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 3);
}

#[test]
fn a_prefix_rest() {
    let cmds = parse_ok("(rewrite (Seq ..pre x y) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 2);
    assert_eq!(app_prefix(lhs), Some("pre"));
}

#[test]
fn a_suffix_rest() {
    let cmds = parse_ok("(rewrite (Seq x y ..suf) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 2);
    assert_eq!(app_suffix(lhs), Some("suf"));
}

#[test]
fn a_both_rests() {
    let cmds = parse_ok("(rewrite (Seq ..pre x ..suf) z)");
    let lhs = first_rewrite(&cmds).0;
    let ch = app_children(lhs);
    assert_eq!(ch.len(), 1);
    assert_eq!(app_prefix(lhs), Some("pre"));
    assert_eq!(app_suffix(lhs), Some("suf"));
}

// ═══════════════════════════════════════════════════════════════════
// Plain / Commutative patterns
// ═══════════════════════════════════════════════════════════════════

#[test]
fn plain_nullary() {
    let cmds = parse_ok("(rewrite (Zero) x)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 0);
}

#[test]
fn plain_binary() {
    let cmds = parse_ok("(rewrite (f x y) z)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 2);
}

#[test]
fn nested_patterns() {
    let cmds = parse_ok("(rewrite (f (g x) (h y z)) w)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert_eq!(ch.len(), 2);
    match &ch[0] {
        SurfacePatChild::Elem(SurfacePattern::App { op, children, .. }) => {
            assert_eq!(op, "g");
            assert_eq!(children.len(), 1);
        }
        other => panic!("expected nested App, got: {other:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Literals in patterns
// ═══════════════════════════════════════════════════════════════════

#[test]
fn literal_int() {
    let cmds = parse_ok("(rewrite (f 42) x)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Lit(v, _)) if v == "42"));
}

#[test]
fn literal_bool() {
    let cmds = parse_ok("(rewrite (f true) x)");
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Lit(v, _)) if v == "true"));
}

#[test]
fn literal_string() {
    let cmds = parse_ok(r#"(rewrite (f "hello") x)"#);
    let ch = app_children(first_rewrite(&cmds).0);
    assert!(matches!(&ch[0], SurfacePatChild::Elem(SurfacePattern::Lit(v, _)) if v == "\"hello\""));
}

// ═══════════════════════════════════════════════════════════════════
// :when and :subsume
// ═══════════════════════════════════════════════════════════════════

#[test]
fn when_clause() {
    let cmds = parse_ok("(rewrite (f x) x :when ((g x)))");
    match &cmds[0] {
        SurfaceCommand::Rewrite { when, .. } => assert_eq!(when.len(), 1),
        _ => panic!("expected Rewrite"),
    }
}

#[test]
fn subsume_flag() {
    let cmds = parse_ok("(rewrite (f x) x :subsume)");
    match &cmds[0] {
        SurfaceCommand::Rewrite { subsume, .. } => assert!(*subsume),
        _ => panic!("expected Rewrite"),
    }
}

#[test]
fn when_and_subsume() {
    let cmds = parse_ok("(rewrite (f x) x :when ((g x)) :subsume)");
    match &cmds[0] {
        SurfaceCommand::Rewrite { when, subsume, .. } => {
            assert_eq!(when.len(), 1);
            assert!(*subsume);
        }
        _ => panic!("expected Rewrite"),
    }
}
