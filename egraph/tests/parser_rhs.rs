// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tests for parser: RHS comprehensions and splices.

use semi_persistent_egraph::ast::*;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::surface_ast::*;

fn parse_ok(src: &str) -> Vec<SurfaceCommand> {
    parse_program_v2(src).unwrap_or_else(|e| panic!("parse failed: {e}\nsrc: {src}"))
}

fn first_rhs(cmds: &[SurfaceCommand]) -> &RhsTerm {
    match &cmds[cmds.len() - 1] {
        SurfaceCommand::Rewrite { rhs, .. } => rhs,
        other => panic!("expected Rewrite, got: {other:?}"),
    }
}

fn rhs_children(rhs: &RhsTerm) -> &[RhsChild] {
    match rhs {
        RhsTerm::App { children, .. } => children,
        _ => panic!("expected App, got: {rhs:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Plain splice: ..name
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rhs_splice_plain() {
    let cmds = parse_ok("(rewrite (f x ..rest) (g ..rest))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 1);
    assert!(matches!(&ch[0], RhsChild::Splice(n, _) if n == "rest"));
}

#[test]
fn rhs_splice_with_terms() {
    let cmds = parse_ok("(rewrite (f x ..rest) (g x ..rest y))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 3);
    assert!(matches!(&ch[0], RhsChild::Term(RhsTerm::Var(n, _)) if n == "x"));
    assert!(matches!(&ch[1], RhsChild::Splice(n, _) if n == "rest"));
    assert!(matches!(&ch[2], RhsChild::Term(RhsTerm::Var(n, _)) if n == "y"));
}

// ═══════════════════════════════════════════════════════════════════
// Set comprehension: ..{body for v in src}
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rhs_set_comp() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..{(h v) for v in rest}))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 1);
    match &ch[0] {
        RhsChild::SetComp {
            body,
            var,
            source,
            filter,
            ..
        } => {
            assert!(matches!(body.as_ref(), RhsTerm::App { op, .. } if op == "h"));
            assert_eq!(var, "v");
            assert_eq!(source, "rest");
            assert!(filter.is_none());
        }
        other => panic!("expected SetComp, got: {other:?}"),
    }
}

#[test]
fn rhs_set_comp_with_filter() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..{(h v) for v in rest if (p v)}))");
    let ch = rhs_children(first_rhs(&cmds));
    match &ch[0] {
        RhsChild::SetComp { filter, .. } => {
            assert!(filter.is_some());
            let f = filter.as_ref().unwrap();
            assert!(matches!(f.as_ref(), RhsTerm::App { op, .. } if op == "p"));
        }
        other => panic!("expected SetComp, got: {other:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Multiset comprehension: ..{body:mult for v:k in src}
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rhs_mset_comp() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..{(h v):k for v:k in rest}))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 1);
    match &ch[0] {
        RhsChild::MsetComp {
            body,
            mult,
            var,
            mult_var,
            source,
            filter,
            ..
        } => {
            assert!(matches!(body.as_ref(), RhsTerm::App { op, .. } if op == "h"));
            assert!(matches!(mult, MultExpr::Var(n) if n == "k"));
            assert_eq!(var, "v");
            assert_eq!(mult_var, "k");
            assert_eq!(source, "rest");
            assert!(filter.is_none());
        }
        other => panic!("expected MsetComp, got: {other:?}"),
    }
}

#[test]
fn rhs_mset_comp_lit_mult() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..{(h v):2 for v:k in rest}))");
    let ch = rhs_children(first_rhs(&cmds));
    match &ch[0] {
        RhsChild::MsetComp { mult, .. } => {
            assert!(matches!(mult, MultExpr::Lit(2)));
        }
        other => panic!("expected MsetComp, got: {other:?}"),
    }
}

#[test]
fn rhs_mset_comp_with_filter() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..{(h v):k for v:k in rest if (p v)}))");
    let ch = rhs_children(first_rhs(&cmds));
    match &ch[0] {
        RhsChild::MsetComp { filter, .. } => {
            assert!(filter.is_some());
        }
        other => panic!("expected MsetComp, got: {other:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Sequence comprehension: ..[body for v in src]
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rhs_seq_comp() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..[v for v in rest]))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 1);
    match &ch[0] {
        RhsChild::SeqComp {
            body,
            var,
            source,
            filter,
            ..
        } => {
            assert!(matches!(body.as_ref(), RhsTerm::Var(n, _) if n == "v"));
            assert_eq!(var, "v");
            assert_eq!(source, "rest");
            assert!(filter.is_none());
        }
        other => panic!("expected SeqComp, got: {other:?}"),
    }
}

#[test]
fn rhs_seq_comp_with_filter() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..[(h v) for v in rest if (p v)]))");
    let ch = rhs_children(first_rhs(&cmds));
    match &ch[0] {
        RhsChild::SeqComp { filter, .. } => {
            assert!(filter.is_some());
        }
        other => panic!("expected SeqComp, got: {other:?}"),
    }
}

#[test]
fn rhs_seq_comp_nested_body() {
    let cmds = parse_ok("(rewrite (f ..rest) (g ..[(h (k v)) for v in rest]))");
    let ch = rhs_children(first_rhs(&cmds));
    match &ch[0] {
        RhsChild::SeqComp { body, .. } => {
            assert!(matches!(body.as_ref(), RhsTerm::App { op, .. } if op == "h"));
        }
        other => panic!("expected SeqComp, got: {other:?}"),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Mixed RHS: terms + splices + comprehensions
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rhs_mixed() {
    let cmds = parse_ok("(rewrite (f x ..rest) (g x ..{(h v) for v in rest} (Zero)))");
    let ch = rhs_children(first_rhs(&cmds));
    assert_eq!(ch.len(), 3);
    assert!(matches!(&ch[0], RhsChild::Term(RhsTerm::Var(n, _)) if n == "x"));
    assert!(matches!(&ch[1], RhsChild::SetComp { .. }));
    assert!(matches!(&ch[2], RhsChild::Term(RhsTerm::App { op, .. }) if op == "Zero"));
}

// ═══════════════════════════════════════════════════════════════════
// Commands: rule with actions
// ═══════════════════════════════════════════════════════════════════

#[test]
fn rule_with_actions() {
    let cmds = parse_ok("(rule ((f x) (g y)) ((union x y) (h x y)))");
    match &cmds[0] {
        SurfaceCommand::Rule { body, head } => {
            assert_eq!(body.len(), 2);
            assert_eq!(head.len(), 2);
            assert!(matches!(&head[0], Action::Union(..)));
            assert!(matches!(&head[1], Action::Insert(..)));
        }
        _ => panic!("expected Rule"),
    }
}

#[test]
fn rule_with_set_action() {
    let cmds = parse_ok("(rule ((f x)) ((set (g x) y)))");
    match &cmds[0] {
        SurfaceCommand::Rule { head, .. } => {
            assert!(matches!(&head[0], Action::Set { func, .. } if func == "g"));
        }
        _ => panic!("expected Rule"),
    }
}
