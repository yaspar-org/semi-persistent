// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]

use semi_persistent_traversals::*;
use semi_persistent_traversals_derive::rec_family;

rec_family! {
    family Lang => LangStore;
    enum Stmt {
        Assign(String, Expr),
        Seq(Stmt, Stmt),
        Print(Expr),
    }
    enum Expr {
        Var(String),
        Lit(i64),
        Add(Expr, Expr),
        Block(Stmt, Expr),
    }
}

fn build_sample() -> (LangStore, LangStoreRoot) {
    let mut s = LangStore::new();
    let one = s.push_expr(ExprNode::Lit(1));
    let two = s.push_expr(ExprNode::Lit(2));
    let sum = s.push_expr(ExprNode::Add(one, two));
    let asgn = s.push_stmt(StmtNode::Assign("x".to_string(), sum));
    let xref = s.push_expr(ExprNode::Var("x".to_string()));
    let pr = s.push_stmt(StmtNode::Print(xref));
    let root = s.push_stmt(StmtNode::Seq(asgn, pr));
    (s, LangStoreRoot::Stmt(root))
}

#[test]
fn partition_fold_show() {
    let (store, root) = build_sample();
    let result = store.fold(
        root,
        |stmt: StmtNodeMapped<String, String>| match stmt {
            StmtNodeMapped::Assign(name, val) => format!("{name} = {val}"),
            StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
            StmtNodeMapped::Print(e) => format!("print({e})"),
        },
        |expr: ExprNodeMapped<String, String>| match expr {
            ExprNodeMapped::Var(name) => name,
            ExprNodeMapped::Lit(n) => n.to_string(),
            ExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
            ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
        },
    );
    assert_eq!(result.unwrap_stmt(), "x = (1 + 2); print(x)");
}

#[test]
fn partition_fold_eval() {
    let (store, root) = build_sample();
    let _result = store.fold(
        root,
        |stmt: StmtNodeMapped<(), i64>| match stmt {
            StmtNodeMapped::Assign(_, _) => (),
            StmtNodeMapped::Seq(_, _) => (),
            StmtNodeMapped::Print(_) => (),
        },
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Var(_) => 0,
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            ExprNodeMapped::Block(_, e) => e,
        },
    );
    // Root is a Stmt, but let's fold from the sum expr
    let sum_id = ExprId(2); // Add(Lit(1), Lit(2))
    let result2 = store.fold(
        LangStoreRoot::Expr(sum_id),
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Var(_) => 0,
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            ExprNodeMapped::Block(_, e) => e,
        },
    );
    assert_eq!(result2.unwrap_expr(), 3);
}

#[test]
fn partition_fold_size() {
    let (store, root) = build_sample();
    let result = store.fold(
        root,
        |stmt: StmtNodeMapped<usize, usize>| match stmt {
            StmtNodeMapped::Assign(_, e) => 1 + e,
            StmtNodeMapped::Seq(l, r) => 1 + l + r,
            StmtNodeMapped::Print(e) => 1 + e,
        },
        |expr: ExprNodeMapped<usize, usize>| match expr {
            ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) => 1,
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Block(l, r) => 1 + l + r,
        },
    );
    assert_eq!(result.unwrap_stmt(), 7);
}

#[test]
fn partition_mark_restore() {
    let mut store = LangStore::new();
    let _one = store.push_expr(ExprNode::Lit(1));
    let mark = store.mark();
    let _two = store.push_expr(ExprNode::Lit(2));
    assert_eq!(store.len_expr(), 2);
    store.restore(&mark);
    assert_eq!(store.len_expr(), 1);
}

#[test]
fn partition_fold_all() {
    let (store, _root) = build_sample();
    let cache = store.fold_all(
        |stmt: StmtNodeMapped<usize, usize>| match stmt {
            StmtNodeMapped::Assign(_, e) => 1 + e,
            StmtNodeMapped::Seq(l, r) => 1 + l + r,
            StmtNodeMapped::Print(e) => 1 + e,
        },
        |expr: ExprNodeMapped<usize, usize>| match expr {
            ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) => 1,
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Block(l, r) => 1 + l + r,
        },
    );
    // Check individual nodes
    assert_eq!(cache[ExprId(0)], 1); // Lit(1)
    assert_eq!(cache[ExprId(2)], 3); // Add(Lit(1), Lit(2))
    assert_eq!(cache[StmtId(2)], 7); // Seq(Assign, Print)
}

#[test]
fn partition_transform() {
    let (store, root) = build_sample();
    let (store2, root2) = store.transform(
        root,
        |stmt| stmt, // identity for stmts
        |expr| match expr {
            ExprNode::Lit(n) => ExprNode::Lit(n * 10),
            other => other,
        },
    );
    let result = store2.fold(
        root2,
        |stmt: StmtNodeMapped<String, String>| match stmt {
            StmtNodeMapped::Assign(name, val) => format!("{name} = {val}"),
            StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
            StmtNodeMapped::Print(e) => format!("print({e})"),
        },
        |expr: ExprNodeMapped<String, String>| match expr {
            ExprNodeMapped::Var(name) => name,
            ExprNodeMapped::Lit(n) => n.to_string(),
            ExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
            ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
        },
    );
    assert_eq!(result.unwrap_stmt(), "x = (10 + 20); print(x)");
}

#[test]
fn partition_fold_short() {
    let (store, root) = build_sample();
    let result = store.fold_short(
        root,
        |stmt: StmtNodeMapped<bool, bool>| match stmt {
            StmtNodeMapped::Print(_) => Err(true), // short-circuit on Print
            _ => Ok(false),
        },
        |_: ExprNodeMapped<bool, bool>| Ok(false),
    );
    assert!(result.unwrap_stmt());
}

#[test]
fn partition_para() {
    let (store, root) = build_sample();
    let result = store.fold_with_ids(
        root,
        |stmt: StmtNodeMapped<(StmtId, String), (ExprId, String)>| match stmt {
            StmtNodeMapped::Assign(name, (_, val)) => format!("{name} = {val}"),
            StmtNodeMapped::Seq((_, l), (_, r)) => format!("{l}; {r}"),
            StmtNodeMapped::Print((_, e)) => format!("print({e})"),
        },
        |expr: ExprNodeMapped<(StmtId, String), (ExprId, String)>| match expr {
            ExprNodeMapped::Var(name) => name,
            ExprNodeMapped::Lit(n) => n.to_string(),
            ExprNodeMapped::Add((_, l), (_, r)) => format!("({l} + {r})"),
            ExprNodeMapped::Block((_, s), (_, e)) => format!("{{ {s}; {e} }}"),
        },
    );
    assert_eq!(result.unwrap_stmt(), "x = (1 + 2); print(x)");
}

#[test]
fn partition_unfold() {
    let mut store = LangStore::new();
    let root = store.unfold(LangStoreSeed::Stmt(3i32), |seed| match seed {
        LangStoreSeed::Stmt(n) if n <= 0 => {
            LangStoreLayer::Stmt(StmtNode::Print(ExprId(0)), vec![LangStoreSeed::Expr(n)])
        }
        LangStoreSeed::Stmt(n) => LangStoreLayer::Stmt(
            StmtNode::Seq(StmtId(0), StmtId(0)),
            vec![LangStoreSeed::Stmt(n - 1), LangStoreSeed::Stmt(n - 1)],
        ),
        LangStoreSeed::Expr(n) => LangStoreLayer::Expr(ExprNode::Lit(n as i64), vec![]),
    });
    let result = store.fold(
        root,
        |stmt: StmtNodeMapped<usize, usize>| match stmt {
            StmtNodeMapped::Assign(_, e) => 1 + e,
            StmtNodeMapped::Seq(l, r) => 1 + l + r,
            StmtNodeMapped::Print(e) => 1 + e,
        },
        |expr: ExprNodeMapped<usize, usize>| match expr {
            ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) => 1,
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Block(l, r) => 1 + l + r,
        },
    );
    assert_eq!(result.unwrap_stmt(), 23);
}

#[test]
fn partition_histo() {
    let (store, root) = build_sample();
    let result = store.fold_with_history(
        root,
        |stmt: StmtNodeMapped<Ann<usize>, Ann<usize>>| match stmt {
            StmtNodeMapped::Assign(_, e) => 1 + e.value,
            StmtNodeMapped::Seq(l, r) => 1 + l.value.max(r.value),
            StmtNodeMapped::Print(e) => 1 + e.value,
        },
        |expr: ExprNodeMapped<Ann<usize>, Ann<usize>>| match expr {
            ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) => 0,
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Block(l, r) => 1 + l.value.max(r.value),
        },
    );
    // Tree: Seq(Assign("x", Add(Lit(1), Lit(2))), Print(Var("x")))
    // Depths: Lit=0, Add=1, Assign=2, Var=0, Print=1, Seq=max(2,1)+1=3
    assert_eq!(result.unwrap_stmt(), 3);
}

#[test]
fn partition_zygo() {
    let (store, root) = build_sample();
    // Aux: count nodes. Main: pretty-print with node count annotation.
    let result = store.fold_with_aux(
        root,
        // aux: count
        |stmt: StmtNodeMapped<usize, usize>| match stmt {
            StmtNodeMapped::Assign(_, e) => 1 + e,
            StmtNodeMapped::Seq(l, r) => 1 + l + r,
            StmtNodeMapped::Print(e) => 1 + e,
        },
        |expr: ExprNodeMapped<usize, usize>| match expr {
            ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) => 1,
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Block(l, r) => 1 + l + r,
        },
        // main: show
        |stmt: StmtNodeMapped<(String, usize), (String, usize)>| match stmt {
            StmtNodeMapped::Assign(name, (val, _)) => format!("{name} = {val}"),
            StmtNodeMapped::Seq((l, _), (r, _)) => format!("{l}; {r}"),
            StmtNodeMapped::Print((e, _)) => format!("print({e})"),
        },
        |expr: ExprNodeMapped<(String, usize), (String, usize)>| match expr {
            ExprNodeMapped::Var(name) => name,
            ExprNodeMapped::Lit(n) => n.to_string(),
            ExprNodeMapped::Add((l, _), (r, _)) => format!("({l} + {r})"),
            ExprNodeMapped::Block((s, _), (e, _)) => format!("{{ {s}; {e} }}"),
        },
    );
    assert_eq!(result.unwrap_stmt(), "x = (1 + 2); print(x)");
}

#[test]
fn partition_fold_with_original() {
    let (store, root) = build_sample();
    let result = store.fold_with_original(
        root,
        |orig: &StmtNode, mapped: StmtNodeMapped<String, String>| {
            let base = match mapped {
                StmtNodeMapped::Assign(name, val) => format!("{name} = {val}"),
                StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
                StmtNodeMapped::Print(e) => format!("print({e})"),
            };
            // Annotate with original variant name
            match orig {
                StmtNode::Seq(_, _) => format!("[seq:{base}]"),
                _ => base,
            }
        },
        |_orig: &ExprNode, mapped: ExprNodeMapped<String, String>| match mapped {
            ExprNodeMapped::Var(name) => name,
            ExprNodeMapped::Lit(n) => n.to_string(),
            ExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
            ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
        },
    );
    assert_eq!(result.unwrap_stmt(), "[seq:x = (1 + 2); print(x)]");
}

// Variadic family test
rec_family! {
    family VLang => VStore;
    enum VStmt { Assign(u32, VExpr), Block(Variadic<VStmt>) }
    enum VExpr { Lit(i64), Add(Variadic<VExpr>), Neg(VExpr) }
}

#[test]
fn partition_variadic_fold() {
    let mut s = VStore::new();
    let one = s.push_vexpr(VExprNode::Lit(1));
    let two = s.push_vexpr(VExprNode::Lit(2));
    let three = s.push_vexpr(VExprNode::Lit(3));
    let sum = s.push_vexpr(VExprNode::Add(Variadic::Resolved(smallvec::smallvec![
        one, two, three
    ])));
    let result = s.fold(
        VStoreRoot::VExpr(sum),
        |_: VStmtNodeMapped<(), i64>| (),
        |expr: VExprNodeMapped<i64>| match expr {
            VExprNodeMapped::Lit(n) => n,
            VExprNodeMapped::Add(xs) => xs.iter().sum(),
            VExprNodeMapped::Neg(x) => -x,
        },
    );
    assert_eq!(result.unwrap_vexpr(), 6);
}

#[test]
fn partition_variadic_pool() {
    let mut s = VStore::new();
    let _one = s.push_vexpr(VExprNode::Lit(1));
    let _two = s.push_vexpr(VExprNode::Lit(2));
    // Use alloc to test pool-based variadic
    let span = s.alloc_vstmt_vstmt(&[]);
    let _empty_block = s.push_vstmt(VStmtNode::Block(span));
    assert_eq!(s.len_vstmt(), 1);
    assert_eq!(s.len_vexpr(), 2);
}
