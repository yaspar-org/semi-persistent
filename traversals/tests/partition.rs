// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]

use semi_persistent_traversals::*;
use semi_persistent_traversals_derive::partition;

partition! {
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
    let result = store.fold(
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
    let one = store.push_expr(ExprNode::Lit(1));
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
        |expr: ExprNodeMapped<bool, bool>| Ok(match expr {
            _ => false,
        }),
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
    let root = store.unfold(
        LangStoreSeed::Stmt(3i32),
        |seed| match seed {
            LangStoreSeed::Stmt(n) if n <= 0 => {
                LangStoreLayer::Stmt(
                    StmtNode::Print(ExprId(0)),
                    vec![LangStoreSeed::Expr(n)],
                )
            }
            LangStoreSeed::Stmt(n) => {
                LangStoreLayer::Stmt(
                    StmtNode::Seq(StmtId(0), StmtId(0)),
                    vec![LangStoreSeed::Stmt(n - 1), LangStoreSeed::Stmt(n - 1)],
                )
            }
            LangStoreSeed::Expr(n) => {
                LangStoreLayer::Expr(ExprNode::Lit(n as i64), vec![])
            }
        },
    );
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
partition! {
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
    let sum = s.push_vexpr(VExprNode::Add(Variadic::Resolved(smallvec::smallvec![one, two, three])));
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
    let one = s.push_vexpr(VExprNode::Lit(1));
    let two = s.push_vexpr(VExprNode::Lit(2));
    // Use alloc to test pool-based variadic
    let span = s.alloc_vstmt_vstmt(&[]);
    let empty_block = s.push_vstmt(VStmtNode::Block(span));
    assert_eq!(s.len_vstmt(), 1);
    assert_eq!(s.len_vexpr(), 2);
}

// Comparison test: same family, same algebras, verify identical fold results
// between coproduct (rec_family!) and partitioned (partition!) layouts
#[test]
fn partition_matches_coproduct() {
    use semi_persistent_traversals_derive::rec_family;

    rec_family! {
        family CmpLang;
        enum CmpStmt {
            Assign(String, CmpExpr),
            Seq(CmpStmt, CmpStmt),
            Print(CmpExpr),
        }
        enum CmpExpr {
            Var(String),
            Lit(i64),
            Add(CmpExpr, CmpExpr),
        }
    }

    partition! {
        family CmpLang => CmpStore;
        enum CmpStmt {
            Assign(String, CmpExpr),
            Seq(CmpStmt, CmpStmt),
            Print(CmpExpr),
        }
        enum CmpExpr {
            Var(String),
            Lit(i64),
            Add(CmpExpr, CmpExpr),
        }
    }

    // Build same tree in both layouts
    // Coproduct
    let mut ca = Arena::<CmpLang<usize, usize>>::new();
    let c_one = ca.push(CmpLang::CmpExprLit(1));
    let c_two = ca.push(CmpLang::CmpExprLit(2));
    let c_sum = ca.push(CmpLang::CmpExprAdd(c_one.0, c_two.0));
    let c_asgn = ca.push(CmpLang::CmpStmtAssign("x".into(), c_sum.0));
    let c_xref = ca.push(CmpLang::CmpExprVar("x".into()));
    let c_pr = ca.push(CmpLang::CmpStmtPrint(c_xref.0));
    let c_root = ca.push(CmpLang::CmpStmtSeq(c_asgn.0, c_pr.0));

    // Partitioned
    let mut ps = CmpStore::new();
    let p_one = ps.push_cmpexpr(CmpExprNode::Lit(1));
    let p_two = ps.push_cmpexpr(CmpExprNode::Lit(2));
    let p_sum = ps.push_cmpexpr(CmpExprNode::Add(p_one, p_two));
    let p_asgn = ps.push_cmpstmt(CmpStmtNode::Assign("x".into(), p_sum));
    let p_xref = ps.push_cmpexpr(CmpExprNode::Var("x".into()));
    let p_pr = ps.push_cmpstmt(CmpStmtNode::Print(p_xref));
    let p_root = ps.push_cmpstmt(CmpStmtNode::Seq(p_asgn, p_pr));

    // Fold: size
    let c_size = fold_cmplang_multi(
        &ca, c_root,
        |stmt: CmpStmt<usize, usize>| match stmt {
            CmpStmt::Assign(_, e) => 1 + e,
            CmpStmt::Seq(l, r) => 1 + l + r,
            CmpStmt::Print(e) => 1 + e,
        },
        |expr: CmpExpr<usize>| match expr {
            CmpExpr::Var(_) | CmpExpr::Lit(_) => 1,
            CmpExpr::Add(l, r) => 1 + l + r,
        },
    );

    let p_size = ps.fold(
        CmpStoreRoot::CmpStmt(p_root),
        |stmt: CmpStmtNodeMapped<usize, usize>| match stmt {
            CmpStmtNodeMapped::Assign(_, e) => 1 + e,
            CmpStmtNodeMapped::Seq(l, r) => 1 + l + r,
            CmpStmtNodeMapped::Print(e) => 1 + e,
        },
        |expr: CmpExprNodeMapped<usize>| match expr {
            CmpExprNodeMapped::Var(_) | CmpExprNodeMapped::Lit(_) => 1,
            CmpExprNodeMapped::Add(l, r) => 1 + l + r,
        },
    );

    let c_size_val = c_size.unwrap_cmpstmt();
    let p_size_val = p_size.unwrap_cmpstmt();
    assert_eq!(c_size_val, p_size_val);
    assert_eq!(p_size_val, 7usize);

    // Fold: show
    let c_show = fold_cmplang_multi(
        &ca, c_root,
        |stmt: CmpStmt<String, String>| match stmt {
            CmpStmt::Assign(name, val) => format!("{name} = {val}"),
            CmpStmt::Seq(l, r) => format!("{l}; {r}"),
            CmpStmt::Print(e) => format!("print({e})"),
        },
        |expr: CmpExpr<String>| match expr {
            CmpExpr::Var(name) => name,
            CmpExpr::Lit(n) => n.to_string(),
            CmpExpr::Add(l, r) => format!("({l} + {r})"),
        },
    );

    let p_show = ps.fold(
        CmpStoreRoot::CmpStmt(p_root),
        |stmt: CmpStmtNodeMapped<String, String>| match stmt {
            CmpStmtNodeMapped::Assign(name, val) => format!("{name} = {val}"),
            CmpStmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
            CmpStmtNodeMapped::Print(e) => format!("print({e})"),
        },
        |expr: CmpExprNodeMapped<String>| match expr {
            CmpExprNodeMapped::Var(name) => name,
            CmpExprNodeMapped::Lit(n) => n.to_string(),
            CmpExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
        },
    );

    let c_show_val = c_show.unwrap_cmpstmt();
    let p_show_val = p_show.unwrap_cmpstmt();
    assert_eq!(c_show_val, p_show_val);
    assert_eq!(p_show_val, "x = (1 + 2); print(x)");
}
