// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use semi_persistent_traversals::rec_family;

rec_family! {
    family Lang => LangStore;

    enum Stmt { Let(String, Expr), Print(Expr), Noop }
    enum Expr { Lit(i64), Var(String), Add(Expr, Expr) }
}

#[test]
fn quick_example_uses_per_sort_mapped_parameters() {
    let mut store = LangStore::new();
    let one = store.push_expr(ExprNode::Lit(1));
    let two = store.push_expr(ExprNode::Lit(2));
    let sum = store.push_expr(ExprNode::Add(one, two));
    let bind = store.push_stmt(StmtNode::Let("x".into(), sum));

    let result = store.fold(
        LangStoreRoot::Stmt(bind),
        |stmt: StmtNodeMapped<i64>| match stmt {
            StmtNodeMapped::Let(name, value) => format!("{name} = {value}"),
            StmtNodeMapped::Print(value) => format!("print({value})"),
            StmtNodeMapped::Noop => "noop".into(),
        },
        |expr: ExprNodeMapped<i64>| match expr {
            ExprNodeMapped::Lit(value) => value,
            ExprNodeMapped::Var(_) => 0,
            ExprNodeMapped::Add(left, right) => left + right,
        },
    );

    assert_eq!(result.unwrap_stmt(), "x = 3");
}
