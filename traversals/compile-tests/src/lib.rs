use semi_persistent_traversals::rec_family;

rec_family! {
    family External => ExternalStore;
    enum Expr { Lit(i64), Add(Expr, Expr) }
    enum Stmt { Print(Expr) }
}

#[test]
fn macro_expansion_needs_only_the_public_crate() {
    let mut store = ExternalStore::new();
    let left = store.push_expr(ExprNode::Lit(1));
    let right = store.push_expr(ExprNode::Lit(2));
    let root = store.push_expr(ExprNode::Add(left, right));

    let result = store.fold(
        ExternalStoreRoot::Expr(root),
        |node: ExprNodeMapped<i64>| match node {
            ExprNodeMapped::Lit(value) => value,
            ExprNodeMapped::Add(left, right) => left + right,
        },
        |_: StmtNodeMapped<i64>| (),
    );

    assert_eq!(result.unwrap_expr(), 3);
}
