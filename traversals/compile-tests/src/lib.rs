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

rec_family! {
    #[smart_constructors]
    family TraitMethodCollision => TraitMethodCollisionStore;
    enum Item { Clone, CloneFrom, Drop }
    enum Root { Item(Item) }
}

#[test]
fn smart_constructors_do_not_shadow_standard_methods() {
    let mut store = TraitMethodCollisionStore::new();
    let cloned = store.clone();
    let mut assigned = TraitMethodCollisionStore::new();
    assigned.clone_from(&cloned);

    assert_eq!(
        std::any::type_name_of_val(&cloned),
        std::any::type_name::<TraitMethodCollisionStore>()
    );
    assert_eq!(
        std::any::type_name_of_val(&assigned),
        std::any::type_name::<TraitMethodCollisionStore>()
    );
    assert_eq!(store.clone_(), ItemId(0));
    assert_eq!(store.clone_from_(), ItemId(1));
    assert_eq!(store.drop_(), ItemId(2));
}

rec_family! {
    family FloatData => FloatDataStore;
    enum FloatExpr {
        F64(f64),
        F32(f32),
        Series(f64, Variadic<FloatExpr>),
    }
    enum FloatStmt { Print(FloatExpr) }
}

#[test]
fn bare_float_data_has_bitwise_structural_identity() {
    let mut plain = FloatDataStore::new();
    let value = plain.push_floatexpr(FloatExprNode::F64(1.5));
    let _print = plain.push_floatstmt(FloatStmtNode::Print(value));

    let mut dedup = FloatDataStore::new_dedup();
    let nan = f64::from_bits(0x7ff8_0000_0000_0001);
    let same_nan = dedup.push_floatexpr(FloatExprNode::F64(nan));
    let duplicate_nan = dedup.push_floatexpr(FloatExprNode::F64(nan));
    let other_nan = dedup.push_floatexpr(FloatExprNode::F64(f64::from_bits(0x7ff8_0000_0000_0002)));
    let positive_zero = dedup.push_floatexpr(FloatExprNode::F64(0.0));
    let negative_zero = dedup.push_floatexpr(FloatExprNode::F64(-0.0));
    let f32_value = dedup.push_floatexpr(FloatExprNode::F32(f32::NAN));
    let f32_duplicate = dedup.push_floatexpr(FloatExprNode::F32(f32::NAN));
    let first_children = dedup.alloc_floatexpr_floatexpr(&[same_nan, positive_zero]);
    let first_series = dedup.push_floatexpr(FloatExprNode::Series(nan, first_children));
    let second_children = dedup.alloc_floatexpr_floatexpr(&[same_nan, positive_zero]);
    let second_series = dedup.push_floatexpr(FloatExprNode::Series(nan, second_children));

    assert_eq!(same_nan, duplicate_nan);
    assert_ne!(same_nan, other_nan);
    assert_ne!(positive_zero, negative_zero);
    assert_eq!(f32_value, f32_duplicate);
    assert_eq!(first_series, second_series);
    assert_eq!(
        dedup.get_floatexpr_resolved(first_series),
        dedup.get_floatexpr_resolved(second_series)
    );
}

rec_family! {
    #[smart_constructors]
    family ConstructorNames => ConstructorNamesStore;
    enum CollisionStmt { Mark, Fold(CollisionExpr) }
    enum CollisionExpr { New, PushCollisionexpr(i64) }
}

#[test]
fn smart_constructors_escape_generated_store_methods() {
    let mut store = ConstructorNamesStore::new();
    let new_node = store.new_();
    let pushed_node = store.push_collisionexpr_(7);
    let mark_node = store.mark_();
    let fold_node = store.fold_(pushed_node);
    let snapshot = store.mark();

    assert_eq!(new_node, CollisionExprId(0));
    assert_eq!(pushed_node, CollisionExprId(1));
    assert_eq!(mark_node, CollisionStmtId(0));
    assert_eq!(fold_node, CollisionStmtId(1));
    store.restore(&snapshot);
}

mod readme_quick_start {
    #![allow(dead_code)]

    use semi_persistent_traversals::rec_family;

    rec_family! {
        family Lang => LangStore;

        enum Stmt { Let(String, Expr), Print(Expr), Noop }
        enum Expr { Lit(i64), Var(String), Add(Expr, Expr) }
    }

    #[test]
    fn mapped_enums_only_take_the_sort_parameters_they_use() {
        let mut s = LangStore::new();
        let one = s.push_expr(ExprNode::Lit(1));
        let two = s.push_expr(ExprNode::Lit(2));
        let sum = s.push_expr(ExprNode::Add(one, two));
        let bind = s.push_stmt(StmtNode::Let("x".into(), sum));

        let result = s.fold(
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
}
