// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#[cfg(test)]
#[allow(clippy::enum_variant_names)]
mod tests {
    use semi_persistent_traversals::*;
    use semi_persistent_traversals_derive::rec_family;

    rec_family! {
        family Lang;

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

    type Ast = Arena<Lang<usize, usize>>;

    fn assign(a: &mut Ast, name: &str, val: Id) -> Id {
        a.push(Lang::StmtAssign(name.to_string(), val.0))
    }
    fn seq(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Lang::StmtSeq(l.0, r.0))
    }
    fn print_stmt(a: &mut Ast, e: Id) -> Id {
        a.push(Lang::StmtPrint(e.0))
    }
    fn var(a: &mut Ast, name: &str) -> Id {
        a.push(Lang::ExprVar(name.to_string()))
    }
    fn lit(a: &mut Ast, n: i64) -> Id {
        a.push(Lang::ExprLit(n))
    }
    fn add(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Lang::ExprAdd(l.0, r.0))
    }
    fn block(a: &mut Ast, s: Id, e: Id) -> Id {
        a.push(Lang::ExprBlock(s.0, e.0))
    }

    fn show(a: &Ast, root: Id) -> String {
        a.fold(root, |node: Lang<String, String>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Assign(name, val) => format!("{name} = {val}"),
                    Stmt::Seq(l, r) => format!("{l}; {r}"),
                    Stmt::Print(e) => format!("print({e})"),
                },
                |expr| match expr {
                    Expr::Var(name) => name,
                    Expr::Lit(n) => n.to_string(),
                    Expr::Add(l, r) => format!("({l} + {r})"),
                    Expr::Block(s, e) => format!("{{ {s}; {e} }}"),
                },
            )
        })
    }

    // x = 1 + 2; print(x)
    fn sample() -> (Ast, Id) {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let sum = add(&mut a, one, two);
        let asgn = assign(&mut a, "x", sum);
        let xref = var(&mut a, "x");
        let pr = print_stmt(&mut a, xref);
        let root = seq(&mut a, asgn, pr);
        (a, root)
    }

    // -- dispatch (uniform) tests -------------------------------------------

    #[test]
    fn cata_show() {
        let (a, root) = sample();
        assert_eq!(show(&a, root), "x = (1 + 2); print(x)");
    }

    #[test]
    fn cata_size() {
        let (a, root) = sample();
        let size = a.fold(root, |node: Lang<usize, usize>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Assign(_, e) => 1 + e,
                    Stmt::Seq(l, r) => 1 + l + r,
                    Stmt::Print(e) => 1 + e,
                },
                |expr| match expr {
                    Expr::Var(_) | Expr::Lit(_) => 1,
                    Expr::Add(l, r) | Expr::Block(l, r) => 1 + l + r,
                },
            )
        });
        assert_eq!(size, 7);
    }

    #[test]
    fn cross_sort_block() {
        let mut a = Ast::new();
        let val = lit(&mut a, 42);
        let asgn = assign(&mut a, "x", val);
        let xref = var(&mut a, "x");
        let root = block(&mut a, asgn, xref);
        assert_eq!(show(&a, root), "{ x = 42; x }");
    }

    #[test]
    fn ana_unfold_family() {
        let mut a = Ast::new();
        let root = unfold(&mut a, 3i32, |n| {
            if n <= 0 {
                (Lang::ExprLit(42), vec![])
            } else if n % 2 == 0 {
                (Lang::ExprAdd(0, 0), vec![n - 1, n - 1])
            } else {
                (Lang::StmtPrint(0), vec![n - 1])
            }
        });
        assert_eq!(show(&a, root), "print((print(42) + print(42)))");
    }

    #[test]
    fn from_sort_to_coproduct() {
        let s: Lang<usize, usize> = Stmt::Print(0).into();
        assert!(matches!(s, Lang::StmtPrint(0)));
        let e: Lang<usize, usize> = Expr::Lit(99).into();
        assert!(matches!(e, Lang::ExprLit(99)));
    }

    #[test]
    fn try_from_coproduct_to_sort() {
        let node: Lang<usize, usize> = Lang::StmtPrint(0);
        let stmt: Result<Stmt<usize, usize>, _> = node.try_into();
        assert!(matches!(stmt, Ok(Stmt::Print(0))));

        let node: Lang<usize, usize> = Lang::ExprLit(42);
        let stmt: Result<Stmt<usize, usize>, _> = node.try_into();
        assert!(stmt.is_err()); // wrong sort
        let expr: Result<Expr<usize, usize>, _> = stmt.unwrap_err().try_into();
        assert!(matches!(expr, Ok(Expr::Lit(42))));
    }

    #[test]
    fn build_with_sort_types() {
        // Use From to build trees with sort types instead of coproduct variants
        let mut a = Ast::new();
        let one = a.push(Expr::Lit(1).into());
        let two = a.push(Expr::Lit(2).into());
        let sum = a.push(Expr::Add(one.0, two.0).into());
        let asgn = a.push(Stmt::Assign("x".into(), sum.0).into());
        let xref = a.push(Expr::Var("x".into()).into());
        let pr = a.push(Stmt::Print(xref.0).into());
        let root = a.push(Stmt::Seq(asgn.0, pr.0).into());
        assert_eq!(show(&a, root), "x = (1 + 2); print(x)");
    }

    #[test]
    fn transform_with_projection() {
        let (a, root) = sample();
        // Use TryFrom to match on sort types in a transform
        let (a2, r2) = a.transform(root, |node| {
            if let Ok(Expr::Lit(n)) = node.clone().try_into() {
                Expr::Lit(n * 10).into()
            } else {
                node
            }
        });
        assert_eq!(show(&a2, r2), "x = (10 + 20); print(x)");
    }

    #[test]
    fn transform_family() {
        let (a, root) = sample();
        let (a2, r2) = a.transform(root, |node| match node {
            Lang::ExprLit(n) => Lang::ExprLit(n * 10),
            other => other,
        });
        assert_eq!(show(&a2, r2), "x = (10 + 20); print(x)");
    }

    #[test]
    fn hc_arena_family() {
        let (arena, root) = sample();
        let (hc, root) = Arena::from_arena(&arena, root);
        let s = hc.fold(root, |node: Lang<String, String>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Assign(name, val) => format!("{name} = {val}"),
                    Stmt::Seq(l, r) => format!("{l}; {r}"),
                    Stmt::Print(e) => format!("print({e})"),
                },
                |expr| match expr {
                    Expr::Var(name) => name,
                    Expr::Lit(n) => n.to_string(),
                    Expr::Add(l, r) => format!("({l} + {r})"),
                    Expr::Block(s, e) => format!("{{ {s}; {e} }}"),
                },
            )
        });
        assert_eq!(s, "x = (1 + 2); print(x)");
    }

    // -- multi-sorted cata: different result type per sort -------------------

    #[test]
    fn cata_family_different_result_types() {
        // Stmts fold to () (side effects), Exprs fold to i64 (values)
        let (a, root) = sample();
        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<(), i64>| match stmt {
                Stmt::Assign(_, _val) => (),
                Stmt::Seq((), ()) => (),
                Stmt::Print(_val) => (),
            },
            |expr: Expr<(), i64>| match expr {
                Expr::Var(_) => 0, // unresolved
                Expr::Lit(n) => n,
                Expr::Add(l, r) => l + r,
                Expr::Block((), e) => e,
            },
        );
        // Root is a Stmt (Seq), so result is Stmt variant
        match result {
            LangRes::Stmt(()) => {} // correct
            _ => panic!("expected Stmt result"),
        }
    }

    #[test]
    fn cata_family_expr_root() {
        // Build just an expression: (1 + 2)
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let root = add(&mut a, one, two);

        let result = fold_lang_multi(
            &a,
            root,
            |_stmt: Stmt<String, i64>| "stmt".to_string(),
            |expr: Expr<String, i64>| match expr {
                Expr::Lit(n) => n,
                Expr::Add(l, r) => l + r,
                Expr::Var(_) => 0,
                Expr::Block(_, e) => e,
            },
        );
        assert_eq!(result.unwrap_expr(), 3);
    }

    #[test]
    fn cata_family_cross_sort() {
        // { x = 42; x } — Block(Stmt, Expr)
        let mut a = Ast::new();
        let val = lit(&mut a, 42);
        let asgn = assign(&mut a, "x", val);
        let xref = var(&mut a, "x");
        let root = block(&mut a, asgn, xref);

        let result = fold_lang_multi(
            &a,
            root,
            // Stmt algebra: returns a list of bindings
            |stmt: Stmt<Vec<(String, i64)>, i64>| match stmt {
                Stmt::Assign(name, val) => vec![(name, val)],
                Stmt::Seq(mut l, r) => {
                    l.extend(r);
                    l
                }
                Stmt::Print(_) => vec![],
            },
            // Expr algebra: returns the value
            |expr: Expr<Vec<(String, i64)>, i64>| match expr {
                Expr::Lit(n) => n,
                Expr::Var(_) => 0,
                Expr::Add(l, r) => l + r,
                Expr::Block(_, e) => e,
            },
        );
        // Root is Expr (Block), so result is Expr variant
        assert_eq!(result.unwrap_expr(), 0); // Var("x") -> 0 (unresolved)
    }

    // -- Family with unit variants -------------------------------------------

    rec_family! {
        family Ty;

        enum MonoTy {
            Int,
            Bool,
            Fn(MonoTy, MonoTy),
        }

        enum PolyTy {
            Forall(String, PolyTy),
            Mono(MonoTy),
        }
    }

    #[test]
    fn family_with_unit_variants() {
        let mut a: Arena<Ty<usize, usize>> = Arena::new();
        let int = a.push(Ty::MonoTyInt);
        let bool_ = a.push(Ty::MonoTyBool);
        let arrow = a.push(Ty::MonoTyFn(int.0, bool_.0));
        let mono = a.push(Ty::PolyTyMono(arrow.0));
        let root = a.push(Ty::PolyTyForall("a".into(), mono.0));

        let s = a.fold(root, |node: Ty<String, String>| {
            node.dispatch(
                |mono: MonoTy<String>| match mono {
                    MonoTy::Int => "Int".into(),
                    MonoTy::Bool => "Bool".into(),
                    MonoTy::Fn(a, b) => format!("({a} -> {b})"),
                },
                |poly| match poly {
                    PolyTy::Forall(v, body) => format!("∀{v}. {body}"),
                    PolyTy::Mono(t) => t,
                },
            )
        });
        assert_eq!(s, "∀a. (Int -> Bool)");
    }

    #[test]
    fn cata_family_typed() {
        // MonoTy folds to u8, PolyTy folds to String
        let mut a: Arena<Ty<usize, usize>> = Arena::new();
        let int = a.push(Ty::MonoTyInt);
        let bool_ = a.push(Ty::MonoTyBool);
        let arrow = a.push(Ty::MonoTyFn(int.0, bool_.0));
        // Wrap the MonoTy in PolyTy::Mono to satisfy the sort constraint
        let mono_wrapped = a.push(Ty::PolyTyMono(arrow.0));
        let root = a.push(Ty::PolyTyForall("a".into(), mono_wrapped.0));

        let result = fold_ty_multi(
            &a,
            root,
            // MonoTy algebra: returns a compact representation
            |mono: MonoTy<u8>| match mono {
                MonoTy::Int => 0u8,
                MonoTy::Bool => 1u8,
                MonoTy::Fn(_, _) => 2u8,
            },
            // PolyTy algebra: returns a string
            |poly: PolyTy<u8, String>| match poly {
                PolyTy::Forall(v, body) => format!("∀{v}. {body}"),
                PolyTy::Mono(t) => format!("mono({})", t),
            },
        );
        assert_eq!(result.unwrap_polyty(), "∀a. mono(2)");
    }

    // -- 3-sort family: Stmt / Expr / Ty ------------------------------------

    rec_family! {
        family IRL;

        enum IStmt {
            Let(String, ITy, IExpr),
            Return(IExpr),
        }

        enum IExpr {
            Var(String),
            Lit(i64),
            Add(IExpr, IExpr),
            Ascribe(IExpr, ITy),
        }

        enum ITy {
            TInt,
            TBool,
            TFn(ITy, ITy),
        }
    }

    #[test]
    fn three_sort_uniform() {
        // let x: Int -> Int = 42; return x
        let mut a: Arena<IRL<usize, usize, usize>> = Arena::new();
        let tint = a.push(IRL::ITyTInt);
        let arrow = a.push(IRL::ITyTFn(tint.0, tint.0));
        let lit42 = a.push(IRL::IExprLit(42));
        let _let = a.push(IRL::IStmtLet("x".into(), arrow.0, lit42.0));
        let xref = a.push(IRL::IExprVar("x".into()));
        let ret = a.push(IRL::IStmtReturn(xref.0));

        let s = a.fold(ret, |node: IRL<String, String, String>| {
            node.dispatch(
                |stmt| match stmt {
                    IStmt::Let(n, ty, e) => format!("let {n}: {ty} = {e}"),
                    IStmt::Return(e) => format!("return {e}"),
                },
                |expr| match expr {
                    IExpr::Var(n) => n,
                    IExpr::Lit(n) => n.to_string(),
                    IExpr::Add(l, r) => format!("({l} + {r})"),
                    IExpr::Ascribe(e, ty) => format!("({e}: {ty})"),
                },
                |ty| match ty {
                    ITy::TInt => "Int".into(),
                    ITy::TBool => "Bool".into(),
                    ITy::TFn(a, b) => format!("({a} -> {b})"),
                },
            )
        });
        assert_eq!(s, "return x");
    }

    #[test]
    fn three_sort_heterogeneous() {
        // Stmts → (), Exprs → i64, Types → &'static str
        let mut a: Arena<IRL<usize, usize, usize>> = Arena::new();
        let tint = a.push(IRL::ITyTInt);
        let lit1 = a.push(IRL::IExprLit(1));
        let lit2 = a.push(IRL::IExprLit(2));
        let sum = a.push(IRL::IExprAdd(lit1.0, lit2.0));
        let asc = a.push(IRL::IExprAscribe(sum.0, tint.0));
        let root = a.push(IRL::IStmtReturn(asc.0));

        let result = fold_irl_multi(
            &a,
            root,
            |stmt: IStmt<i64, &str>| match stmt {
                IStmt::Let(_, _, _) => (),
                IStmt::Return(_) => (),
            },
            |expr: IExpr<i64, &str>| match expr {
                IExpr::Var(_) => 0,
                IExpr::Lit(n) => n,
                IExpr::Add(l, r) => l + r,
                IExpr::Ascribe(e, _) => e,
            },
            |ty: ITy<&str>| match ty {
                ITy::TInt => "Int",
                ITy::TBool => "Bool",
                ITy::TFn(_, _) => "Fn",
            },
        );
        match result {
            IRLRes::IStmt(()) => {} // correct: root is a stmt
            other => panic!("expected IStmt, got {:?}", other),
        }
    }

    #[test]
    fn para_family_subtree_ids() {
        let (a, root) = sample();
        // fold_with_ids_lang: each child carries (Id, Ai) — the original subtree id + folded result
        let result = fold_with_ids_lang_multi(
            &a,
            root,
            // Stmt algebra: returns String showing subtree ids
            |stmt: Stmt<(Id, String), (Id, String)>| match stmt {
                Stmt::Seq((lid, l), (rid, r)) => format!("seq[{},{}]({l}; {r})", lid.0, rid.0),
                Stmt::Assign(name, (eid, val)) => format!("{name}={val}@{}", eid.0),
                Stmt::Print((eid, val)) => format!("print({val}@{})", eid.0),
            },
            // Expr algebra: returns String
            |expr: Expr<(Id, String), (Id, String)>| match expr {
                Expr::Var(name) => name,
                Expr::Lit(n) => n.to_string(),
                Expr::Add((_, l), (_, r)) => format!("({l} + {r})"),
                Expr::Block((_, s), (_, e)) => format!("{{ {s}; {e} }}"),
            },
        );
        let s = result.unwrap_stmt();
        // Should contain subtree ids from para
        assert!(s.contains("seq["));
        assert!(s.contains("@"));
    }

    #[test]
    fn fold_short_family_early_exit() {
        let (a, root) = sample();
        let result = fold_short_lang_multi(
            &a,
            root,
            |stmt: Stmt<bool, bool>| match stmt {
                Stmt::Assign(_, found) | Stmt::Print(found) => {
                    if found {
                        Err(true)
                    } else {
                        Ok(false)
                    }
                }
                Stmt::Seq(l, r) => {
                    if l || r {
                        Err(true)
                    } else {
                        Ok(false)
                    }
                }
            },
            |expr: Expr<bool, bool>| match expr {
                Expr::Var(name) if name == "x" => Err(true),
                Expr::Var(_) | Expr::Lit(_) => Ok(false),
                Expr::Add(l, r) | Expr::Block(l, r) => {
                    if l || r {
                        Err(true)
                    } else {
                        Ok(false)
                    }
                }
            },
        );
        // Should find "x" and short-circuit
        match result {
            LangRes::Stmt(v) | LangRes::Expr(v) => assert!(v),
        }
    }

    #[test]
    fn fold_short_family_no_exit() {
        let (a, root) = sample();
        let result = fold_short_lang_multi(
            &a,
            root,
            |stmt: Stmt<bool, bool>| {
                Ok(match stmt {
                    Stmt::Assign(_, f) | Stmt::Print(f) => f,
                    Stmt::Seq(l, r) => l || r,
                })
            },
            |expr: Expr<bool, bool>| {
                Ok(match expr {
                    Expr::Var(name) => name == "z",
                    Expr::Lit(_) => false,
                    Expr::Add(l, r) | Expr::Block(l, r) => l || r,
                })
            },
        );
        assert!(matches!(result, LangRes::Stmt(false)));
    }

    #[test]
    fn transform_family_per_sort() {
        let (a, root) = sample();
        let (a2, r2) = transform_lang_multi(
            &a,
            root,
            |stmt| stmt.into(),
            |expr| match expr {
                Expr::Lit(n) => Expr::Lit(n * 2).into(),
                other => other.into(),
            },
        );
        assert_eq!(show(&a2, r2), "x = (2 + 4); print(x)");
    }

    #[test]
    fn fold_with_history_family() {
        let (a, root) = sample();
        let result = fold_with_history_lang_multi(
            &a,
            root,
            |stmt: Stmt<Ann<usize>, Ann<usize>>| match stmt {
                Stmt::Assign(_, e) | Stmt::Print(e) => 1 + e.value,
                Stmt::Seq(l, r) => 1 + l.value.max(r.value),
            },
            |expr: Expr<Ann<usize>, Ann<usize>>| match expr {
                Expr::Var(_) | Expr::Lit(_) => 0,
                Expr::Add(l, r) => {
                    let penalty = if !l.children.is_empty() { 1 } else { 0 };
                    1 + l.value.max(r.value) + penalty
                }
                Expr::Block(s, e) => 1 + s.value.max(e.value),
            },
        );
        assert!(result.unwrap_stmt() > 2);
    }

    #[test]
    fn fold_with_original_family() {
        let (a, root) = sample();
        let result = fold_with_original_lang_multi(
            &a,
            root,
            |_orig: &Stmt<usize, usize>, stmt: Stmt<usize, usize>| match stmt {
                Stmt::Assign(_, e) | Stmt::Print(e) => e,
                Stmt::Seq(l, r) => l + r,
            },
            |orig: &Expr<usize, usize>, expr: Expr<usize, usize>| {
                let child_cost = match &expr {
                    Expr::Var(_) | Expr::Lit(_) => 0,
                    Expr::Add(l, r) | Expr::Block(l, r) => l + r,
                };
                let own = match orig {
                    Expr::Add(..) => 2,
                    _ => 0,
                };
                child_cost + own
            },
        );
        // Add(1, 2) costs 2
        assert!(result.unwrap_stmt() >= 2);
    }

    #[test]
    fn prefold_family() {
        let (a, root) = sample();
        let result = prefold_lang_multi(
            &a,
            root,
            |stmt| stmt.into(),
            // pre: rewrite Add → just keep left child (drop right)
            |expr| match expr {
                Expr::Add(_l, _r) => Expr::Lit(99).into(), // replace Add with constant
                other => other.into(),
            },
            |stmt: Stmt<String, String>| match stmt {
                Stmt::Assign(n, v) => format!("{n}={v}"),
                Stmt::Seq(l, r) => format!("{l};{r}"),
                Stmt::Print(e) => format!("print({e})"),
            },
            |expr: Expr<String, String>| match expr {
                Expr::Var(n) => n,
                Expr::Lit(n) => n.to_string(),
                Expr::Add(l, r) => format!("({l}+{r})"),
                Expr::Block(s, e) => format!("{{{s};{e}}}"),
            },
        );
        let s = result.unwrap_stmt();
        assert!(s.contains("99")); // Add was replaced with Lit(99)
    }
}
