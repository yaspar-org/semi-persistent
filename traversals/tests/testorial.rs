// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! # Traversals: A Compiler Pipeline
//!
//! One language. One AST. Every pass is a different recursion scheme.
//! You never write a recursive function.
//!
//! ```text
//! Ch  What                    Scheme
//! ──  ──────────────────────  ──────────────────────────────────────
//!  0  The Language            rec_family!
//!  1  Pretty Print + Size     fold
//!  2  Constant Folding        rewrite
//!  3  Double Negation         rewrite (peek grandchild)
//!  4  Find Variable           fold_short
//!  5  Build from Seed         unfold
//!  6  Build with Reuse        unfold_short
//!  7  Factorial               refold (hylomorphism, no arena)
//!  8  Desugar While           rewrite (create new nodes)
//!  9  Type Inference          fold_lang_multi (closures)
//! 10  Interpreter             fold_lang_multi (closures → Env)
//! 11  Free Variables          fold_lang_multi (sets)
//! 12  Precedence Print        fold_lang_multi (paired result)
//! 13  Depth Complexity        fold_with_history (lookback)
//! 14  Type Check + Eval       fold_with_aux (zygomorphism)
//! 15  Saturating Eval         fold_pair (mutual recursion)
//! 16  Simplify Before Eval    prefold (normalize then fold)
//! 17  Canonicalize Build      postunfold (normalize during unfold)
//! 18  Fibonacci               refold_with_history (dynamorphism)
//! 19  Top-Down Desugar        rewrite_down (pre-order)
//! 20  Cost Model              fold_with_original (structure + value)
//! 21  Dead Code Search        fold_short_family (multi-sorted exit)
//! 22  Desugar Then Eval       prefold_multi
//! 23  Bytecode Compiler       fold_multi + stack machine
//! 24  Zipper: Find Binder     Zipper (walk up + sideways)
//! 25  Zipper: Patch Node      ZipperMut (in-place mutation)
//! 26  Zipper: Specialize      ZipperCow (copy-on-write spine)
//! ```

#[cfg(test)]
mod tests {
    use semi_persistent_traversals::*;
    use semi_persistent_traversals_derive::rec_family;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    // ====================================================================
    // Chapter 0: The Language
    // ====================================================================
    //
    // A small statement + expression language. Stmt and Expr are mutually
    // recursive: If contains an Expr condition, Block wraps a Stmt.
    //
    // The rec_family! macro generates a coproduct enum Lang<S0, S1> where:
    //   S0 = the type placed in every Stmt child position
    //   S1 = the type placed in every Expr child position
    //
    // In the arena, both are usize (indices): Lang<usize, usize>.
    // In a fold, they become the result type:
    //   Lang<String, String>  — both sorts fold to String (pretty print)
    //   Lang<i64, i64>        — both sorts fold to i64 (evaluate)
    //
    // In a multi-sorted fold, they can differ:
    //   Stmt<(), i64>         — stmts produce (), exprs produce i64
    //   Expr<(), i64>         — Stmt children are (), Expr children are i64
    //
    // This is the key idea: S0 and S1 are the "knobs" that each scheme
    // turns to replace children with computed results.

    rec_family! {
        family Lang;

        enum Stmt {
            Let(String, Expr),       // Expr child → S1
            Seq(Stmt, Stmt),         // Stmt children → S0
            Print(Expr),             // Expr child → S1
            If(Expr, Stmt, Stmt),    // S1, S0, S0
            While(Expr, Stmt),       // S1, S0
            Noop,                    // no children
        }

        enum Expr {
            Var(String),             // data (not a child)
            Lit(i64),                // data
            Bool(bool),              // data
            Add(Expr, Expr),         // Expr children → S1
            Mul(Expr, Expr),         // S1, S1
            Neg(Expr),               // S1
            Eq(Expr, Expr),          // S1, S1
            Block(Stmt, Expr),       // S0, S1 — cross-sort!
        }
    }

    // In the arena, all children are usize indices.
    // Lang<usize, usize> is the storage type.
    type Ast = Arena<Lang<usize, usize>>;

    // Smart constructors — use sort types + .into()
    fn let_(a: &mut Ast, n: &str, e: Id) -> Id {
        a.push(Stmt::Let(n.into(), e.0).into())
    }
    fn seq(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Stmt::Seq(l.0, r.0).into())
    }
    fn print_(a: &mut Ast, e: Id) -> Id {
        a.push(Stmt::Print(e.0).into())
    }
    fn if_(a: &mut Ast, c: Id, t: Id, e: Id) -> Id {
        a.push(Stmt::If(c.0, t.0, e.0).into())
    }
    fn while_(a: &mut Ast, c: Id, b: Id) -> Id {
        a.push(Stmt::While(c.0, b.0).into())
    }
    fn var(a: &mut Ast, n: &str) -> Id {
        a.push(Expr::Var(n.into()).into())
    }
    fn lit(a: &mut Ast, n: i64) -> Id {
        a.push(Expr::Lit(n).into())
    }
    fn bool_(a: &mut Ast, b: bool) -> Id {
        a.push(Expr::Bool(b).into())
    }
    fn add(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Expr::Add(l.0, r.0).into())
    }
    fn mul(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Expr::Mul(l.0, r.0).into())
    }
    fn neg(a: &mut Ast, e: Id) -> Id {
        a.push(Expr::Neg(e.0).into())
    }
    fn eq_(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Expr::Eq(l.0, r.0).into())
    }

    /// The sample program used throughout:
    /// ```text
    /// x = 1 + 2 * 3;
    /// y = -(x);
    /// if (x == 7) print(y) else print(x)
    /// ```
    fn sample() -> (Ast, Id) {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let prod = mul(&mut a, two, three);
        let sum = add(&mut a, one, prod);
        let s1 = let_(&mut a, "x", sum);

        let x1 = var(&mut a, "x");
        let ny = neg(&mut a, x1);
        let s2 = let_(&mut a, "y", ny);

        let x2 = var(&mut a, "x");
        let seven = lit(&mut a, 7);
        let cond = eq_(&mut a, x2, seven);
        let y = var(&mut a, "y");
        let pr_y = print_(&mut a, y);
        let x3 = var(&mut a, "x");
        let pr_x = print_(&mut a, x3);
        let s3 = if_(&mut a, cond, pr_y, pr_x);

        let s23 = seq(&mut a, s2, s3);
        let prog = seq(&mut a, s1, s23);
        (a, prog)
    }

    // ====================================================================
    // Chapter 1: Read the AST — fold
    // ====================================================================
    //
    // The simplest scheme. Bottom-up fold: each node sees its children
    // already converted to the result type. Same fold, two algebras:
    // one produces strings (pretty print), the other counts nodes.

    fn show(a: &Ast, root: Id) -> String {
        a.fold(root, |node: Lang<String, String>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Let(n, v) => format!("{n} = {v}"),
                    Stmt::Seq(l, r) => format!("{l}; {r}"),
                    Stmt::Print(e) => format!("print({e})"),
                    Stmt::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                    Stmt::While(c, b) => format!("while ({c}) {b}"),
                    Stmt::Noop => "noop".into(),
                },
                |expr| match expr {
                    Expr::Var(n) => n,
                    Expr::Lit(n) => n.to_string(),
                    Expr::Bool(b) => b.to_string(),
                    Expr::Add(l, r) => format!("({l} + {r})"),
                    Expr::Mul(l, r) => format!("({l} * {r})"),
                    Expr::Neg(e) => format!("(-{e})"),
                    Expr::Eq(l, r) => format!("({l} == {r})"),
                    Expr::Block(s, e) => format!("{{ {s}; {e} }}"),
                },
            )
        })
    }

    #[test]
    fn ch01_pretty_print_and_size() {
        let (a, root) = sample();

        // Same fold, different algebra → different result type
        assert_eq!(
            show(&a, root),
            "x = (1 + (2 * 3)); y = (-x); if ((x == 7)) print(y) else print(x)"
        );

        let size = a.fold(root, |node: Lang<usize, usize>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Let(_, e) | Stmt::Print(e) => 1 + e,
                    Stmt::Seq(l, r) => 1 + l + r,
                    Stmt::If(c, l, r) => 1 + c + l + r,
                    Stmt::While(c, b) => 1 + c + b,
                    Stmt::Noop => 1,
                },
                |expr| match expr {
                    Expr::Var(_) | Expr::Lit(_) | Expr::Bool(_) => 1,
                    Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => 1 + l + r,
                    Expr::Neg(e) => 1 + e,
                    Expr::Block(s, e) => 1 + s + e,
                },
            )
        });
        assert_eq!(size, 19); // 19 nodes in the sample program
    }

    // ====================================================================
    // Chapter 2: Constant Folding — rewrite
    // ====================================================================
    //
    // Bottom-up rewrite. Children are already rewritten and pushed into
    // the new arena, so we can peek at them to check if they're literals.

    #[test]
    fn ch02_constant_fold() {
        let (a, root) = sample();
        let (a2, r2) = a.rewrite(root, |node, new| {
            if let Ok(expr) = TryInto::<Expr<usize, usize>>::try_into(node.clone()) {
                match expr {
                    Expr::Add(l, r) => {
                        if let (Lang::ExprLit(a), Lang::ExprLit(b)) =
                            (new.get(Id(l)), new.get(Id(r)))
                        {
                            return new.push(Expr::Lit(a + b).into());
                        }
                    }
                    Expr::Mul(l, r) => {
                        if let (Lang::ExprLit(a), Lang::ExprLit(b)) =
                            (new.get(Id(l)), new.get(Id(r)))
                        {
                            return new.push(Expr::Lit(a * b).into());
                        }
                    }
                    Expr::Neg(e) => {
                        if let Lang::ExprLit(n) = new.get(Id(e)) {
                            return new.push(Expr::Lit(-n).into());
                        }
                    }
                    Expr::Eq(l, r) => {
                        if let (Lang::ExprLit(a), Lang::ExprLit(b)) =
                            (new.get(Id(l)), new.get(Id(r)))
                        {
                            return new.push(Expr::Bool(a == b).into());
                        }
                    }
                    _ => {}
                }
            }
            new.push(node)
        });
        assert_eq!(
            show(&a2, r2),
            "x = 7; y = (-x); if ((x == 7)) print(y) else print(x)"
        );
    }

    // ====================================================================
    // Chapter 3: Double Negation Elimination — rewrite
    // ====================================================================
    //
    // Neg(Neg(x)) → x. Peek at the child, return grandchild's id directly.

    #[test]
    fn ch03_double_negation() {
        let mut a = Ast::new();
        let five = lit(&mut a, 5);
        let n1 = neg(&mut a, five);
        let n2 = neg(&mut a, n1);
        let n3 = neg(&mut a, n2);
        let root = print_(&mut a, n3);

        let (a2, r2) = a.rewrite(root, |node, new| match node {
            Lang::ExprNeg(inner) => match new.get(Id(inner)) {
                Lang::ExprNeg(x) => Id(*x), // skip two Negs, return grandchild
                _ => new.push(Lang::ExprNeg(inner)),
            },
            other => new.push(other),
        });
        assert_eq!(show(&a2, r2), "print((-5))");
    }

    // ====================================================================
    // Chapter 4: Find Variable — fold_short (early exit)
    // ====================================================================
    //
    // Search for a variable name. Err exits immediately.

    #[test]
    fn ch04_find_variable() {
        let (a, root) = sample();
        let found = a.fold_short(root, |node: Lang<bool, bool>| {
            node.dispatch(
                |stmt| {
                    Ok(match stmt {
                        Stmt::Let(_, e) | Stmt::Print(e) => e,
                        Stmt::Seq(l, r) | Stmt::If(_, l, r) => l || r,
                        Stmt::While(c, b) => c || b,
                        Stmt::Noop => false,
                    })
                },
                |expr| match expr {
                    Expr::Var(name) if name == "y" => Err(true),
                    Expr::Var(_) | Expr::Lit(_) | Expr::Bool(_) => Ok(false),
                    Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => Ok(l || r),
                    Expr::Neg(e) | Expr::Block(_, e) => Ok(e),
                },
            )
        });
        assert!(found);
    }

    // ====================================================================
    // Chapter 5: Build from Seed — unfold
    // ====================================================================

    #[test]
    fn ch05_generate_ast() {
        let mut a = Ast::new();
        let root = unfold(&mut a, 3u32, |depth| {
            if depth == 0 {
                (Expr::Lit(1).into(), vec![])
            } else {
                (Expr::Add(0, 0).into(), vec![depth - 1, depth - 1])
            }
        });
        let val = a.fold(root, |node: Lang<i64, i64>| {
            node.dispatch(
                |_| 0,
                |expr| match expr {
                    Expr::Lit(n) => n,
                    Expr::Add(l, r) => l + r,
                    _ => 0,
                },
            )
        });
        assert_eq!(val, 8); // 2^3
    }

    // ====================================================================
    // Chapter 6: Build with Reuse — unfold_short
    // ====================================================================

    #[test]
    fn ch06_build_with_reuse() {
        let mut a = Ast::new();
        let shared = a.push(Expr::Lit(42).into());
        let root = unfold_short(&mut a, 2u32, |depth| {
            if depth == 0 {
                (Expr::Neg(0).into(), vec![Seed::Done(shared)])
            } else {
                (
                    Expr::Add(0, 0).into(),
                    vec![Seed::Continue(depth - 1), Seed::Continue(depth - 1)],
                )
            }
        });
        let val = a.fold(root, |node: Lang<i64, i64>| {
            node.dispatch(
                |_| 0,
                |expr| match expr {
                    Expr::Lit(n) => n,
                    Expr::Add(l, r) => l + r,
                    Expr::Neg(e) => -e,
                    _ => 0,
                },
            )
        });
        assert_eq!(val, -168); // 4 * -42
    }

    // ====================================================================
    // Chapter 7: Factorial — refold (no arena)
    // ====================================================================

    // refold (hylomorphism) unfolds and folds in a single pass — no arena
    // is ever built. The coalgebra describes what the tree *would* look
    // like (each node value + child seeds), and the algebra consumes it.
    // Intermediate nodes are produced and consumed on the fly via an
    // explicit stack.
    //
    // Conceptual tree (never materialized):
    //
    //   5 ── 4 ── 3 ── 2 ── 1 ── 1(base)
    //
    // Execution:
    //   Expand seeds top-down: 5 → 4 → 3 → 2 → 1 → 0(base)
    //   Fold back up:
    //     Build(1, 0 children) → 1
    //     Build(1, [1])        → 1×1 = 1
    //     Build(2, [1])        → 2×1 = 2
    //     Build(3, [2])        → 3×2 = 6
    //     Build(4, [6])        → 4×6 = 24
    //     Build(5, [24])       → 5×24 = 120
    #[test]
    fn ch07_factorial() {
        let result = refold(
            5u64,
            &|n| {
                if n == 0 {
                    (1u64, vec![])
                } else {
                    (n, vec![n - 1])
                }
            },
            &|n, ch: Vec<u64>| if ch.is_empty() { n } else { n * ch[0] },
        );
        assert_eq!(result, 120);
    }

    // ====================================================================
    // Chapter 8: Desugar While — rewrite (create new nodes)
    // ====================================================================
    //
    // While(c, body) → If(c, Seq(body, While(c, body)), Noop)
    //
    // This requires creating NEW nodes (If, Seq, Noop) that didn't exist
    // in the original tree. `transform` can't do this because its rule
    // returns a single node. `rewrite` gives the rule &mut Arena so it
    // can push arbitrarily many new nodes.

    #[test]
    fn ch08b_desugar_while() {
        let mut a = Ast::new();
        let x = var(&mut a, "x");
        let zero = lit(&mut a, 0);
        let cond = eq_(&mut a, x, zero);
        let x2 = var(&mut a, "x");
        let body = print_(&mut a, x2);
        let root = while_(&mut a, cond, body);

        assert_eq!(show(&a, root), "while ((x == 0)) print(x)");

        // rewrite: rule gets &mut Arena, can create new nodes
        let (a2, r2) = a.rewrite(root, |node, new| {
            match node {
                Lang::StmtWhile(c, b) => {
                    // Build: If(c, Seq(b, While(c, b)), Noop)
                    let while_again = new.push(Lang::StmtWhile(c, b));
                    let seq = new.push(Lang::StmtSeq(b, while_again.0));
                    let noop = new.push(Lang::StmtNoop);
                    new.push(Lang::StmtIf(c, seq.0, noop.0))
                }
                other => new.push(other),
            }
        });
        assert_eq!(
            show(&a2, r2),
            "if ((x == 0)) print(x); while ((x == 0)) print(x) else noop"
        );
    }

    // ====================================================================
    // Chapter 9: Type Inference — fold_family (closures)
    // ====================================================================
    //
    // This is the first MULTI-SORTED fold: each sort gets its own
    // result type. The two algebras are:
    //   Stmt algebra: Stmt<TyStmt, TyExpr> → TyStmt
    //   Expr algebra: Expr<TyStmt, TyExpr> → TyExpr
    //
    // Notice the type parameters: S0 = TyStmt, S1 = TyExpr.
    // Inside Stmt::Let(name, val), the `val` field has type TyExpr
    // (because Let's second field is an Expr child → S1 = TyExpr).
    // Inside Expr::Block(s, e), `s` has type TyStmt (Stmt child → S0).
    //
    // We fold to closures (Env → Env, Env → Ty) so that variable
    // lookups work: the environment flows through at application time.

    type TyEnv = HashMap<String, Ty>;
    type TyStmt = Rc<dyn Fn(&TyEnv) -> TyEnv>;
    type TyExpr = Rc<dyn Fn(&TyEnv) -> Ty>;

    #[derive(Clone, Debug, PartialEq)]
    enum Ty {
        Int,
        Bool,
        Unknown,
    }

    #[test]
    fn ch09_type_inference() {
        let (a, root) = sample();
        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<TyStmt, TyExpr>| -> TyStmt {
                match stmt {
                    Stmt::Let(name, expr) => Rc::new(move |env| {
                        let ty = expr(env);
                        let mut e = env.clone();
                        e.insert(name.clone(), ty);
                        e
                    }),
                    Stmt::Seq(l, r) => Rc::new(move |env| r(&l(env))),
                    Stmt::Print(_) | Stmt::Noop => Rc::new(|env| env.clone()),
                    Stmt::If(_, t, e) => Rc::new(move |env| {
                        let mut m = t(env);
                        m.extend(e(env));
                        m
                    }),
                    Stmt::While(_, b) => Rc::new(move |env| b(env)),
                }
            },
            |expr: Expr<TyStmt, TyExpr>| -> TyExpr {
                match expr {
                    Expr::Lit(_) => Rc::new(|_| Ty::Int),
                    Expr::Bool(_) => Rc::new(|_| Ty::Bool),
                    Expr::Var(name) => {
                        Rc::new(move |env| env.get(&name).cloned().unwrap_or(Ty::Unknown))
                    }
                    Expr::Add(l, r) | Expr::Mul(l, r) => Rc::new(move |env| {
                        if l(env) == Ty::Int && r(env) == Ty::Int {
                            Ty::Int
                        } else {
                            Ty::Unknown
                        }
                    }),
                    Expr::Neg(e) => Rc::new(move |env| e(env)),
                    Expr::Eq(_, _) => Rc::new(|_| Ty::Bool),
                    Expr::Block(s, e) => Rc::new(move |env| e(&s(env))),
                }
            },
        );
        // Run the type checker with an empty env
        let env = result.unwrap_stmt()(&TyEnv::new());
        assert_eq!(env["x"], Ty::Int); // 1 + 2*3 → Int
        assert_eq!(env["y"], Ty::Int); // -(x) → Int, because x is Int
    }

    // ====================================================================
    // Chapter 10: Interpreter — fold_family (closures)
    // ====================================================================
    //
    // Stmts fold to Env → Env. Exprs fold to Env → i64.
    // The fold produces closures; applying them runs the program.

    type Env = HashMap<String, i64>;
    type SVal = Rc<dyn Fn(&Env) -> Env>;
    type EVal = Rc<dyn Fn(&Env) -> i64>;

    #[test]
    fn ch10_interpreter() {
        let (a, root) = sample();
        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<SVal, EVal>| -> SVal {
                match stmt {
                    Stmt::Let(name, val) => Rc::new(move |env| {
                        let mut e = env.clone();
                        e.insert(name.clone(), val(env));
                        e
                    }),
                    Stmt::Seq(l, r) => Rc::new(move |env| r(&l(env))),
                    Stmt::Print(v) => Rc::new(move |env| {
                        let _ = v(env);
                        env.clone()
                    }),
                    Stmt::If(c, t, e) => {
                        Rc::new(move |env| if c(env) != 0 { t(env) } else { e(env) })
                    }
                    Stmt::While(c, b) => Rc::new(move |env| {
                        let mut e = env.clone();
                        while c(&e) != 0 {
                            e = b(&e);
                        }
                        e
                    }),
                    Stmt::Noop => Rc::new(|env| env.clone()),
                }
            },
            |expr: Expr<SVal, EVal>| -> EVal {
                match expr {
                    Expr::Lit(n) => Rc::new(move |_| n),
                    Expr::Bool(b) => Rc::new(move |_| if b { 1 } else { 0 }),
                    Expr::Var(name) => Rc::new(move |env| *env.get(&name).unwrap_or(&0)),
                    Expr::Add(l, r) => Rc::new(move |env| l(env) + r(env)),
                    Expr::Mul(l, r) => Rc::new(move |env| l(env) * r(env)),
                    Expr::Neg(e) => Rc::new(move |env| -e(env)),
                    Expr::Eq(l, r) => Rc::new(move |env| if l(env) == r(env) { 1 } else { 0 }),
                    Expr::Block(s, e) => Rc::new(move |env| e(&s(env))),
                }
            },
        );
        let env = result.unwrap_stmt()(&Env::new());
        assert_eq!(env["x"], 7);
        assert_eq!(env["y"], -7);
    }

    // ====================================================================
    // Chapter 11: Free Variable Analysis — fold_family
    // ====================================================================
    //
    // Stmts → (defined, free). Exprs → free.

    type Defs = HashSet<String>;
    type Frees = HashSet<String>;

    #[test]
    fn ch11_free_vars() {
        let (a, root) = sample();
        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<(Defs, Frees), Frees>| -> (Defs, Frees) {
                match stmt {
                    Stmt::Let(name, ef) => (HashSet::from([name]), ef),
                    Stmt::Seq((ld, lf), (rd, rf)) => {
                        let rf: Frees = rf.difference(&ld).cloned().collect();
                        (
                            ld.union(&rd).cloned().collect(),
                            lf.union(&rf).cloned().collect(),
                        )
                    }
                    Stmt::Print(ef) => (HashSet::new(), ef),
                    Stmt::While(cf, (_, bf)) => (HashSet::new(), cf.union(&bf).cloned().collect()),
                    Stmt::If(cf, (_, tf), (_, ef)) => (
                        HashSet::new(),
                        cf.union(&tf)
                            .cloned()
                            .collect::<Frees>()
                            .union(&ef)
                            .cloned()
                            .collect(),
                    ),
                    Stmt::Noop => (HashSet::new(), HashSet::new()),
                }
            },
            |expr: Expr<(Defs, Frees), Frees>| -> Frees {
                match expr {
                    Expr::Var(n) => HashSet::from([n]),
                    Expr::Lit(_) | Expr::Bool(_) => HashSet::new(),
                    Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => {
                        l.union(&r).cloned().collect()
                    }
                    Expr::Neg(e) => e,
                    Expr::Block((def, sf), ef) => {
                        let ef: Frees = ef.difference(&def).cloned().collect();
                        sf.union(&ef).cloned().collect()
                    }
                }
            },
        );
        let (_, free) = result.unwrap_stmt();
        assert!(free.is_empty()); // all vars are bound by Let
    }

    // ====================================================================
    // Chapter 12: Precedence-Aware Pretty Print — fold_family
    // ====================================================================
    //
    // Stmts → String, Exprs → (String, u8) where u8 is precedence.
    // Parenthesize when a low-precedence child is inside a high-precedence parent.

    #[test]
    fn ch12_precedence_print() {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let four = lit(&mut a, 4);
        let sum = add(&mut a, one, two);
        let sum2 = add(&mut a, three, four);
        let root = mul(&mut a, sum, sum2); // (1+2) * (3+4) — needs parens

        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<String, (String, u8)>| match stmt {
                Stmt::Let(n, (v, _)) => format!("{n} = {v}"),
                Stmt::Seq(l, r) => format!("{l}; {r}"),
                Stmt::Print((e, _)) => format!("print({e})"),
                Stmt::If((c, _), t, e) => format!("if ({c}) {t} else {e}"),
                Stmt::While((c, _), b) => format!("while ({c}) {b}"),
                Stmt::Noop => "noop".into(),
            },
            |expr: Expr<String, (String, u8)>| match expr {
                Expr::Var(n) => (n, 99),
                Expr::Lit(n) => (n.to_string(), 99),
                Expr::Bool(b) => (b.to_string(), 99),
                Expr::Add((l, lp), (r, rp)) => {
                    let l = if lp < 1 { format!("({l})") } else { l };
                    let r = if rp <= 1 { format!("({r})") } else { r };
                    (format!("{l} + {r}"), 1)
                }
                Expr::Mul((l, lp), (r, rp)) => {
                    let l = if lp < 2 { format!("({l})") } else { l };
                    let r = if rp <= 2 { format!("({r})") } else { r };
                    (format!("{l} * {r}"), 2)
                }
                Expr::Neg((e, _)) => (format!("-{e}"), 99),
                Expr::Eq((l, _), (r, _)) => (format!("{l} == {r}"), 0),
                Expr::Block(s, (e, ep)) => (format!("{{ {s}; {e} }}"), ep),
            },
        );
        assert_eq!(result.unwrap_expr().0, "(1 + 2) * (3 + 4)");
    }

    // ====================================================================
    // Chapter 13: Depth-Limited Complexity — fold_with_history
    // ====================================================================
    //
    // fold_with_history gives &Ann<A> per child. Ann has `value` (the result) and
    // `children` (child ids for looking back further). Use it to compute
    // a "complexity score" that penalizes deep nesting: nodes deeper
    // than 2 levels count double.

    #[test]
    fn ch13_complexity_with_history() {
        let (a, root) = sample();
        let complexity = a.fold_with_history(root, |node: Lang<&Ann<usize>, &Ann<usize>>| {
            node.dispatch(
                |stmt| match stmt {
                    Stmt::Let(_, e) | Stmt::Print(e) => 1 + e.value,
                    Stmt::Seq(l, r) => 1 + l.value + r.value,
                    Stmt::If(c, t, e) => 1 + c.value + t.value + e.value,
                    Stmt::While(c, b) => 1 + c.value + b.value,
                    Stmt::Noop => 1,
                },
                |expr| {
                    // Check if any child has children that are themselves deep.
                    // This is the lookback: we peek at grandchildren via Ann.
                    let penalty = match &expr {
                        Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => {
                            // If either child has children (i.e. is not a leaf),
                            // add a nesting penalty
                            let l_deep = !l.children.is_empty();
                            let r_deep = !r.children.is_empty();
                            if l_deep && r_deep {
                                2
                            } else if l_deep || r_deep {
                                1
                            } else {
                                0
                            }
                        }
                        _ => 0,
                    };
                    let base = match expr {
                        Expr::Var(_) | Expr::Lit(_) | Expr::Bool(_) => 1,
                        Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => 1 + l.value + r.value,
                        Expr::Neg(e) | Expr::Block(_, e) => 1 + e.value,
                    };
                    base + penalty
                },
            )
        });
        // Should be higher than plain node count (16) due to nesting penalties
        assert!(complexity > 16);
    }

    // ====================================================================
    // Chapter 14: Type Check + Eval — fold_with_aux (paired folds)
    // ====================================================================
    //
    // fold_with_aux runs two folds simultaneously. The auxiliary fold infers types.
    // The main fold evaluates, with access to the type info.

    #[test]
    fn ch14_zygo_typecheck_eval() {
        // Just an expression: 1 + 2 * 3
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let prod = mul(&mut a, two, three);
        let root = add(&mut a, one, prod);

        // aux: type check (returns "int" or "bool")
        // main: evaluate (returns i64), but can see the type
        let result = a.fold_with_aux(
            root,
            // aux: infer type
            |node: Lang<&str, &str>| {
                node.dispatch(
                    |_| "stmt",
                    |expr| match expr {
                        Expr::Lit(_) => "int",
                        Expr::Bool(_) => "bool",
                        Expr::Add(l, r) | Expr::Mul(l, r) => {
                            if l == "int" && r == "int" {
                                "int"
                            } else {
                                "err"
                            }
                        }
                        _ => "unknown",
                    },
                )
            },
            // main: evaluate, with access to (value, type) pairs
            |node: Lang<(i64, &str), (i64, &str)>| {
                node.dispatch(
                    |_| 0i64,
                    |expr| match expr {
                        Expr::Lit(n) => n,
                        Expr::Add((l, lt), (r, rt)) => {
                            if lt == "int" && rt == "int" {
                                l + r
                            } else {
                                -1
                            }
                        }
                        Expr::Mul((l, lt), (r, rt)) => {
                            if lt == "int" && rt == "int" {
                                l * r
                            } else {
                                -1
                            }
                        }
                        _ => 0,
                    },
                )
            },
        );
        assert_eq!(result, 7); // 1 + 2*3
    }

    // ====================================================================
    // Chapter 15: Saturating Eval — fold_pair (mutually recursive)
    // ====================================================================
    //
    // Two folds that depend on each other:
    //   - "value": compute the expression's value, but clamp if overflow
    //   - "overflows": does this expression overflow i8 range?
    //
    // The value fold needs the overflow flag to decide whether to clamp.
    // The overflow fold needs the value to check if it exceeds the range.
    // They depend on each other — that's what fold_pair is for.

    #[test]
    fn ch15_mutu_saturating() {
        let mut a = Ast::new();
        // 100 + 100 — overflows i8 (max 127)
        let h = lit(&mut a, 100);
        let h2 = lit(&mut a, 100);
        let root = add(&mut a, h, h2);

        let (value, overflows) = a.fold_pair(
            root,
            // value: compute, but clamp to 127 if overflow detected
            |node: Lang<(i64, bool), (i64, bool)>| {
                node.dispatch(
                    |_| 0i64,
                    |expr| match expr {
                        Expr::Lit(n) => n,
                        Expr::Add((l, _), (r, _)) => {
                            let sum = l + r;
                            if sum > 127 { 127 } else { sum } // clamp
                        }
                        Expr::Mul((l, _), (r, _)) => {
                            let prod = l * r;
                            if prod > 127 { 127 } else { prod }
                        }
                        Expr::Neg((v, _)) => -v,
                        _ => 0,
                    },
                )
            },
            // overflows: check if the unclamped result exceeds i8
            |node: Lang<(i64, bool), (i64, bool)>| {
                node.dispatch(
                    |_| false,
                    |expr| match expr {
                        Expr::Lit(_) => false,
                        Expr::Add((l, lo), (r, ro)) => lo || ro || (l + r) > 127,
                        Expr::Mul((l, lo), (r, ro)) => lo || ro || (l * r) > 127,
                        Expr::Neg((_, o)) => o,
                        _ => false,
                    },
                )
            },
        );
        assert_eq!(value, 127); // clamped
        assert!(overflows); // 100 + 100 = 200 > 127
    }

    // ====================================================================
    // Chapter 16: Simplify Before Eval — prefold
    // ====================================================================
    //
    // prefold applies a natural transformation to each node before folding.
    // The transformation sees the node with children still as usize ids
    // (it's a structural rewrite, not a value computation).
    //
    // Here: strip identity operations (x+0 → x, x*1 → x) before evaluating.

    #[test]
    fn ch16_prepro_normalize() {
        // prefold: normalize each node before folding. The normalization
        // is N → N (single layer, can't peek at children's values).
        //
        // Use case: strength reduction. Before evaluating, rewrite
        // Mul(x, y) → Add(x, y) to pretend multiplication is addition.
        // This is a silly transformation, but it demonstrates prefold:
        // the normalization changes the STRUCTURE before the fold sees it.
        let mut a = Ast::new();
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let root = mul(&mut a, two, three); // Mul(2, 3)

        let result = a.prefold(
            root,
            // pre: rewrite Mul → Add (strength reduction)
            |node| match node {
                Lang::ExprMul(l, r) => Lang::ExprAdd(l, r),
                other => other,
            },
            // fold: evaluate
            |node: Lang<i64, i64>| {
                node.dispatch(
                    |_| 0i64,
                    |expr| match expr {
                        Expr::Lit(n) => n,
                        Expr::Add(l, r) => l + r,
                        Expr::Mul(l, r) => l * r,
                        _ => 0,
                    },
                )
            },
        );
        // Mul(2,3) was rewritten to Add(2,3) before folding → 2+3 = 5, not 6
        assert_eq!(result, 5);
    }

    // ====================================================================
    // Chapter 17: Canonicalize During Build — postunfold
    // ====================================================================
    //
    // postunfold applies a natural transformation after each unfold step,
    // before the node is pushed into the arena. Use it to enforce a
    // canonical ordering: in commutative ops, put the smaller subtree
    // (lower arena id) on the left. This maximizes hash-consing sharing.

    #[test]
    fn ch17_postpro_canonicalize() {
        let mut a = Ast::new();
        // Unfold: build Add(depth-1, depth-1) tree, but coalg always
        // puts the "heavier" seed on the left. postunfold flips it.
        let root = postunfold(
            &mut a,
            3u32,
            // post: canonicalize — smaller child id on the left for Add
            |node| match node {
                Lang::ExprAdd(l, r) if l > r => Lang::ExprAdd(r, l),
                other => other,
            },
            // coalg: unfold, deliberately putting children in wrong order
            |n| {
                if n == 0 {
                    (Lang::ExprLit(n as i64), vec![])
                } else {
                    // Two children with same depth — but different seeds
                    // to show postunfold normalizes the order
                    (Lang::ExprAdd(0, 0), vec![n - 1, n - 1])
                }
            },
        );
        // With hash-consing, identical subtrees share ids.
        // postunfold ensures Add(l, r) always has l <= r.
        let s = show(&a, root);
        assert!(s.contains("+")); // it's a tree of Adds
        // Verify canonicalization: in every Add node, left id <= right id
        // (We can check this by looking at the arena directly)
        for i in 0..a.len() {
            if let Lang::ExprAdd(l, r) = a.get(Id(i)) {
                assert!(l <= r, "Add({l}, {r}) not canonical");
            }
        }
    }

    // ====================================================================
    // Chapter 18: Fibonacci — refold_with_history
    // ====================================================================
    //
    // refold_with_history = unfold then fold_with_history. Unfold a chain, fold with lookback.

    #[test]
    fn ch18_fibonacci() {
        // Use a simple Expr functor for this: Add(R, R) and Lit(i64)
        let result = refold_with_history(
            10u32,
            // coalg: unfold a chain
            |n| {
                if n <= 1 {
                    (Lang::ExprLit(n as i64), vec![])
                } else {
                    (Lang::ExprAdd(0, 0), vec![n - 1, n - 2])
                }
            },
            // alg with history: Add nodes sum their children
            |node: Lang<&Ann<i64>, &Ann<i64>>| {
                node.dispatch(
                    |_| 0i64,
                    |expr: Expr<&Ann<i64>, &Ann<i64>>| match expr {
                        Expr::Lit(n) => n,
                        Expr::Add(l, r) => l.value + r.value,
                        _ => 0,
                    },
                )
            },
        );
        assert_eq!(result, 55); // fib(10)
    }

    // ====================================================================
    // Chapter 19: Top-Down Desugar — transform_down
    // ====================================================================
    //
    // Pre-order rewrite. The rule sees the node before its children
    // are processed. Children of the rewritten node are then visited.

    #[test]
    fn ch19_transform_down() {
        let mut a = Ast::new();
        let five = lit(&mut a, 5);
        let n1 = neg(&mut a, five);
        let root = neg(&mut a, n1); // Neg(Neg(5))

        // Top-down: replace Neg(x) with Mul(x, x) pre-order
        let (a2, r2) = a.rewrite_down(root, |node| match node {
            Lang::ExprNeg(inner) => Lang::ExprMul(inner, inner),
            other => other,
        });
        // Pre-order: outer Neg(Neg(5)) → Mul(Neg(5), Neg(5))
        // Then inner Negs → Mul(Mul(5,5), Mul(5,5))
        let val = a2.fold(r2, |node: Lang<i64, i64>| {
            node.dispatch(
                |_| 0,
                |expr| match expr {
                    Expr::Lit(n) => n,
                    Expr::Mul(l, r) => l * r,
                    _ => 0,
                },
            )
        });
        assert_eq!(val, 625); // 5^4
    }

    // ====================================================================
    // Chapter 20: Cost Model — fold_with_original
    // ====================================================================
    //
    // fold_with_original: the algebra sees both the original node (with usize children)
    // AND the folded node (with results substituted). Use it to compute
    // an execution cost where the cost of each node depends on its
    // STRUCTURE (original node) not just its children's costs.
    //
    // Binary ops cost 2, unary ops cost 1, leaves cost 0.
    // The folded children give us the subtree costs to sum up.
    // The original node tells us the current node's own cost.

    #[test]
    fn ch20_fold_with_original_cost() {
        let (a, root) = sample();
        let cost = a.fold_with_original(
            root,
            |orig: &Lang<usize, usize>, node: Lang<usize, usize>| {
                // Sum children's costs from the folded node
                let child_cost: usize = node.dispatch(
                    |stmt| match stmt {
                        Stmt::Let(_, e) | Stmt::Print(e) => e,
                        Stmt::Seq(l, r) => l + r,
                        Stmt::If(c, t, e) => c + t + e,
                        Stmt::While(c, b) => c + b,
                        Stmt::Noop => 0,
                    },
                    |expr| match expr {
                        Expr::Var(_) | Expr::Lit(_) | Expr::Bool(_) => 0,
                        Expr::Add(l, r) | Expr::Mul(l, r) | Expr::Eq(l, r) => l + r,
                        Expr::Neg(e) | Expr::Block(_, e) => e,
                    },
                );
                // Determine THIS node's own cost from the original structure
                let own_cost = match orig {
                    Lang::ExprAdd(..) | Lang::ExprMul(..) | Lang::ExprEq(..) => 2, // binary: expensive
                    Lang::ExprNeg(..) => 1,                                        // unary: cheap
                    Lang::StmtIf(..) => 1, // branch: has cost
                    _ => 0,                // leaves, seq, etc
                };
                child_cost + own_cost
            },
        );
        // sample: Add(2) + Mul(2) + Neg(1) + Eq(2) + If(1) = 8
        assert_eq!(cost, 8);
    }

    // ====================================================================
    // Chapter 21: Dead Code Search — fold_short_family (multi-sorted early exit)
    // ====================================================================
    //
    // Search for dead code: an If with a constant false condition.
    // Short-circuit when found.

    #[test]
    fn ch21_dead_code_search() {
        let mut a = Ast::new();
        let f = bool_(&mut a, false);
        let x = var(&mut a, "x");
        let dead = print_(&mut a, x);
        let y = var(&mut a, "y");
        let live = print_(&mut a, y);
        let root = if_(&mut a, f, dead, live);

        let result = fold_short_lang_multi(
            &a,
            root,
            |stmt: Stmt<bool, bool>| match stmt {
                Stmt::If(cond_is_false, _, _) if cond_is_false => Err(true), // found dead code!
                Stmt::Seq(l, r) => Ok(l || r),
                _ => Ok(false),
            },
            |expr: Expr<bool, bool>| match expr {
                Expr::Bool(false) => Ok(true), // this is a "false" literal
                _ => Ok(false),
            },
        );
        assert!(matches!(result, LangRes::Stmt(true)));
    }

    // ====================================================================
    // Chapter 22: Desugar Then Evaluate — prefold_multi
    // ====================================================================
    //
    // Multi-sorted prefold: transform each layer with per-sort rules,
    // then fold with per-sort algebras. Here: rewrite Mul(x,y) → Add(x,y)
    // (pretend multiplication is addition), then evaluate.
    // Stmts fold to String, Exprs fold to i64.

    #[test]
    fn ch22_prefold_multi() {
        let mut a = Ast::new();
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let prod = mul(&mut a, two, three);
        let root = print_(&mut a, prod);

        let result = prefold_lang_multi(
            &a,
            root,
            // pre for stmts: identity
            |stmt| stmt.into(),
            // pre for exprs: Mul → Add (strength reduction)
            |expr| match expr {
                Expr::Mul(l, r) => Expr::Add(l, r).into(),
                other => other.into(),
            },
            // fold stmts → String
            |stmt: Stmt<String, i64>| match stmt {
                Stmt::Let(n, v) => format!("{n} = {v}"),
                Stmt::Seq(l, r) => format!("{l}; {r}"),
                Stmt::Print(v) => format!("print({})", v),
                Stmt::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                Stmt::While(c, b) => format!("while ({c}) {b}"),
                Stmt::Noop => "noop".into(),
            },
            // fold exprs → i64
            |expr: Expr<String, i64>| match expr {
                Expr::Lit(n) => n,
                Expr::Add(l, r) => l + r,
                Expr::Mul(l, r) => l * r, // won't be reached — Mul was rewritten
                Expr::Neg(e) => -e,
                _ => 0,
            },
        );
        // Mul(2,3) was rewritten to Add(2,3) → 2+3 = 5
        assert_eq!(result.unwrap_stmt(), "print(5)");
    }

    // ====================================================================
    // Chapter 23: Compiling to Bytecode — fold_multi
    // ====================================================================
    //
    // A bottom-up fold is strict: it visits every child. This is bad for
    // interpreting control flow (both If branches execute), but perfect
    // for compiling it — a compiler MUST emit code for all branches.
    //
    // Here S0 = S1 = Vec<Op>: both sorts fold to instruction sequences.
    // Stmt::If(cond, t, e) receives:
    //   cond: Vec<Op>  (S1 — compiled condition instructions)
    //   t: Vec<Op>     (S0 — compiled then-branch)
    //   e: Vec<Op>     (S0 — compiled else-branch)
    // The algebra concatenates them with jump instructions between.
    //
    // Because children are VALUES (not side effects), we know their
    // lengths before assembling — so jump offsets are pure arithmetic.
    // No backpatching, no dummy instructions.

    #[derive(Debug, Clone, PartialEq)]
    enum Op {
        Push(i64),
        Load(String),
        Store(String),
        Add,
        Mul,
        Neg,
        Eq,
        JumpIfFalse(isize), // relative jump if top is 0
        Jump(isize),        // unconditional relative jump
        Print,
    }

    #[test]
    fn ch23_compile_to_bytecode() {
        let (a, root) = sample();

        let result = fold_lang_multi(
            &a,
            root,
            |stmt: Stmt<Vec<Op>, Vec<Op>>| match stmt {
                Stmt::Let(name, mut val) => {
                    val.push(Op::Store(name));
                    val
                }
                Stmt::Seq(mut l, mut r) => {
                    l.append(&mut r);
                    l
                }
                Stmt::Print(mut v) => {
                    v.push(Op::Print);
                    v
                }
                Stmt::If(mut cond, mut t, mut e) => {
                    cond.push(Op::JumpIfFalse(t.len() as isize + 1));
                    cond.append(&mut t);
                    cond.push(Op::Jump(e.len() as isize));
                    cond.append(&mut e);
                    cond
                }
                Stmt::While(mut cond, mut body) => {
                    let body_len = body.len();
                    cond.push(Op::JumpIfFalse(body_len as isize + 1));
                    cond.append(&mut body);
                    cond.push(Op::Jump(-(cond.len() as isize)));
                    cond
                }
                Stmt::Noop => vec![],
            },
            |expr: Expr<Vec<Op>, Vec<Op>>| match expr {
                Expr::Lit(n) => vec![Op::Push(n)],
                Expr::Bool(b) => vec![Op::Push(if b { 1 } else { 0 })],
                Expr::Var(name) => vec![Op::Load(name)],
                Expr::Add(mut l, mut r) => {
                    l.append(&mut r);
                    l.push(Op::Add);
                    l
                }
                Expr::Mul(mut l, mut r) => {
                    l.append(&mut r);
                    l.push(Op::Mul);
                    l
                }
                Expr::Neg(mut e) => {
                    e.push(Op::Neg);
                    e
                }
                Expr::Eq(mut l, mut r) => {
                    l.append(&mut r);
                    l.push(Op::Eq);
                    l
                }
                Expr::Block(mut s, mut e) => {
                    s.append(&mut e);
                    s
                }
            },
        );

        let bytecode = result.unwrap_stmt();

        // Verify the compiled bytecode for our sample program:
        //   x = 1 + 2 * 3; y = -(x); if (x == 7) print(y) else print(x)
        assert_eq!(
            bytecode,
            vec![
                // x = 1 + 2 * 3
                Op::Push(1),
                Op::Push(2),
                Op::Push(3),
                Op::Mul,
                Op::Add,
                Op::Store("x".into()),
                // y = -(x)
                Op::Load("x".into()),
                Op::Neg,
                Op::Store("y".into()),
                // if (x == 7) ...
                Op::Load("x".into()),
                Op::Push(7),
                Op::Eq,
                Op::JumpIfFalse(3), // if false, skip 'then' block + Jump
                // then: print(y)
                Op::Load("y".into()),
                Op::Print,
                Op::Jump(2), // skip 'else'
                Op::Load("x".into()),
                Op::Print,
            ]
        );

        // Run the bytecode on a simple stack machine
        let (env, output) = run(&bytecode);
        assert_eq!(env["x"], 7);
        assert_eq!(env["y"], -7);
        assert_eq!(output, vec![-7]); // if (7==7) → true → print(y) → print(-7)
    }

    /// Stack machine: executes Vec<Op>, returns final env and printed values.
    fn run(code: &[Op]) -> (Env, Vec<i64>) {
        let mut stack: Vec<i64> = Vec::new();
        let mut env = Env::new();
        let mut output: Vec<i64> = Vec::new();
        let mut pc = 0;
        while pc < code.len() {
            match &code[pc] {
                Op::Push(n) => stack.push(*n),
                Op::Load(name) => stack.push(*env.get(name).unwrap_or(&0)),
                Op::Store(name) => {
                    let v = stack.pop().unwrap();
                    env.insert(name.clone(), v);
                }
                Op::Add => {
                    let r = stack.pop().unwrap();
                    let l = stack.pop().unwrap();
                    stack.push(l + r);
                }
                Op::Mul => {
                    let r = stack.pop().unwrap();
                    let l = stack.pop().unwrap();
                    stack.push(l * r);
                }
                Op::Neg => {
                    let v = stack.pop().unwrap();
                    stack.push(-v);
                }
                Op::Eq => {
                    let r = stack.pop().unwrap();
                    let l = stack.pop().unwrap();
                    stack.push(if l == r { 1 } else { 0 });
                }
                Op::JumpIfFalse(offset) => {
                    let v = stack.pop().unwrap();
                    if v == 0 {
                        pc = ((pc + 1) as isize + offset) as usize;
                        continue;
                    }
                }
                Op::Jump(offset) => {
                    pc = ((pc + 1) as isize + offset) as usize;
                    continue;
                }
                Op::Print => {
                    let v = stack.pop().unwrap();
                    output.push(v);
                }
            }
            pc += 1;
        }
        (env, output)
    }

    // ====================================================================
    // Chapter 24: Zipper — walk up and check siblings to find a binder
    // ====================================================================
    //
    // A Zipper is a cursor with a crumb trail — the only way to go
    // child → parent in an arena (arenas store parent → child, not
    // the reverse).
    //
    // Use case: you're at a variable reference Var("y") deep in the AST.
    // In this language, Let bindings are siblings in a Seq — not ancestors.
    // So to find the binder, you walk up to the enclosing Seq, then check
    // its left child. No fold can change direction like this.

    #[test]
    fn ch24_zipper_find_binder_via_sibling() {
        // x = 1 + 2 * 3; y = -(x); if (x == 7) print(y) else print(x)
        let (a, root) = sample();

        let mut z = Zipper::new(&a, root);

        // Navigate to Var("y") inside print(y):
        // Seq → Seq(Let("y"), If) → If → Print(Var("y")) → Var("y")
        z.down(1); // → Seq(Let("y",...), If(...))
        z.down(1); // → If(cond, then, else)
        z.down(1); // → Print(Var("y"))
        z.down(0); // → Var("y")
        assert!(matches!(z.focus(), Lang::ExprVar(n) if n == "y"));

        // Walk up to the nearest Seq, then check its left sibling for a Let
        z.up(); // → Print
        z.up(); // → If
        z.up(); // → Seq(Let("y",...), If(...))

        // The left sibling (child 0) of this Seq should be Let("y",...)
        z.down(0);
        assert!(matches!(z.focus(), Lang::StmtLet(n, _) if n == "y"));

        // We found the binding! This required going up AND sideways —
        // something only a zipper can do.
    }

    // ====================================================================
    // Chapter 25: ZipperMut — mark all ancestors of a node
    // ====================================================================
    //
    // ZipperMut overwrites nodes in place. All parents sharing that node
    // see the change. This is useful for propagating information upward
    // through the tree — something no bottom-up fold can do, because
    // folds produce new values, they don't mutate existing nodes.
    //
    // Here we find the Neg node and walk up to root, replacing every
    // literal we pass through with Lit(0) — a silly example, but it
    // shows the "walk up and mutate" pattern that only a zipper can do.

    #[test]
    fn ch24_zipper_mut_walk_up_and_patch() {
        // Build: Add(Lit(10), Mul(Lit(20), Neg(Lit(30))))
        let mut a: Arena<Lang<usize, usize>> = Arena::new();
        let n10 = a.push(Lang::ExprLit(10));
        let n20 = a.push(Lang::ExprLit(20));
        let n30 = a.push(Lang::ExprLit(30));
        let neg = a.push(Lang::ExprNeg(n30.0));
        let mul = a.push(Lang::ExprMul(n20.0, neg.0));
        let root = a.push(Lang::ExprAdd(n10.0, mul.0));

        // Navigate to Neg, then walk up and negate every Lit we encounter
        {
            let mut z = ZipperMut::new(&mut a, root);
            z.down(1); // Mul
            z.down(1); // Neg
            z.down(0); // Lit(30)

            // Negate this literal
            if let &Lang::ExprLit(n) = z.focus() {
                z.set_focus(Lang::ExprLit(-n));
            }

            // Walk up — at each level, check siblings for literals to negate
            while z.up() {
                // We're now at the parent. Check if it's a Lit (it won't be
                // in this tree, but the pattern is what matters).
            }
        }

        // Lit(30) is now Lit(-30), and since Neg(Lit(-30)) = -(-30) = 30
        let val = a.fold(root, |node: Lang<i64, i64>| match node {
            Lang::ExprLit(n) => n,
            Lang::ExprAdd(l, r) => l + r,
            Lang::ExprMul(l, r) => l * r,
            Lang::ExprNeg(e) => -e,
            _ => 0,
        });
        // Add(10, Mul(20, Neg(-30))) = 10 + 20 * 30 = 610
        assert_eq!(val, 610);
    }

    // ====================================================================
    // Chapter 26: ZipperCow — specialize one use of a shared subtree
    // ====================================================================
    //
    // In a hash-consed arena, identical subtrees share the same Id.
    // If you want to optimize ONE use of a shared subtree without
    // affecting the other, you need copy-on-write: rebuild the spine
    // from the edit point to the root, leaving the original intact.
    //
    // Here: two If branches both print the same expression. We want to
    // constant-fold only the "then" branch's copy.

    #[test]
    fn ch25_zipper_cow_specialize_shared_subtree() {
        // Two separate trees share a common subtree via the same arena.
        // Tree 1: Print(Add(1, 2))
        // Tree 2: Neg(Add(1, 2))   — same Add node!
        // We want to constant-fold the Add in tree 1 without affecting tree 2.
        let mut a: Arena<Lang<usize, usize>> = Arena::new();
        let one = a.push(Lang::ExprLit(1));
        let two = a.push(Lang::ExprLit(2));
        let shared_add = a.push(Lang::ExprAdd(one.0, two.0));
        let tree1_root = a.push(Lang::StmtPrint(shared_add.0));
        let tree2_root = a.push(Lang::ExprNeg(shared_add.0));

        // Both trees reference the same Add(1,2)
        assert_eq!(show(&a, tree1_root), "print((1 + 2))");
        assert_eq!(show(&a, tree2_root), "(-(1 + 2))");

        // COW-edit tree1: navigate into Print → Add, replace with Lit(3)
        let mut z = ZipperCow::new(&a, tree1_root);
        z.down(0); // → Add(1, 2)
        let (new_arena, new_root) = z.set_focus(Lang::ExprLit(3));

        // New tree1: print(3) — the Add was folded
        assert_eq!(show(&new_arena, new_root), "print(3)");

        // Original tree1 AND tree2 are completely untouched
        assert_eq!(show(&a, tree1_root), "print((1 + 2))");
        assert_eq!(show(&a, tree2_root), "(-(1 + 2))");
    }
}
