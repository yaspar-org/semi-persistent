// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#[cfg(test)]
mod tests {
    use semi_persistent_traversals::*;
    use semi_persistent_traversals_derive::rec_family;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    rec_family! {
        family Lang;

        enum Stmt {
            Assign(String, Expr),
            Seq(Stmt, Stmt),
            Print(Expr),
            If(Expr, Stmt, Stmt),
        }

        enum Expr {
            Var(String),
            Lit(i64),
            Add(Expr, Expr),
            Mul(Expr, Expr),
            Block(Stmt, Expr),
        }
    }

    type Ast = Arena<Lang<usize, usize>>;

    fn assign(a: &mut Ast, n: &str, e: Id) -> Id {
        a.push(Stmt::Assign(n.into(), e.0).into())
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
    fn var(a: &mut Ast, n: &str) -> Id {
        a.push(Expr::Var(n.into()).into())
    }
    fn lit(a: &mut Ast, n: i64) -> Id {
        a.push(Expr::Lit(n).into())
    }
    fn add(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Expr::Add(l.0, r.0).into())
    }
    fn mul(a: &mut Ast, l: Id, r: Id) -> Id {
        a.push(Expr::Mul(l.0, r.0).into())
    }
    fn block(a: &mut Ast, s: Id, e: Id) -> Id {
        a.push(Expr::Block(s.0, e.0).into())
    }

    // ========================================================================
    // Example 1: Precedence-aware pretty printer
    //
    //   Stmts  → String
    //   Exprs  → (String, u8)   (text + precedence level)
    // ========================================================================

    fn pretty(a: &Ast, root: Id) -> String {
        let result = fold_lang_multi(
            a,
            root,
            |stmt: Stmt<String, (String, u8)>| match stmt {
                Stmt::Assign(name, (val, _)) => format!("{name} = {val}"),
                Stmt::Seq(l, r) => format!("{l}; {r}"),
                Stmt::Print((e, _)) => format!("print({e})"),
                Stmt::If((cond, _), then_, else_) => format!("if {cond} then {then_} else {else_}"),
            },
            |expr: Expr<String, (String, u8)>| match expr {
                Expr::Var(name) => (name, 99),
                Expr::Lit(n) => (n.to_string(), 99),
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
                Expr::Block(s, (e, ep)) => (format!("{{ {s}; {e} }}"), ep),
            },
        );
        match result {
            LangRes::Stmt(s) => s,
            LangRes::Expr((s, _)) => s,
        }
    }

    #[test]
    fn pretty_adds_parens_for_add_in_mul() {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let four = lit(&mut a, 4);
        let sum1 = add(&mut a, one, two);
        let sum2 = add(&mut a, three, four);
        let root = mul(&mut a, sum1, sum2);
        assert_eq!(pretty(&a, root), "(1 + 2) * (3 + 4)");
    }

    #[test]
    fn pretty_no_parens_when_mul_in_add() {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let three = lit(&mut a, 3);
        let prod = mul(&mut a, two, three);
        let root = add(&mut a, one, prod);
        assert_eq!(pretty(&a, root), "1 + 2 * 3");
    }

    #[test]
    fn pretty_stmt_with_expr() {
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let two = lit(&mut a, 2);
        let sum = add(&mut a, one, two);
        let three = lit(&mut a, 3);
        let prod = mul(&mut a, sum, three);
        let root = print_(&mut a, prod);
        assert_eq!(pretty(&a, root), "print((1 + 2) * 3)");
    }

    // ========================================================================
    // Example 2: Interpreter
    //
    //   Stmts  → Rc<dyn Fn(&Env) -> Env>     (environment transformer)
    //   Exprs  → Rc<dyn Fn(&Env) -> i64>     (evaluator)
    //
    // The fold produces closures. Applying them to an environment runs the
    // program. Rc satisfies the Clone bound on fold_lang_multi.
    // ========================================================================

    type Env = HashMap<String, i64>;
    type SVal = Rc<dyn Fn(&Env) -> Env>;
    type EVal = Rc<dyn Fn(&Env) -> i64>;

    fn interp(a: &Ast, root: Id, env: &Env) -> Result<Env, i64> {
        let result = fold_lang_multi(
            a,
            root,
            |stmt: Stmt<SVal, EVal>| -> SVal {
                match stmt {
                    Stmt::Assign(name, val) => Rc::new(move |env| {
                        let v = val(env);
                        let mut e = env.clone();
                        e.insert(name.clone(), v);
                        e
                    }),
                    Stmt::Seq(l, r) => Rc::new(move |env| r(&l(env))),
                    Stmt::Print(val) => Rc::new(move |env| {
                        let _ = val(env);
                        env.clone()
                    }),
                    Stmt::If(cond, then_, else_) => Rc::new(move |env| {
                        if cond(env) != 0 {
                            then_(env)
                        } else {
                            else_(env)
                        }
                    }),
                }
            },
            |expr: Expr<SVal, EVal>| -> EVal {
                match expr {
                    Expr::Lit(n) => Rc::new(move |_| n),
                    Expr::Var(name) => Rc::new(move |env| *env.get(&name).unwrap_or(&0)),
                    Expr::Add(l, r) => Rc::new(move |env| l(env) + r(env)),
                    Expr::Mul(l, r) => Rc::new(move |env| l(env) * r(env)),
                    Expr::Block(s, e) => Rc::new(move |env| e(&s(env))),
                }
            },
        );
        match result {
            LangRes::Stmt(f) => Ok(f(env)),
            LangRes::Expr(f) => Err(f(env)),
        }
    }

    #[test]
    fn interp_basic() {
        // x = 10; y = x + 20
        let mut a = Ast::new();
        let ten = lit(&mut a, 10);
        let s1 = assign(&mut a, "x", ten);
        let x = var(&mut a, "x");
        let twenty = lit(&mut a, 20);
        let sum = add(&mut a, x, twenty);
        let s2 = assign(&mut a, "y", sum);
        let prog = seq(&mut a, s1, s2);

        let env = interp(&a, prog, &Env::new()).unwrap();
        assert_eq!(env["x"], 10);
        assert_eq!(env["y"], 30);
    }

    #[test]
    fn interp_block_expr() {
        // { x = 5; x } * 2
        let mut a = Ast::new();
        let five = lit(&mut a, 5);
        let s = assign(&mut a, "x", five);
        let x = var(&mut a, "x");
        let blk = block(&mut a, s, x);
        let two = lit(&mut a, 2);
        let root = mul(&mut a, blk, two);

        let val = interp(&a, root, &Env::new()).unwrap_err();
        assert_eq!(val, 10);
    }

    #[test]
    fn interp_if() {
        // if 1 then x = 42 else x = 0
        let mut a = Ast::new();
        let cond = lit(&mut a, 1);
        let v1 = lit(&mut a, 42);
        let then_ = assign(&mut a, "x", v1);
        let v2 = lit(&mut a, 0);
        let else_ = assign(&mut a, "x", v2);
        let root = if_(&mut a, cond, then_, else_);

        let env = interp(&a, root, &Env::new()).unwrap();
        assert_eq!(env["x"], 42);
    }

    // ========================================================================
    // Example 3: Free variable analysis
    //
    //   Stmts  → (defined: HashSet, free: HashSet)
    //   Exprs  → HashSet<String>
    // ========================================================================

    type Defs = HashSet<String>;
    type Frees = HashSet<String>;

    fn free_vars(a: &Ast, root: Id) -> HashSet<String> {
        let result = fold_lang_multi(
            a,
            root,
            |stmt: Stmt<(Defs, Frees), Frees>| -> (Defs, Frees) {
                match stmt {
                    Stmt::Assign(name, expr_free) => (HashSet::from([name]), expr_free),
                    Stmt::Seq((ld, lf), (rd, rf)) => {
                        let right_free: Frees = rf.difference(&ld).cloned().collect();
                        let free = lf.union(&right_free).cloned().collect();
                        let def = ld.union(&rd).cloned().collect();
                        (def, free)
                    }
                    Stmt::Print(expr_free) => (HashSet::new(), expr_free),
                    Stmt::If(cf, (_, tf), (_, ef)) => {
                        let free = cf
                            .union(&tf)
                            .cloned()
                            .collect::<Frees>()
                            .union(&ef)
                            .cloned()
                            .collect();
                        (HashSet::new(), free)
                    }
                }
            },
            |expr: Expr<(Defs, Frees), Frees>| -> Frees {
                match expr {
                    Expr::Var(name) => HashSet::from([name]),
                    Expr::Lit(_) => HashSet::new(),
                    Expr::Add(l, r) | Expr::Mul(l, r) => l.union(&r).cloned().collect(),
                    Expr::Block((def, sf), ef) => {
                        let ef: Frees = ef.difference(&def).cloned().collect();
                        sf.union(&ef).cloned().collect()
                    }
                }
            },
        );
        match result {
            LangRes::Stmt((_, free)) => free,
            LangRes::Expr(free) => free,
        }
    }

    #[test]
    fn free_vars_all_free() {
        let mut a = Ast::new();
        let x = var(&mut a, "x");
        let y = var(&mut a, "y");
        let root = add(&mut a, x, y);
        assert_eq!(free_vars(&a, root), HashSet::from(["x".into(), "y".into()]));
    }

    #[test]
    fn free_vars_all_bound() {
        // x = 1; print(x)
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let s1 = assign(&mut a, "x", one);
        let x = var(&mut a, "x");
        let s2 = print_(&mut a, x);
        let root = seq(&mut a, s1, s2);
        assert!(free_vars(&a, root).is_empty());
    }

    #[test]
    fn free_vars_mixed() {
        // x = y + 1; print(x)  — y is free
        let mut a = Ast::new();
        let y = var(&mut a, "y");
        let one = lit(&mut a, 1);
        let sum = add(&mut a, y, one);
        let s1 = assign(&mut a, "x", sum);
        let x = var(&mut a, "x");
        let s2 = print_(&mut a, x);
        let root = seq(&mut a, s1, s2);
        assert_eq!(free_vars(&a, root), HashSet::from(["y".into()]));
    }

    #[test]
    fn free_vars_block_scoping() {
        // { x = 1; x } + y  — x bound in block, y free
        let mut a = Ast::new();
        let one = lit(&mut a, 1);
        let s = assign(&mut a, "x", one);
        let x = var(&mut a, "x");
        let blk = block(&mut a, s, x);
        let y = var(&mut a, "y");
        let root = add(&mut a, blk, y);
        assert_eq!(free_vars(&a, root), HashSet::from(["y".into()]));
    }
}
