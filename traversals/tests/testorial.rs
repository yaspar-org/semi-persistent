// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Testorial: worked examples for every rec_family! scheme.
//!
//! A small imperative language is the running example. Each chapter is a
//! standalone `#[test]` covering one recursion scheme or technique.
//!
//! # API convention
//!
//! Every scheme takes **one closure per sort, in declaration order**. With
//! two sorts (Stmt, Expr), `fold` / `fold_short` / `rewrite` / etc. take two
//! closures. `fold_with_aux` and `fold_pair` take two closures per sort
//! (four total). Each sort can return a different type. Results are
//! sort-tagged via `LangStoreFoldResult<A_stmt, A_expr>`; unwrap with
//! `.unwrap_stmt()` / `.unwrap_expr()` when the root sort is known.
//!
//! ```text
//! Ch  What                    Scheme
//! ──  ──────────────────────  ──────────────────────────────────────
//!  0  The Language            rec_family!
//!  1  Pretty Print + Size     fold (multi-sorted by default)
//!  2  Constant Folding        rewrite
//!  3  Double Negation         rewrite
//!  4  Find Variable           fold_short
//!  5  Build from Seed         unfold
//!  6  Build with Reuse        unfold_short
//!  8  Desugar While           rewrite
//!  9  Type Inference          fold
//! 10  Interpreter             fold
//! 11  Free Variables          fold
//! 12  Precedence Print        fold
//! 13  Depth Complexity        fold_with_history
//! 14  Type Check + Eval       fold_with_aux
//! 15  Saturating Eval         fold_pair
//! 16  Simplify Before Eval    prefold
//! 17  Canonicalize Build      postunfold
//! 19  Top-Down Desugar        rewrite_down
//! 20  Cost Model              fold_with_original
//! 21  Dead Code Search        fold_short (multi-sorted early exit)
//! 22  Desugar Then Eval       prefold (multi-sorted)
//! 23  Bytecode Compiler       fold
//! 24  Zipper: Find Binder     Zipper
//! 25  Zipper: Patch Node      ZipperMut
//! 26  Zipper: Specialize      ZipperCow
//! ```

#[cfg(test)]
mod tests {
    use semi_persistent_traversals::*;
    use semi_persistent_traversals_derive::rec_family;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    // ====================================================================
    // Chapter 0: The Language (partitioned)
    // ====================================================================

    rec_family! {
        family Lang => LangStore;

        enum Stmt {
            Let(String, Expr),
            Seq(Stmt, Stmt),
            Print(Expr),
            If(Expr, Stmt, Stmt),
            While(Expr, Stmt),
            Noop,
        }

        enum Expr {
            Var(String),
            Lit(i64),
            Bool(bool),
            Add(Expr, Expr),
            Mul(Expr, Expr),
            Neg(Expr),
            Eq(Expr, Expr),
            Block(Stmt, Expr),
        }
    }

    // Smart constructors
    fn let_(s: &mut LangStore, n: &str, e: ExprId) -> StmtId {
        s.push_stmt(StmtNode::Let(n.into(), e))
    }
    fn seq(s: &mut LangStore, l: StmtId, r: StmtId) -> StmtId {
        s.push_stmt(StmtNode::Seq(l, r))
    }
    fn print_(s: &mut LangStore, e: ExprId) -> StmtId {
        s.push_stmt(StmtNode::Print(e))
    }
    fn if_(s: &mut LangStore, c: ExprId, t: StmtId, e: StmtId) -> StmtId {
        s.push_stmt(StmtNode::If(c, t, e))
    }
    fn while_(s: &mut LangStore, c: ExprId, b: StmtId) -> StmtId {
        s.push_stmt(StmtNode::While(c, b))
    }
    fn var(s: &mut LangStore, n: &str) -> ExprId {
        s.push_expr(ExprNode::Var(n.into()))
    }
    fn lit(s: &mut LangStore, n: i64) -> ExprId {
        s.push_expr(ExprNode::Lit(n))
    }
    fn bool_(s: &mut LangStore, b: bool) -> ExprId {
        s.push_expr(ExprNode::Bool(b))
    }
    fn add(s: &mut LangStore, l: ExprId, r: ExprId) -> ExprId {
        s.push_expr(ExprNode::Add(l, r))
    }
    fn mul(s: &mut LangStore, l: ExprId, r: ExprId) -> ExprId {
        s.push_expr(ExprNode::Mul(l, r))
    }
    fn neg(s: &mut LangStore, e: ExprId) -> ExprId {
        s.push_expr(ExprNode::Neg(e))
    }
    fn eq_(s: &mut LangStore, l: ExprId, r: ExprId) -> ExprId {
        s.push_expr(ExprNode::Eq(l, r))
    }

    /// Same sample program:
    /// x = 1 + 2 * 3; y = -(x); if (x == 7) print(y) else print(x)
    fn sample() -> (LangStore, LangStoreRoot) {
        let mut s = LangStore::new();
        let one = lit(&mut s, 1);
        let two = lit(&mut s, 2);
        let three = lit(&mut s, 3);
        let prod = mul(&mut s, two, three);
        let sum = add(&mut s, one, prod);
        let s1 = let_(&mut s, "x", sum);

        let x1 = var(&mut s, "x");
        let ny = neg(&mut s, x1);
        let s2 = let_(&mut s, "y", ny);

        let x2 = var(&mut s, "x");
        let seven = lit(&mut s, 7);
        let cond = eq_(&mut s, x2, seven);
        let y = var(&mut s, "y");
        let pr_y = print_(&mut s, y);
        let x3 = var(&mut s, "x");
        let pr_x = print_(&mut s, x3);
        let s3 = if_(&mut s, cond, pr_y, pr_x);

        let s23 = seq(&mut s, s2, s3);
        let prog = seq(&mut s, s1, s23);
        (s, LangStoreRoot::Stmt(prog))
    }

    // Helper: pretty-print via fold
    fn show(s: &LangStore, root: LangStoreRoot) -> String {
        let r = s.fold(
            root,
            |stmt: StmtNodeMapped<String, String>| match stmt {
                StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
                StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
                StmtNodeMapped::Print(e) => format!("print({e})"),
                StmtNodeMapped::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                StmtNodeMapped::While(c, b) => format!("while ({c}) {b}"),
                StmtNodeMapped::Noop => "noop".into(),
            },
            |expr: ExprNodeMapped<String, String>| match expr {
                ExprNodeMapped::Var(n) => n,
                ExprNodeMapped::Lit(n) => n.to_string(),
                ExprNodeMapped::Bool(b) => b.to_string(),
                ExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
                ExprNodeMapped::Mul(l, r) => format!("({l} * {r})"),
                ExprNodeMapped::Neg(e) => format!("(-{e})"),
                ExprNodeMapped::Eq(l, r) => format!("({l} == {r})"),
                ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
            },
        );
        match r { LangStoreFoldResult::Stmt(v) => v, LangStoreFoldResult::Expr(v) => v }
    }

    // ====================================================================
    // Chapter 1: Pretty Print + Size — fold
    // ====================================================================

    #[test]
    fn ch01_pretty_print_and_size() {
        let (s, root) = sample();
        assert_eq!(
            show(&s, root),
            "x = (1 + (2 * 3)); y = (-x); if ((x == 7)) print(y) else print(x)"
        );

        let size = s.fold(
            root,
            |stmt: StmtNodeMapped<usize, usize>| match stmt {
                StmtNodeMapped::Let(_, e) | StmtNodeMapped::Print(e) => 1 + e,
                StmtNodeMapped::Seq(l, r) => 1 + l + r,
                StmtNodeMapped::If(c, l, r) => 1 + c + l + r,
                StmtNodeMapped::While(c, b) => 1 + c + b,
                StmtNodeMapped::Noop => 1,
            },
            |expr: ExprNodeMapped<usize, usize>| match expr {
                ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) | ExprNodeMapped::Bool(_) => 1,
                ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => 1 + l + r,
                ExprNodeMapped::Neg(e) => 1 + e,
                ExprNodeMapped::Block(s, e) => 1 + s + e,
            },
        );
        assert_eq!(size.unwrap_stmt(), 19);
    }

    // ====================================================================
    // Chapter 4: Find Variable — fold_short
    // ====================================================================

    #[test]
    fn ch04_find_variable() {
        let (s, root) = sample();
        let found = s.fold_short(
            root,
            |stmt: StmtNodeMapped<bool, bool>| Ok(match stmt {
                StmtNodeMapped::Let(_, e) | StmtNodeMapped::Print(e) => e,
                StmtNodeMapped::Seq(l, r) | StmtNodeMapped::If(_, l, r) => l || r,
                StmtNodeMapped::While(c, b) => c || b,
                StmtNodeMapped::Noop => false,
            }),
            |expr: ExprNodeMapped<bool, bool>| match expr {
                ExprNodeMapped::Var(name) if name == "y" => Err(true),
                ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) | ExprNodeMapped::Bool(_) => Ok(false),
                ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => Ok(l || r),
                ExprNodeMapped::Neg(e) | ExprNodeMapped::Block(_, e) => Ok(e),
            },
        );
        assert!(matches!(found, LangStoreFoldResult::Expr(true)));
    }

    // ====================================================================
    // Chapter 9: Type Inference — fold (multi-sorted by default)
    // ====================================================================

    type TyEnv = HashMap<String, Ty>;
    type TyStmt = Rc<dyn Fn(&TyEnv) -> TyEnv>;
    type TyExpr = Rc<dyn Fn(&TyEnv) -> Ty>;

    #[derive(Clone, Debug, PartialEq)]
    enum Ty { Int, Bool, Unknown }

    #[test]
    fn ch09_type_inference() {
        let (s, root) = sample();
        let result = s.fold(
            root,
            |stmt: StmtNodeMapped<TyStmt, TyExpr>| -> TyStmt {
                match stmt {
                    StmtNodeMapped::Let(name, expr) => Rc::new(move |env| {
                        let ty = expr(env);
                        let mut e = env.clone();
                        e.insert(name.clone(), ty);
                        e
                    }),
                    StmtNodeMapped::Seq(l, r) => Rc::new(move |env| r(&l(env))),
                    StmtNodeMapped::Print(_) | StmtNodeMapped::Noop => Rc::new(|env| env.clone()),
                    StmtNodeMapped::If(_, t, e) => Rc::new(move |env| {
                        let mut m = t(env);
                        m.extend(e(env));
                        m
                    }),
                    StmtNodeMapped::While(_, b) => Rc::new(move |env| b(env)),
                }
            },
            |expr: ExprNodeMapped<TyStmt, TyExpr>| -> TyExpr {
                match expr {
                    ExprNodeMapped::Lit(_) => Rc::new(|_| Ty::Int),
                    ExprNodeMapped::Bool(_) => Rc::new(|_| Ty::Bool),
                    ExprNodeMapped::Var(name) => Rc::new(move |env| env.get(&name).cloned().unwrap_or(Ty::Unknown)),
                    ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) => Rc::new(move |env| {
                        if l(env) == Ty::Int && r(env) == Ty::Int { Ty::Int } else { Ty::Unknown }
                    }),
                    ExprNodeMapped::Neg(e) => Rc::new(move |env| e(env)),
                    ExprNodeMapped::Eq(_, _) => Rc::new(|_| Ty::Bool),
                    ExprNodeMapped::Block(s, e) => Rc::new(move |env| e(&s(env))),
                }
            },
        );
        let env = result.unwrap_stmt()(&TyEnv::new());
        assert_eq!(env["x"], Ty::Int);
        assert_eq!(env["y"], Ty::Int);
    }

    // ====================================================================
    // Chapter 10: Interpreter — fold
    // ====================================================================

    type Env = HashMap<String, i64>;
    type SVal = Rc<dyn Fn(&Env) -> Env>;
    type EVal = Rc<dyn Fn(&Env) -> i64>;

    #[test]
    fn ch10_interpreter() {
        let (s, root) = sample();
        let result = s.fold(
            root,
            |stmt: StmtNodeMapped<SVal, EVal>| -> SVal {
                match stmt {
                    StmtNodeMapped::Let(name, val) => Rc::new(move |env| {
                        let mut e = env.clone();
                        e.insert(name.clone(), val(env));
                        e
                    }),
                    StmtNodeMapped::Seq(l, r) => Rc::new(move |env| r(&l(env))),
                    StmtNodeMapped::Print(v) => Rc::new(move |env| { let _ = v(env); env.clone() }),
                    StmtNodeMapped::If(c, t, e) => Rc::new(move |env| if c(env) != 0 { t(env) } else { e(env) }),
                    StmtNodeMapped::While(c, b) => Rc::new(move |env| {
                        let mut e = env.clone();
                        while c(&e) != 0 { e = b(&e); }
                        e
                    }),
                    StmtNodeMapped::Noop => Rc::new(|env| env.clone()),
                }
            },
            |expr: ExprNodeMapped<SVal, EVal>| -> EVal {
                match expr {
                    ExprNodeMapped::Lit(n) => Rc::new(move |_| n),
                    ExprNodeMapped::Bool(b) => Rc::new(move |_| if b { 1 } else { 0 }),
                    ExprNodeMapped::Var(name) => Rc::new(move |env| *env.get(&name).unwrap_or(&0)),
                    ExprNodeMapped::Add(l, r) => Rc::new(move |env| l(env) + r(env)),
                    ExprNodeMapped::Mul(l, r) => Rc::new(move |env| l(env) * r(env)),
                    ExprNodeMapped::Neg(e) => Rc::new(move |env| -e(env)),
                    ExprNodeMapped::Eq(l, r) => Rc::new(move |env| if l(env) == r(env) { 1 } else { 0 }),
                    ExprNodeMapped::Block(s, e) => Rc::new(move |env| e(&s(env))),
                }
            },
        );
        let env = result.unwrap_stmt()(&Env::new());
        assert_eq!(env["x"], 7);
        assert_eq!(env["y"], -7);
    }

    // ====================================================================
    // Chapter 11: Free Variables — fold
    // ====================================================================

    type Defs = HashSet<String>;
    type Frees = HashSet<String>;

    #[test]
    fn ch11_free_vars() {
        let (s, root) = sample();
        let result = s.fold(
            root,
            |stmt: StmtNodeMapped<(Defs, Frees), Frees>| -> (Defs, Frees) {
                match stmt {
                    StmtNodeMapped::Let(name, ef) => (HashSet::from([name]), ef),
                    StmtNodeMapped::Seq((ld, lf), (rd, rf)) => {
                        let rf: Frees = rf.difference(&ld).cloned().collect();
                        (ld.union(&rd).cloned().collect(), lf.union(&rf).cloned().collect())
                    }
                    StmtNodeMapped::Print(ef) => (HashSet::new(), ef),
                    StmtNodeMapped::While(cf, (_, bf)) => (HashSet::new(), cf.union(&bf).cloned().collect()),
                    StmtNodeMapped::If(cf, (_, tf), (_, ef)) => (
                        HashSet::new(),
                        cf.union(&tf).cloned().collect::<Frees>().union(&ef).cloned().collect(),
                    ),
                    StmtNodeMapped::Noop => (HashSet::new(), HashSet::new()),
                }
            },
            |expr: ExprNodeMapped<(Defs, Frees), Frees>| -> Frees {
                match expr {
                    ExprNodeMapped::Var(n) => HashSet::from([n]),
                    ExprNodeMapped::Lit(_) | ExprNodeMapped::Bool(_) => HashSet::new(),
                    ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => l.union(&r).cloned().collect(),
                    ExprNodeMapped::Neg(e) => e,
                    ExprNodeMapped::Block((def, sf), ef) => {
                        let ef: Frees = ef.difference(&def).cloned().collect();
                        sf.union(&ef).cloned().collect()
                    }
                }
            },
        );
        let (_, free) = result.unwrap_stmt();
        assert!(free.is_empty());
    }

    // ====================================================================
    // Chapter 12: Precedence Print — fold
    // ====================================================================

    #[test]
    fn ch12_precedence_print() {
        let mut s = LangStore::new();
        let one = lit(&mut s, 1);
        let two = lit(&mut s, 2);
        let three = lit(&mut s, 3);
        let four = lit(&mut s, 4);
        let sum = add(&mut s, one, two);
        let sum2 = add(&mut s, three, four);
        let root = mul(&mut s, sum, sum2);

        let result = s.fold(
            LangStoreRoot::Expr(root),
            |stmt: StmtNodeMapped<String, (String, u8)>| match stmt {
                StmtNodeMapped::Let(n, (v, _)) => format!("{n} = {v}"),
                StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
                StmtNodeMapped::Print((e, _)) => format!("print({e})"),
                StmtNodeMapped::If((c, _), t, e) => format!("if ({c}) {t} else {e}"),
                StmtNodeMapped::While((c, _), b) => format!("while ({c}) {b}"),
                StmtNodeMapped::Noop => "noop".into(),
            },
            |expr: ExprNodeMapped<String, (String, u8)>| match expr {
                ExprNodeMapped::Var(n) => (n, 99),
                ExprNodeMapped::Lit(n) => (n.to_string(), 99),
                ExprNodeMapped::Bool(b) => (b.to_string(), 99),
                ExprNodeMapped::Add((l, lp), (r, rp)) => {
                    let l = if lp < 1 { format!("({l})") } else { l };
                    let r = if rp <= 1 { format!("({r})") } else { r };
                    (format!("{l} + {r}"), 1)
                }
                ExprNodeMapped::Mul((l, lp), (r, rp)) => {
                    let l = if lp < 2 { format!("({l})") } else { l };
                    let r = if rp <= 2 { format!("({r})") } else { r };
                    (format!("{l} * {r}"), 2)
                }
                ExprNodeMapped::Neg((e, _)) => (format!("-{e}"), 99),
                ExprNodeMapped::Eq((l, _), (r, _)) => (format!("{l} == {r}"), 0),
                ExprNodeMapped::Block(_, (e, ep)) => (format!("{{ {e} }}"), ep),
            },
        );
        assert_eq!(result.unwrap_expr().0, "(1 + 2) * (3 + 4)");
    }

    // ====================================================================
    // Chapter 2: Constant Folding — rewrite
    // ====================================================================

    #[test]
    fn ch02_constant_fold() {
        let (s, root) = sample();
        let (s2, r2) = s.rewrite(
            root,
            |node, new: &mut LangStore| match node {
                StmtNode::While(c, b) => {
                    // Desugar while: If(c, Seq(b, While(c, b)), Noop)
                    // (not needed here, just pass through)
                    new.push_stmt(StmtNode::While(c, b))
                }
                other => new.push_stmt(other),
            },
            |node, new: &mut LangStore| match node {
                ExprNode::Add(l, r) => {
                    if let (ExprNode::Lit(a), ExprNode::Lit(b)) = (new.get_expr(l), new.get_expr(r)) {
                        return new.push_expr(ExprNode::Lit(a + b));
                    }
                    new.push_expr(ExprNode::Add(l, r))
                }
                ExprNode::Mul(l, r) => {
                    if let (ExprNode::Lit(a), ExprNode::Lit(b)) = (new.get_expr(l), new.get_expr(r)) {
                        return new.push_expr(ExprNode::Lit(a * b));
                    }
                    new.push_expr(ExprNode::Mul(l, r))
                }
                ExprNode::Neg(e) => {
                    if let ExprNode::Lit(n) = new.get_expr(e) {
                        return new.push_expr(ExprNode::Lit(-n));
                    }
                    new.push_expr(ExprNode::Neg(e))
                }
                ExprNode::Eq(l, r) => {
                    if let (ExprNode::Lit(a), ExprNode::Lit(b)) = (new.get_expr(l), new.get_expr(r)) {
                        return new.push_expr(ExprNode::Bool(a == b));
                    }
                    new.push_expr(ExprNode::Eq(l, r))
                }
                other => new.push_expr(other),
            },
        );
        assert_eq!(
            show(&s2, r2),
            "x = 7; y = (-x); if ((x == 7)) print(y) else print(x)"
        );
    }

    // ====================================================================
    // Chapter 3: Double Negation — rewrite
    // ====================================================================

    #[test]
    fn ch03_double_negation() {
        let mut s = LangStore::new();
        let five = lit(&mut s, 5);
        let n1 = neg(&mut s, five);
        let n2 = neg(&mut s, n1);
        let n3 = neg(&mut s, n2);
        let root = print_(&mut s, n3);

        let (s2, r2) = s.rewrite(
            LangStoreRoot::Stmt(root),
            |node, new: &mut LangStore| new.push_stmt(node),
            |node, new: &mut LangStore| match node {
                ExprNode::Neg(inner) => match new.get_expr(inner) {
                    ExprNode::Neg(x) => *x, // skip two Negs
                    _ => new.push_expr(ExprNode::Neg(inner)),
                },
                other => new.push_expr(other),
            },
        );
        assert_eq!(show(&s2, r2), "print((-5))");
    }

    // ====================================================================
    // Chapter 8: Desugar While — rewrite
    // ====================================================================

    #[test]
    fn ch08_desugar_while() {
        let mut s = LangStore::new();
        let x = var(&mut s, "x");
        let zero = lit(&mut s, 0);
        let cond = eq_(&mut s, x, zero);
        let x2 = var(&mut s, "x");
        let body = print_(&mut s, x2);
        let root = while_(&mut s, cond, body);

        assert_eq!(show(&s, LangStoreRoot::Stmt(root)), "while ((x == 0)) print(x)");

        let (s2, r2) = s.rewrite(
            LangStoreRoot::Stmt(root),
            |node, new: &mut LangStore| match node {
                StmtNode::While(c, b) => {
                    let while_again = new.push_stmt(StmtNode::While(c, b));
                    let seq = new.push_stmt(StmtNode::Seq(b, while_again));
                    let noop = new.push_stmt(StmtNode::Noop);
                    new.push_stmt(StmtNode::If(c, seq, noop))
                }
                other => new.push_stmt(other),
            },
            |node, new: &mut LangStore| new.push_expr(node),
        );
        assert_eq!(
            show(&s2, r2),
            "if ((x == 0)) print(x); while ((x == 0)) print(x) else noop"
        );
    }

    // ====================================================================
    // Chapter 5: Build from Seed — unfold
    // ====================================================================

    #[test]
    fn ch05_generate_ast() {
        let mut s = LangStore::new();
        let root = s.unfold(
            LangStoreSeed::Expr(3u32),
            |seed| match seed {
                LangStoreSeed::Expr(0) => LangStoreLayer::Expr(ExprNode::Lit(1), vec![]),
                LangStoreSeed::Expr(n) => LangStoreLayer::Expr(
                    ExprNode::Add(ExprId(0), ExprId(0)),
                    vec![LangStoreSeed::Expr(n - 1), LangStoreSeed::Expr(n - 1)],
                ),
                LangStoreSeed::Stmt(_) => unreachable!(),
            },
        );
        let val = s.fold(
            root,
            |_: StmtNodeMapped<i64, i64>| 0i64,
            |expr: ExprNodeMapped<i64, i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(l, r) => l + r,
                _ => 0,
            },
        );
        assert_eq!(val.unwrap_expr(), 8);
    }

    // ====================================================================
    // Chapter 6: Build with Reuse — unfold_short
    // ====================================================================

    #[test]
    fn ch06_build_with_reuse() {
        let mut s = LangStore::new();
        let shared = lit(&mut s, 42);
        let root = s.unfold_short(
            LangStoreSeed::Expr(2u32),
            |seed| match seed {
                LangStoreSeed::Expr(0) => LangStoreApoLayer::Expr(
                    ExprNode::Neg(ExprId(0)),
                    vec![LangStoreApoSeed::DoneExpr(shared)],
                ),
                LangStoreSeed::Expr(n) => LangStoreApoLayer::Expr(
                    ExprNode::Add(ExprId(0), ExprId(0)),
                    vec![LangStoreApoSeed::Continue(LangStoreSeed::Expr(n - 1)), LangStoreApoSeed::Continue(LangStoreSeed::Expr(n - 1))],
                ),
                LangStoreSeed::Stmt(_) => unreachable!(),
            },
        );
        let val = s.fold(
            root,
            |_: StmtNodeMapped<i64, i64>| 0i64,
            |expr: ExprNodeMapped<i64, i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(l, r) => l + r,
                ExprNodeMapped::Neg(e) => -e,
                _ => 0,
            },
        );
        // 2^2 leaves, each Neg(42) = -42, then summed: -42 * 4 = -168
        assert_eq!(val.unwrap_expr(), -168);
    }

    // ====================================================================
    // Chapter 13: Depth Complexity — fold_with_history
    // ====================================================================

    #[test]
    fn ch13_complexity_with_history() {
        let (s, root) = sample();
        let complexity = s.fold_with_history(
            root,
            |stmt: StmtNodeMapped<Ann<usize>, Ann<usize>>| match stmt {
                StmtNodeMapped::Let(_, e) | StmtNodeMapped::Print(e) => 1 + e.value,
                StmtNodeMapped::Seq(l, r) => 1 + l.value + r.value,
                StmtNodeMapped::If(c, t, e) => 1 + c.value + t.value + e.value,
                StmtNodeMapped::While(c, b) => 1 + c.value + b.value,
                StmtNodeMapped::Noop => 1,
            },
            |expr: ExprNodeMapped<Ann<usize>, Ann<usize>>| {
                let penalty = match &expr {
                    ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => {
                        let l_deep = !l.children.is_empty();
                        let r_deep = !r.children.is_empty();
                        if l_deep && r_deep { 2 } else if l_deep || r_deep { 1 } else { 0 }
                    }
                    _ => 0,
                };
                let base = match expr {
                    ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) | ExprNodeMapped::Bool(_) => 1,
                    ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => 1 + l.value + r.value,
                    ExprNodeMapped::Neg(e) | ExprNodeMapped::Block(_, e) => 1 + e.value,
                };
                base + penalty
            },
        );
        assert!(complexity.unwrap_stmt() > 16);
    }

    // ====================================================================
    // Chapter 14: Type Check + Eval — fold_with_aux
    // ====================================================================

    #[test]
    fn ch14_zygo_typecheck_eval() {
        let mut s = LangStore::new();
        let one = lit(&mut s, 1);
        let two = lit(&mut s, 2);
        let three = lit(&mut s, 3);
        let prod = mul(&mut s, two, three);
        let root = add(&mut s, one, prod);

        let result = s.fold_with_aux(
            LangStoreRoot::Expr(root),
            // aux: type check
            |_: StmtNodeMapped<&str, &str>| "stmt",
            |expr: ExprNodeMapped<&str, &str>| match expr {
                ExprNodeMapped::Lit(_) => "int",
                ExprNodeMapped::Bool(_) => "bool",
                ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) => {
                    if l == "int" && r == "int" { "int" } else { "err" }
                }
                _ => "unknown",
            },
            // main: evaluate with type info
            |_: StmtNodeMapped<(i64, &str), (i64, &str)>| 0i64,
            |expr: ExprNodeMapped<(i64, &str), (i64, &str)>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add((l, lt), (r, rt)) => if lt == "int" && rt == "int" { l + r } else { -1 },
                ExprNodeMapped::Mul((l, lt), (r, rt)) => if lt == "int" && rt == "int" { l * r } else { -1 },
                _ => 0,
            },
        );
        assert_eq!(result.unwrap_expr(), 7);
    }

    // ====================================================================
    // Chapter 15: Saturating Eval — fold_pair (mutual recursion)
    // ====================================================================

    #[test]
    fn ch15_mutu_saturating() {
        let mut s = LangStore::new();
        let h = lit(&mut s, 100);
        let h2 = lit(&mut s, 100);
        let root = add(&mut s, h, h2);

        let result = s.fold_pair(
            LangStoreRoot::Expr(root),
            // stmt A alg: unused
            |_: StmtNodeMapped<(i64, bool), (i64, bool)>| 0i64,
            // stmt B alg: unused
            |_: StmtNodeMapped<(i64, bool), (i64, bool)>| false,
            // expr A alg: clamped value
            |expr: ExprNodeMapped<(i64, bool), (i64, bool)>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add((l, _), (r, _)) => { let s = l + r; if s > 127 { 127 } else { s } }
                ExprNodeMapped::Mul((l, _), (r, _)) => { let p = l * r; if p > 127 { 127 } else { p } }
                ExprNodeMapped::Neg((v, _)) => -v,
                _ => 0,
            },
            // expr B alg: overflow flag
            |expr: ExprNodeMapped<(i64, bool), (i64, bool)>| match expr {
                ExprNodeMapped::Lit(_) => false,
                ExprNodeMapped::Add((l, lo), (r, ro)) => lo || ro || (l + r) > 127,
                ExprNodeMapped::Mul((l, lo), (r, ro)) => lo || ro || (l * r) > 127,
                ExprNodeMapped::Neg((_, o)) => o,
                _ => false,
            },
        );
        let (value, overflows) = result.unwrap_expr();
        assert_eq!(value, 127);
        assert!(overflows);
    }

    // ====================================================================
    // Chapter 16: Simplify Before Eval — prefold
    // ====================================================================

    #[test]
    fn ch16_prepro_normalize() {
        let mut s = LangStore::new();
        let two = lit(&mut s, 2);
        let three = lit(&mut s, 3);
        let root = mul(&mut s, two, three);

        let result = s.prefold(
            LangStoreRoot::Expr(root),
            |stmt: StmtNode| stmt,
            |expr: ExprNode| match expr {
                ExprNode::Mul(l, r) => ExprNode::Add(l, r),
                other => other,
            },
            |_: StmtNodeMapped<i64, i64>| 0i64,
            |expr: ExprNodeMapped<i64, i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(l, r) => l + r,
                ExprNodeMapped::Mul(l, r) => l * r,
                _ => 0,
            },
        );
        // Mul(2,3) -> Add(2,3) -> 5
        assert_eq!(result.unwrap_expr(), 5);
    }

    // ====================================================================
    // Chapter 22: Desugar Then Evaluate — prefold (multi-sorted)
    // ====================================================================

    #[test]
    fn ch22_prefold_multi() {
        let mut s = LangStore::new();
        let two = lit(&mut s, 2);
        let three = lit(&mut s, 3);
        let prod = mul(&mut s, two, three);
        let root = print_(&mut s, prod);

        let result = s.prefold(
            LangStoreRoot::Stmt(root),
            |stmt: StmtNode| stmt,
            |expr: ExprNode| match expr {
                ExprNode::Mul(l, r) => ExprNode::Add(l, r),
                other => other,
            },
            |stmt: StmtNodeMapped<String, i64>| match stmt {
                StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
                StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
                StmtNodeMapped::Print(v) => format!("print({v})"),
                StmtNodeMapped::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                StmtNodeMapped::While(c, b) => format!("while ({c}) {b}"),
                StmtNodeMapped::Noop => "noop".into(),
            },
            |expr: ExprNodeMapped<String, i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(l, r) => l + r,
                ExprNodeMapped::Mul(l, r) => l * r,
                ExprNodeMapped::Neg(e) => -e,
                _ => 0,
            },
        );
        assert_eq!(result.unwrap_stmt(), "print(5)");
    }

    // ====================================================================
    // Chapter 17: Canonicalize During Build — postunfold
    // ====================================================================

    #[test]
    fn ch17_postpro_canonicalize() {
        let mut s = LangStore::new();
        let root = s.postunfold(
            LangStoreSeed::Expr(3u32),
            |stmt: StmtNode| stmt,
            |expr: ExprNode| match expr {
                ExprNode::Add(l, r) if l.0 > r.0 => ExprNode::Add(r, l),
                other => other,
            },
            |seed| match seed {
                LangStoreSeed::Expr(0) => LangStoreLayer::Expr(ExprNode::Lit(0), vec![]),
                LangStoreSeed::Expr(n) => LangStoreLayer::Expr(
                    ExprNode::Add(ExprId(0), ExprId(0)),
                    vec![LangStoreSeed::Expr(n - 1), LangStoreSeed::Expr(n - 1)],
                ),
                LangStoreSeed::Stmt(_) => unreachable!(),
            },
        );
        // Verify canonicalization: in every Add node, left id <= right id
        for i in 0..s.len_expr() {
            if let ExprNode::Add(l, r) = s.get_expr(ExprId(i)) {
                assert!(l.0 <= r.0, "Add({}, {}) not canonical", l.0, r.0);
            }
        }
        let _ = root;
    }

    // ====================================================================
    // Chapter 19: Top-Down Desugar — rewrite_down
    // ====================================================================

    #[test]
    fn ch19_transform_down() {
        let mut s = LangStore::new();
        let five = lit(&mut s, 5);
        let n1 = neg(&mut s, five);
        let root = neg(&mut s, n1);

        let (s2, r2) = s.rewrite_down(
            LangStoreRoot::Expr(root),
            |stmt: StmtNode| stmt,
            |expr: ExprNode| match expr {
                ExprNode::Neg(inner) => ExprNode::Mul(inner, inner),
                other => other,
            },
        );
        let val = s2.fold(
            r2,
            |_: StmtNodeMapped<i64, i64>| 0i64,
            |expr: ExprNodeMapped<i64, i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Mul(l, r) => l * r,
                _ => 0,
            },
        );
        assert_eq!(val.unwrap_expr(), 625);
    }

    // ====================================================================
    // Chapter 24: Zipper — find binder via sibling
    // ====================================================================

    #[test]
    fn ch24_zipper_find_binder_via_sibling() {
        let (store, root) = sample();
        let mut z = LangStoreZipper::new(&store, root);

        // Navigate: Seq → Seq(Let("y"), If) → If → Print(Var("y")) → Var("y")
        assert!(z.down(1));
        assert!(z.down(1));
        assert!(z.down(1));
        assert!(z.down(0));
        match z.focus() {
            LangStoreRoot::Expr(id) => assert!(matches!(store.get_expr(id), ExprNode::Var(n) if n == "y")),
            _ => panic!("expected Expr"),
        }

        // Walk up: Print → If → Seq(Let("y"), If)
        assert!(z.up());
        assert!(z.up());
        assert!(z.up());

        // Left sibling should be Let("y", ...)
        assert!(z.down(0));
        match z.focus() {
            LangStoreRoot::Stmt(id) => assert!(matches!(store.get_stmt(id), StmtNode::Let(n, _) if n == "y")),
            _ => panic!("expected Stmt"),
        }
    }

    // ====================================================================
    // Chapter 25: ZipperMut — in-place mutation
    // ====================================================================

    #[test]
    fn ch25_zipper_mut_walk_up_and_patch() {
        let mut s = LangStore::new();
        let n10 = lit(&mut s, 10);
        let n20 = lit(&mut s, 20);
        let n30 = lit(&mut s, 30);
        let ng = neg(&mut s, n30);
        let m = mul(&mut s, n20, ng);
        let root = add(&mut s, n10, m);

        {
            let mut z = LangStoreZipperMut::new(&mut s, LangStoreRoot::Expr(root));
            z.down(1); // Mul
            z.down(1); // Neg
            z.down(0); // Lit(30)
            if let LangStoreRoot::Expr(id) = z.focus() {
                if let ExprNode::Lit(n) = z.store.get_expr(id).clone() {
                    z.set_focus_expr(ExprNode::Lit(-n));
                }
            }
        }

        // Add(10, Mul(20, Neg(-30))) = 10 + 20 * 30 = 610
        let val = s.fold(
            LangStoreRoot::Expr(root),
            |_: StmtNodeMapped<i64, i64>| 0i64,
            |e: ExprNodeMapped<i64, i64>| match e {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(l, r) => l + r,
                ExprNodeMapped::Mul(l, r) => l * r,
                ExprNodeMapped::Neg(x) => -x,
                _ => 0,
            },
        );
        assert_eq!(val.unwrap_expr(), 610);
    }

    // ====================================================================
    // Chapter 26: ZipperCow — specialize shared subtree
    // ====================================================================

    #[test]
    fn ch26_zipper_cow_specialize_shared_subtree() {
        let mut s = LangStore::new();
        let one = lit(&mut s, 1);
        let two = lit(&mut s, 2);
        let shared_add = add(&mut s, one, two);
        let tree1_root = print_(&mut s, shared_add);
        let tree2_root = neg(&mut s, shared_add);

        assert_eq!(show(&s, LangStoreRoot::Stmt(tree1_root)), "print((1 + 2))");
        assert_eq!(show(&s, LangStoreRoot::Expr(tree2_root)), "(-(1 + 2))");

        // COW-edit tree1: navigate Print → Add, replace Add with Lit(3)
        let mut z = LangStoreZipperCow::new(&s, LangStoreRoot::Stmt(tree1_root));
        z.down(0); // → Add
        let (new_store, new_root) = z.set_focus_expr(ExprNode::Lit(3));

        assert_eq!(show(&new_store, new_root), "print(3)");

        // Original store untouched
        assert_eq!(show(&s, LangStoreRoot::Stmt(tree1_root)), "print((1 + 2))");
        assert_eq!(show(&s, LangStoreRoot::Expr(tree2_root)), "(-(1 + 2))");
    }

    // ====================================================================
    // Memoization strategy: exercise Sparse path
    // ====================================================================

    #[test]
    fn memo_strategy_sparse_fold_matches_dense() {
        use semi_persistent_traversals::Sparse;

        let (s, root) = sample();
        let dense = show(&s, root);

        // Same fold via sparse strategy
        let sparse_result = s.with_strategy::<Sparse>().fold(
            root,
            |stmt: StmtNodeMapped<String, String>| match stmt {
                StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
                StmtNodeMapped::Seq(l, r) => format!("{l}; {r}"),
                StmtNodeMapped::Print(e) => format!("print({e})"),
                StmtNodeMapped::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                StmtNodeMapped::While(c, b) => format!("while ({c}) {b}"),
                StmtNodeMapped::Noop => "noop".into(),
            },
            |expr: ExprNodeMapped<String, String>| match expr {
                ExprNodeMapped::Var(n) => n,
                ExprNodeMapped::Lit(n) => n.to_string(),
                ExprNodeMapped::Bool(b) => b.to_string(),
                ExprNodeMapped::Add(l, r) => format!("({l} + {r})"),
                ExprNodeMapped::Mul(l, r) => format!("({l} * {r})"),
                ExprNodeMapped::Neg(e) => format!("(-{e})"),
                ExprNodeMapped::Eq(l, r) => format!("({l} == {r})"),
                ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
            },
        );
        let sparse = match sparse_result {
            LangStoreFoldResult::Stmt(v) => v,
            LangStoreFoldResult::Expr(v) => v,
        };
        assert_eq!(sparse, dense);
    }

    #[test]
    fn memo_strategy_sparse_transform_matches_dense() {
        use semi_persistent_traversals::Sparse;

        let (s, root) = sample();
        let (dense_store, dense_root) = s.rewrite(
            root,
            |n, new: &mut LangStore| new.push_stmt(n),
            |n, new: &mut LangStore| new.push_expr(n),
        );
        let (sparse_store, sparse_root) = s.with_strategy::<Sparse>().rewrite(
            root,
            |n, new: &mut LangStore| new.push_stmt(n),
            |n, new: &mut LangStore| new.push_expr(n),
        );
        assert_eq!(show(&dense_store, dense_root), show(&sparse_store, sparse_root));
    }

    // ====================================================================
    // Hash-consing (dedup): new_dedup returns existing ids for identical nodes
    // ====================================================================

    #[test]
    fn dedup_identical_expr_nodes_share_id() {
        let mut s = LangStore::new_dedup();
        let a1 = s.push_expr(ExprNode::Lit(42));
        let a2 = s.push_expr(ExprNode::Lit(42));
        assert_eq!(a1, a2);
        assert_eq!(s.len_expr(), 1);

        // Different literals get different ids
        let b = s.push_expr(ExprNode::Lit(7));
        assert_ne!(a1, b);

        // Structural dedup: Add(Lit(1), Lit(2)) pushed twice shares
        let one = s.push_expr(ExprNode::Lit(1));
        let two = s.push_expr(ExprNode::Lit(2));
        let sum1 = s.push_expr(ExprNode::Add(one, two));
        let one2 = s.push_expr(ExprNode::Lit(1));
        let two2 = s.push_expr(ExprNode::Lit(2));
        let sum2 = s.push_expr(ExprNode::Add(one2, two2));
        assert_eq!(one, one2);
        assert_eq!(two, two2);
        assert_eq!(sum1, sum2);
    }

    #[test]
    fn dedup_per_sort_isolated() {
        let mut s = LangStore::new_dedup();
        // Stmt and Expr dedup tables are independent.
        let e = s.push_expr(ExprNode::Lit(1));
        let stmt1 = s.push_stmt(StmtNode::Print(e));
        let stmt2 = s.push_stmt(StmtNode::Print(e));
        assert_eq!(stmt1, stmt2);
        assert_eq!(s.len_stmt(), 1);
        assert_eq!(s.len_expr(), 1);
    }

    #[test]
    fn dedup_disabled_by_default() {
        let mut s = LangStore::new();
        let a1 = s.push_expr(ExprNode::Lit(42));
        let a2 = s.push_expr(ExprNode::Lit(42));
        assert_ne!(a1, a2);
        assert_eq!(s.len_expr(), 2);
    }

    #[test]
    fn dedup_mark_restore_prunes_stale_entries() {
        let mut s = LangStore::new_dedup();
        let mark = s.mark();
        let _a = s.push_expr(ExprNode::Lit(42));
        assert_eq!(s.len_expr(), 1);
        s.restore(&mark);
        assert_eq!(s.len_expr(), 0);

        // After restore, the same node is brand-new — should get id 0 again.
        let b = s.push_expr(ExprNode::Lit(42));
        assert_eq!(b.0, 0);
        assert_eq!(s.len_expr(), 1);
    }

    // ====================================================================
    // Chapter 20: Cost Model — fold_with_original
    // ====================================================================

    #[test]
    fn ch20_fold_with_original_cost() {
        let (s, root) = sample();
        let cost = s.fold_with_original(
            root,
            |orig: &StmtNode, mapped: StmtNodeMapped<usize, usize>| {
                let child_cost = match mapped {
                    StmtNodeMapped::Let(_, e) | StmtNodeMapped::Print(e) => e,
                    StmtNodeMapped::Seq(l, r) => l + r,
                    StmtNodeMapped::If(c, t, e) => c + t + e,
                    StmtNodeMapped::While(c, b) => c + b,
                    StmtNodeMapped::Noop => 0,
                };
                let own = match orig {
                    StmtNode::If(..) => 1,
                    _ => 0,
                };
                child_cost + own
            },
            |orig: &ExprNode, mapped: ExprNodeMapped<usize, usize>| {
                let child_cost = match mapped {
                    ExprNodeMapped::Var(_) | ExprNodeMapped::Lit(_) | ExprNodeMapped::Bool(_) => 0,
                    ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) | ExprNodeMapped::Eq(l, r) => l + r,
                    ExprNodeMapped::Neg(e) | ExprNodeMapped::Block(_, e) => e,
                };
                let own = match orig {
                    ExprNode::Add(..) | ExprNode::Mul(..) | ExprNode::Eq(..) => 2,
                    ExprNode::Neg(..) => 1,
                    _ => 0,
                };
                child_cost + own
            },
        );
        assert_eq!(cost.unwrap_stmt(), 8);
    }

    // ====================================================================
    // Chapter 23: Bytecode Compiler — fold
    // ====================================================================

    #[derive(Debug, Clone, PartialEq)]
    enum Op {
        Push(i64), Load(String), Store(String),
        Add, Mul, Neg, Eq,
        JumpIfFalse(isize), Jump(isize), Print,
    }

    #[test]
    fn ch23_compile_to_bytecode() {
        let (s, root) = sample();
        let result = s.fold(
            root,
            |stmt: StmtNodeMapped<Vec<Op>, Vec<Op>>| match stmt {
                StmtNodeMapped::Let(name, mut val) => { val.push(Op::Store(name)); val }
                StmtNodeMapped::Seq(mut l, mut r) => { l.append(&mut r); l }
                StmtNodeMapped::Print(mut v) => { v.push(Op::Print); v }
                StmtNodeMapped::If(mut cond, mut t, mut e) => {
                    cond.push(Op::JumpIfFalse(t.len() as isize + 1));
                    cond.append(&mut t);
                    cond.push(Op::Jump(e.len() as isize));
                    cond.append(&mut e);
                    cond
                }
                StmtNodeMapped::While(mut cond, mut body) => {
                    let body_len = body.len();
                    cond.push(Op::JumpIfFalse(body_len as isize + 1));
                    cond.append(&mut body);
                    cond.push(Op::Jump(-(cond.len() as isize)));
                    cond
                }
                StmtNodeMapped::Noop => vec![],
            },
            |expr: ExprNodeMapped<Vec<Op>, Vec<Op>>| match expr {
                ExprNodeMapped::Lit(n) => vec![Op::Push(n)],
                ExprNodeMapped::Bool(b) => vec![Op::Push(if b { 1 } else { 0 })],
                ExprNodeMapped::Var(name) => vec![Op::Load(name)],
                ExprNodeMapped::Add(mut l, mut r) => { l.append(&mut r); l.push(Op::Add); l }
                ExprNodeMapped::Mul(mut l, mut r) => { l.append(&mut r); l.push(Op::Mul); l }
                ExprNodeMapped::Neg(mut e) => { e.push(Op::Neg); e }
                ExprNodeMapped::Eq(mut l, mut r) => { l.append(&mut r); l.push(Op::Eq); l }
                ExprNodeMapped::Block(mut s, mut e) => { s.append(&mut e); s }
            },
        );
        let bytecode = result.unwrap_stmt();
        assert_eq!(bytecode, vec![
            Op::Push(1), Op::Push(2), Op::Push(3), Op::Mul, Op::Add, Op::Store("x".into()),
            Op::Load("x".into()), Op::Neg, Op::Store("y".into()),
            Op::Load("x".into()), Op::Push(7), Op::Eq,
            Op::JumpIfFalse(3),
            Op::Load("y".into()), Op::Print, Op::Jump(2),
            Op::Load("x".into()), Op::Print,
        ]);
    }

    // ====================================================================
    // Chapter 21: Dead Code Search — fold_short (multi-sorted early exit)
    // ====================================================================

    #[test]
    fn ch21_dead_code_search() {
        let mut s = LangStore::new();
        let f = bool_(&mut s, false);
        let x = var(&mut s, "x");
        let dead = print_(&mut s, x);
        let y = var(&mut s, "y");
        let live = print_(&mut s, y);
        let root = if_(&mut s, f, dead, live);

        let result = s.fold_short(
            LangStoreRoot::Stmt(root),
            |stmt: StmtNodeMapped<bool, bool>| match stmt {
                StmtNodeMapped::If(cond_is_false, _, _) if cond_is_false => Err(true),
                StmtNodeMapped::Seq(l, r) => Ok(l || r),
                _ => Ok(false),
            },
            |expr: ExprNodeMapped<bool, bool>| match expr {
                ExprNodeMapped::Bool(false) => Ok(true),
                _ => Ok(false),
            },
        );
        assert!(matches!(result, LangStoreFoldResult::Stmt(true)));
    }
}
