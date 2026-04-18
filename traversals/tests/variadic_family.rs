// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]
//! Test: recursive family with variadic children of different sorts.
//!
//! Stmt  ::= Assign(StringId, IExpr) | If(BExpr, Stmt, Stmt) | Block(Variadic<Stmt>)
//! BExpr ::= True | False | And(Variadic<BExpr>) | Or(Variadic<BExpr>) | Lt(IExpr, IExpr)
//! IExpr ::= Lit(i64) | Var(StringId) | Add(Variadic<IExpr>) | Mul(Variadic<IExpr>) | Neg(IExpr)
//!
//! This file is the TARGET API. It will not compile until Arena, rec_family!,
//! Variadic, StringId, and HasVariadic are all implemented.

use semi_persistent_traversals::*;
use semi_persistent_traversals_derive::rec_family;

rec_family! {
    family Lang;
    enum Stmt  { Assign(StringId, IExpr), If(BExpr, Stmt, Stmt), Block(Variadic<Stmt>) }
    enum BExpr { True, False, And(Variadic<BExpr>), Or(Variadic<BExpr>), Lt(IExpr, IExpr) }
    enum IExpr { Lit(i64), Var(StringId), Add(Variadic<IExpr>), Mul(Variadic<IExpr>), Neg(IExpr) }
}

type Ast = Arena<Lang<usize, usize, usize>>;

fn lit(a: &mut Ast, n: i64) -> Id {
    a.push(IExpr::Lit(n).into())
}
fn var(a: &mut Ast, s: &str) -> Id {
    let id = a.intern_str(s);
    a.push(IExpr::Var(id).into())
}
fn neg(a: &mut Ast, x: Id) -> Id {
    a.push(IExpr::Neg(x.0).into())
}
fn add(a: &mut Ast, xs: &[Id]) -> Id {
    let v = a.alloc_children(xs);
    a.push(IExpr::Add(v).into())
}
fn mul(a: &mut Ast, xs: &[Id]) -> Id {
    let v = a.alloc_children(xs);
    a.push(IExpr::Mul(v).into())
}
fn lt(a: &mut Ast, l: Id, r: Id) -> Id {
    a.push(BExpr::Lt(l.0, r.0).into())
}
fn tt(a: &mut Ast) -> Id {
    a.push(BExpr::True.into())
}
fn ff(a: &mut Ast) -> Id {
    a.push(BExpr::False.into())
}
fn and(a: &mut Ast, bs: &[Id]) -> Id {
    let v = a.alloc_children(bs);
    a.push(BExpr::And(v).into())
}
fn or(a: &mut Ast, bs: &[Id]) -> Id {
    let v = a.alloc_children(bs);
    a.push(BExpr::Or(v).into())
}
fn assign(a: &mut Ast, name: &str, val: Id) -> Id {
    let n = a.intern_str(name);
    a.push(Stmt::Assign(n, val.0).into())
}
fn if_(a: &mut Ast, c: Id, t: Id, e: Id) -> Id {
    a.push(Stmt::If(c.0, t.0, e.0).into())
}
fn block(a: &mut Ast, stmts: &[Id]) -> Id {
    let v = a.alloc_children(stmts);
    a.push(Stmt::Block(v).into())
}

#[test]
fn pretty_print() {
    let mut a = Ast::new();
    let one = lit(&mut a, 1);
    let two = lit(&mut a, 2);
    let three = lit(&mut a, 3);
    let sum = add(&mut a, &[one, two, three]);
    let asgn_x = assign(&mut a, "x", sum);

    let x = var(&mut a, "x");
    let ten = lit(&mut a, 10);
    let cmp = lt(&mut a, x, ten);
    let t = tt(&mut a);
    let cond = and(&mut a, &[cmp, t]);

    let x2 = var(&mut a, "x");
    let cube = mul(&mut a, &[x2, x2, x2]);
    let asgn_y = assign(&mut a, "y", cube);
    let body = block(&mut a, &[asgn_y]);
    let else_ = block(&mut a, &[]);
    let if_stmt = if_(&mut a, cond, body, else_);
    let prog = block(&mut a, &[asgn_x, if_stmt]);

    let s = a.fold(prog, |node: Lang<String, String, String>| {
        node.dispatch(
            |stmt| match stmt {
                Stmt::Assign(name, val) => format!("{} = {val}", a.get_str(name)),
                Stmt::If(c, t, e) => format!("if ({c}) {t} else {e}"),
                Stmt::Block(stmts) => {
                    let ss: Vec<_> = stmts.into_iter().collect();
                    format!("{{ {} }}", ss.join("; "))
                }
            },
            |bexpr| match bexpr {
                BExpr::True => "true".into(),
                BExpr::False => "false".into(),
                BExpr::And(bs) => {
                    let v: Vec<_> = bs.into_iter().collect();
                    v.join(" && ")
                }
                BExpr::Or(bs) => {
                    let v: Vec<_> = bs.into_iter().collect();
                    v.join(" || ")
                }
                BExpr::Lt(l, r) => format!("{l} < {r}"),
            },
            |iexpr| match iexpr {
                IExpr::Lit(n) => n.to_string(),
                IExpr::Var(name) => a.get_str(name).to_string(),
                IExpr::Add(xs) => {
                    let v: Vec<_> = xs.into_iter().collect();
                    format!("({})", v.join(" + "))
                }
                IExpr::Mul(xs) => {
                    let v: Vec<_> = xs.into_iter().collect();
                    format!("({})", v.join(" * "))
                }
                IExpr::Neg(x) => format!("(-{x})"),
            },
        )
    });
    assert_eq!(
        s,
        "{ x = (1 + 2 + 3); if (x < 10 && true) { y = (x * x * x) } else {  } }"
    );
}

#[test]
fn multi_fold_eval() {
    let mut a = Ast::new();
    let one = lit(&mut a, 1);
    let two = lit(&mut a, 2);
    let three = lit(&mut a, 3);
    let sum = add(&mut a, &[one, two, three]);

    let result = fold_lang_multi(
        &a,
        sum,
        |_stmt: Stmt<(), bool, i64>| (),
        |bexpr: BExpr<bool, i64>| match bexpr {
            BExpr::True => true,
            BExpr::False => false,
            BExpr::And(bs) => bs.iter().all(|b| *b),
            BExpr::Or(bs) => bs.iter().any(|b| *b),
            BExpr::Lt(l, r) => l < r,
        },
        |iexpr: IExpr<i64>| match iexpr {
            IExpr::Lit(n) => n,
            IExpr::Var(_) => 0,
            IExpr::Add(xs) => xs.iter().sum(),
            IExpr::Mul(xs) => xs.iter().product(),
            IExpr::Neg(x) => -x,
        },
    );
    assert_eq!(result.unwrap_iexpr(), 6);
}

#[test]
fn bool_eval() {
    let mut a = Ast::new();
    let one = lit(&mut a, 1);
    let ten = lit(&mut a, 10);
    let cmp = lt(&mut a, one, ten);
    let t = tt(&mut a);
    let f = ff(&mut a);
    let disj = or(&mut a, &[f, t]);
    let conj = and(&mut a, &[t, cmp, disj]);

    let result = fold_lang_multi(
        &a,
        conj,
        |_: Stmt<(), bool, i64>| (),
        |bexpr: BExpr<bool, i64>| match bexpr {
            BExpr::True => true,
            BExpr::False => false,
            BExpr::And(bs) => bs.iter().all(|b| *b),
            BExpr::Or(bs) => bs.iter().any(|b| *b),
            BExpr::Lt(l, r) => l < r,
        },
        |iexpr: IExpr<i64>| match iexpr {
            IExpr::Lit(n) => n,
            IExpr::Var(_) => 0,
            IExpr::Add(xs) => xs.iter().sum(),
            IExpr::Mul(xs) => xs.iter().product(),
            IExpr::Neg(x) => -x,
        },
    );
    assert!(result.unwrap_bexpr());
}

#[test]
fn string_interning() {
    let mut a = Ast::new();
    let x1 = a.intern_str("x");
    let x2 = a.intern_str("x");
    let y = a.intern_str("y");
    assert_eq!(x1, x2);
    assert_ne!(x1, y);
    assert_eq!(a.get_str(x1), "x");
    assert_eq!(a.get_str(y), "y");
}

#[test]
fn variadic_dedup() {
    let mut a: HcArena<Lang<usize, usize, usize>> = Arena::new_dedup();
    let t = a.push(Lang::BExprTrue);
    let f = a.push(Lang::BExprFalse);
    let args1 = a.alloc_children(&[t, f]);
    let c1 = a.push(Lang::BExprAnd(args1));
    let args2 = a.alloc_children(&[t, f]);
    let c2 = a.push(Lang::BExprAnd(args2));
    assert_eq!(c1, c2);
}

#[test]
fn transform_negate_literals() {
    let mut a = Ast::new();
    let one = lit(&mut a, 1);
    let two = lit(&mut a, 2);
    let sum = add(&mut a, &[one, two]);

    let (a2, r2) = a.rewrite(sum, |node, arena| {
        let node = match node {
            Lang::IExprLit(n) => Lang::IExprLit(-n),
            other => other,
        };
        arena.push(node)
    });

    let val = a2.fold(r2, |node: Lang<i64, i64, i64>| {
        node.dispatch(
            |_| 0i64,
            |_| 0i64,
            |i| match i {
                IExpr::Lit(n) => n,
                IExpr::Add(xs) => xs.iter().sum(),
                _ => 0,
            },
        )
    });
    assert_eq!(val, -3);
}
