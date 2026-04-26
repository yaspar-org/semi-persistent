# amzn-semi-persistent-traversals

Arena-based recursion schemes for Rust. Write the algebra, not the traversal.

## What it does

Semi-Persistent Traversals lets you define recursive data types as **functors** — enums
parameterized over their child type — and store them in flat arenas.
The library then provides a full suite of stack-safe, memoized
traversal schemes so you never write a recursive function:

- **Folds** (bottom-up): `fold`, `fold_all`, `fold_with_ids`,
  `fold_with_history`, `fold_with_aux`, `fold_pair`, `fold_short`,
  `fold_with_original`, `fold_mut`, `prefold`
- **Zero-clone folds**: `fold_ref`, `fold_all_ref` — algebra receives `&A`
  children instead of cloned `A`. Use when result type is expensive to clone.
- **Unfolds** (top-down build): `unfold`, `unfold_short`, `postunfold`
- **Refolds** (unfold then fold): `refold`, `refold_with_history`, `refold_full`
- **Transforms** (tree → tree): `transform`, `rewrite`, `rewrite_down`

All traversals are iterative (no stack overflow on million-node trees),
automatically memoized (shared subtrees computed once), and work on both
`Arena::new()` (no dedup) and `Arena::new_dedup()` (hash-consing on push).

## Quick example — single sort

```rust
use amzn_semi-persistent-traversals::{Arena, Functor};
use amzn_semi-persistent-traversals_derive::RecFunctor;

#[derive(Clone, PartialEq, Eq, Hash, RecFunctor)]
enum E<R> { Lit(i64), Add(R, R), Neg(R) }

let mut a = Arena::new();
let one = a.push(E::Lit(1));
let two = a.push(E::Lit(2));
let sum = a.push(E::Add(one.0, two.0));

// Evaluate — you write only the algebra
let val = a.fold(sum, |node: E<i64>| match node {
    E::Lit(n) => n,
    E::Add(a, b) => a + b,
    E::Neg(a) => -a,
});
assert_eq!(val, 3);
```

## Mutually recursive types — `rec_family!`

Real ASTs have multiple sorts defined in terms of each other. Here's a
language with expressions and types, plus a pretty printer:

```rust
use amzn_semi-persistent-traversals::Arena;
use amzn_semi-persistent-traversals_derive::rec_family;

rec_family! {
    family Lang;
    enum Expr {
        IntLit(i64),
        BoolLit(bool),
        Add(Expr, Expr),
        Eq(Expr, Expr),
        If(Expr, Expr, Expr),
        Call(String, Variadic<Expr>),  // variable-arity: f(a, b, c, ...)
        Ann(Expr, Ty),
    }
    enum Ty {
        TInt,
        TBool,
        TFn(Variadic<Ty>, Ty),        // (T1, T2, ...) -> T
    }
}
```

`Variadic<Sort>` declares a variable-length child list. In the arena it's
stored inline (no `Vec` allocation for ≤4 elements). In the algebra, it
appears as `Variadic<A>` which you iterate with `.iter()`:

```rust
// Build: f(1, 2, 3)
let args = a.alloc_children(&[one, two, three]);  // returns Variadic<usize>
let call = a.push(Lang::ExprCall("f".into(), args));

// Pretty-print — Variadic<&String> in the ref algebra
let result = fold_ref_lang_multi(&a, call,
    |e: Expr<&String, &String>| match e {
        Expr::Call(name, args) => {
            let arg_strs: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
            format!("{}({})", name, arg_strs.join(", "))
        }
        // ...other arms...
    },
    |t: Ty<&String>| match t {
        Ty::TFn(params, ret) => {
            let ps: Vec<&str> = params.iter().map(|s| s.as_str()).collect();
            format!("({}) -> {}", ps.join(", "), ret)
        }
        // ...
    },
);
```

The macro generates:
- **Coproduct enum** `Lang<S0, S1>` stored in the arena
- **Per-sort enums** `Expr<S0, S1>` and `Ty<S1>` for pattern matching
- **`fold_lang_multi`** / **`fold_ref_lang_multi`** — heterogeneous folds
  where each sort can produce a different result type
- **`fold_all_lang_multi`** / **`fold_all_ref_lang_multi`** — O(n) linear
  scan over the entire arena
- `dispatch`, `multi_map`, `multi_map_ref`, `From`/`TryFrom` conversions

Scales to any number of sorts.

## Partitioned layout — `partition!`

`partition!` generates the same family as `rec_family!` but stores each sort
in its own arena with typed IDs (`StmtId`, `ExprId`). Folds are 9–15% faster,
and multi-sorted folds take **one algebra per sort** rather than one algebra
plus a `dispatch`.

```rust
use amzn_semi_persistent_traversals_derive::partition;

partition! {
    family Lang => LangStore;

    enum Stmt { Let(String, Expr), Print(Expr), Noop }
    enum Expr { Lit(i64), Var(String), Add(Expr, Expr) }
}

// Build a program: let x = 1 + 2; print(x)
let mut s = LangStore::new();
let one  = s.push_expr(ExprNode::Lit(1));
let two  = s.push_expr(ExprNode::Lit(2));
let sum  = s.push_expr(ExprNode::Add(one, two));
let bind = s.push_stmt(StmtNode::Let("x".into(), sum));
let x    = s.push_expr(ExprNode::Var("x".into()));
let pr   = s.push_stmt(StmtNode::Print(x));
// ... combine into a root stmt ...

// Fold: one algebra per sort, in declaration order.
// Each algebra receives a mapped enum where child ids are replaced by results.
// Each sort can return a different type.
let result = s.fold(
    LangStoreRoot::Stmt(bind),
    // Stmt algebra: sees StmtNodeMapped<StmtResult, ExprResult>
    |stmt: StmtNodeMapped<String, i64>| match stmt {
        StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
        StmtNodeMapped::Print(v)  => format!("print({v})"),
        StmtNodeMapped::Noop      => "noop".into(),
    },
    // Expr algebra: sees ExprNodeMapped<StmtResult, ExprResult>
    |expr: ExprNodeMapped<String, i64>| match expr {
        ExprNodeMapped::Lit(n)      => n,
        ExprNodeMapped::Var(_)      => 0,
        ExprNodeMapped::Add(l, r)   => l + r,
    },
);

// Result is sort-tagged. Unwrap when you know the root sort.
let s: String = result.unwrap_stmt();
```

**Calling convention for every scheme** (`fold`, `fold_short`,
`fold_with_history`, `fold_with_aux`, `fold_with_original`, `fold_pair`,
`prefold`, `rewrite`, `rewrite_down`, `transform`): **one closure per sort
in declaration order**. With N sorts, these schemes take N closures.
`fold_pair` takes 2N closures (two algebras per sort). Each mapped enum
is generic over only the sort result types it references.

## Crate structure

- `amzn-semi-persistent-traversals` — core library: `Arena`, `Functor` trait, all schemes
- `amzn-semi-persistent-traversals-derive` — proc macros: `#[derive(RecFunctor)]` and `rec_family!`

## Choosing layout, memo strategy, and dedup

Three orthogonal choices affect performance and ergonomics:

- **Layout**: `Arena<Lang<usize, usize>>` (coproduct, via `rec_family!`) vs
  `LangStore` (partitioned per-sort arenas, via `partition!`). Partitioned
  fold is 9–15% faster with typed IDs and cleaner algebras — **prefer
  partitioned for multi-sort ASTs**.
- **Memo strategy**: `Dense` (default, `O(store)` memo) vs `Sparse`
  (hashmap, `O(reachable)` memo) vs `memo::None` (no dedup, for pure trees).
  Use `store.with_strategy::<Sparse>().fold(…)` when folding a small
  subtree inside a large store.
- **Dedup**: `new()` (plain push) vs `new_dedup()` (hash-consing). Dedup
  is 2–3× slower at construction but can shrink a 500K-node tree to 19
  unique nodes when there's structural sharing. Use for e-graphs,
  compiler IRs, canonicalization.

Full decision guide with benchmarks:
[`doc/design/layout-and-strategy.md`](doc/design/layout-and-strategy.md).

## Documentation

See [TUTORIAL.md](TUTORIAL.md) for the full guide covering every scheme,
the internal design, mutually recursive type families, and deduplication.

See `tests/testorial.rs` for a 30-chapter worked example building a complete
compiler pipeline (pretty printer, constant folder, type checker,
interpreter, bytecode compiler) using only recursion schemes.
