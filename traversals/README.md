# amzn-semi-persistent-traversals

Partitioned-arena recursion schemes for Rust. Write the algebra, not the traversal.

## What it does

Declare a family of mutually recursive types with `rec_family!`. The macro
generates per-sort arenas with **typed IDs** (`StmtId`, `ExprId`, ...) and
a full suite of stack-safe, memoized traversals — so you never write a
recursive function:

- **Folds** (bottom-up): `fold`, `fold_all`, `fold_with_ids`,
  `fold_with_history`, `fold_with_aux`, `fold_pair`, `fold_short`,
  `fold_with_original`, `prefold`
- **Unfolds** (top-down build): `unfold`, `unfold_short`, `postunfold`
- **Transforms** (tree → tree): `transform`, `rewrite`, `rewrite_down`
- **Zippers**: `Zipper`, `ZipperMut`, `ZipperCow`

All traversals are iterative (no stack overflow on million-node trees),
automatically memoized (shared subtrees computed once), and run on a store
created with `Store::new()` (plain) or `Store::new_dedup()` (hash-consing).
Memoization is parameterized — use `store.with_strategy::<Sparse>().fold(...)`
to switch between dense, sparse, and no-memo strategies.

## Quick example

```rust
use semi_persistent_traversals_derive::rec_family;

rec_family! {
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

// Fold: one algebra per sort, in declaration order.
// Each algebra receives a mapped enum where child ids are replaced by results.
// Each sort can return a different type.
let result = s.fold(
    LangStoreRoot::Stmt(bind),
    // Stmt algebra: sees StmtNodeMapped<String, i64>
    |stmt: StmtNodeMapped<String, i64>| match stmt {
        StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
        StmtNodeMapped::Print(v)  => format!("print({v})"),
        StmtNodeMapped::Noop      => "noop".into(),
    },
    // Expr algebra: sees ExprNodeMapped<String, i64>
    |expr: ExprNodeMapped<String, i64>| match expr {
        ExprNodeMapped::Lit(n)    => n,
        ExprNodeMapped::Var(_)    => 0,
        ExprNodeMapped::Add(l, r) => l + r,
    },
);

// Result is sort-tagged. Unwrap when you know the root sort.
let rendered: String = result.unwrap_stmt();
```

## Calling convention

Every scheme takes **one closure per sort, in declaration order**. With N
sorts the single-closure schemes (`fold`, `fold_short`, `fold_with_history`,
`fold_with_original`, `prefold`, `rewrite`, `rewrite_down`, `transform`,
`fold_all`, `unfold`, `unfold_short`, `postunfold`) take N closures.
`fold_with_aux` and `fold_pair` take 2N closures (two algebras per sort).

Each mapped enum is generic only over the sort result types it references,
so empty sort parameters don't clutter signatures. Return values are sort-
tagged via `<Store>FoldResult<A_stmt, A_expr, ...>`; unwrap with
`.unwrap_<sort>()` or match on it.

## Variadic children

`Variadic<Sort>` declares a variable-arity child list. Stored inline for
small lists, pooled for larger ones. In algebras it appears as
`Variadic<A>` and iterates with `.iter()`.

```rust
rec_family! {
    family Calc => CalcStore;
    enum Stmt { Call(String, Variadic<Expr>) }
    enum Expr { Lit(i64) }
}
```

## Choosing memo strategy and dedup

Two orthogonal choices affect performance:

- **Memo strategy**: `Dense` (default, `O(store)` memo) vs `Sparse`
  (hashmap, `O(reachable)` memo) vs `memo::None` (no dedup, for pure
  trees). Use `store.with_strategy::<Sparse>().fold(…)` when folding a
  small subtree inside a large store.
- **Dedup**: `Store::new()` (plain push) vs `Store::new_dedup()`
  (hash-consing). Dedup is 2–3× slower at construction but can shrink
  a 500K-node tree to 19 unique nodes when there's structural sharing.
  Use for e-graphs, compiler IRs, canonicalization.

Full decision guide with benchmarks:
[`doc/design/memo-and-dedup.md`](doc/design/memo-and-dedup.md).

## Crate structure

- `amzn-semi-persistent-traversals` — core library: memo strategies,
  `Variadic`, `HasVariadic`, `Ann`
- `amzn-semi-persistent-traversals-derive` — the `rec_family!` proc macro

## Documentation

- [TUTORIAL.md](TUTORIAL.md) — extended guide to every scheme.
- [`tests/testorial.rs`](tests/testorial.rs) — 24
  worked chapters building a complete compiler pipeline (pretty printer,
  constant folder, type checker, interpreter, bytecode compiler) using
  only recursion schemes.
