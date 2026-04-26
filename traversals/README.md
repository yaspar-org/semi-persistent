# amzn-semi-persistent-traversals

Partitioned-arena recursion schemes for Rust. Write the algebra, not the
traversal.

## What it does

Real ASTs have many mutually recursive types. A small imperative
language has statements that contain expressions and expressions that
contain statements; neither makes sense alone. Declaring these types
by hand in Rust is awkward because they reference each other, and
writing recursive traversals over them risks stack overflows on deep
trees while repeating the same boilerplate for every new operation.

The `rec_family!` macro in this crate takes a single declaration of a
mutually recursive family and generates everything you need to work
with it: one arena per type, typed IDs that prevent you from mixing
them up, and a suite of iterative, memoized traversal schemes that
cross between types automatically. You write the per-node logic (the
*algebra*) and the library runs the recursion.

The schemes fall into four groups. Folds walk a tree bottom-up and
combine child results: `fold`, `fold_all`, `fold_with_ids`,
`fold_with_history`, `fold_with_aux`, `fold_pair`, `fold_short`,
`fold_with_original`, and `prefold`. Unfolds build a tree top-down from
a seed: `unfold`, `unfold_short`, and `postunfold`. Transforms rewrite
a tree into another tree, bottom-up or top-down: `transform`,
`rewrite`, and `rewrite_down`. Zippers give you a cursor that can walk
up, across, and back down the tree, reading (`Zipper`), mutating
in place (`ZipperMut`), or producing a copy-on-write variant
(`ZipperCow`).

All traversals are iterative, so million-node trees do not overflow the
stack. All folds are memoized, so shared subtrees are folded once. The
store can be created plain with `Store::new()` or with hash-consing via
`Store::new_dedup()`. Memo strategy is configurable with
`store.with_strategy::<Sparse>().fold(...)`.

## Quick example

```rust
use semi_persistent_traversals_derive::rec_family;

rec_family! {
    family Lang => LangStore;

    enum Stmt { Let(String, Expr), Print(Expr), Noop }
    enum Expr { Lit(i64), Var(String), Add(Expr, Expr) }
}

let mut s = LangStore::new();
let one  = s.push_expr(ExprNode::Lit(1));
let two  = s.push_expr(ExprNode::Lit(2));
let sum  = s.push_expr(ExprNode::Add(one, two));
let bind = s.push_stmt(StmtNode::Let("x".into(), sum));

let result = s.fold(
    LangStoreRoot::Stmt(bind),
    |stmt: StmtNodeMapped<String, i64>| match stmt {
        StmtNodeMapped::Let(n, v) => format!("{n} = {v}"),
        StmtNodeMapped::Print(v)  => format!("print({v})"),
        StmtNodeMapped::Noop      => "noop".into(),
    },
    |expr: ExprNodeMapped<String, i64>| match expr {
        ExprNodeMapped::Lit(n)    => n,
        ExprNodeMapped::Var(_)    => 0,
        ExprNodeMapped::Add(l, r) => l + r,
    },
);

let rendered: String = result.unwrap_stmt();
```

The word *sort* means "one of the categories in a family of mutually
recursive definitions". Above, `Stmt` and `Expr` are sorts. Each sort
produces a small set of Rust types with systematic suffixes. `StmtNode`
is the enum stored in the arena. `StmtId` is a typed handle into the
arena. `StmtNodeMapped<A_stmt, A_expr>` is what an algebra receives,
with each child ID replaced by the algebra's result for that child.
Parameter order on the mapped enums follows sort declaration order
family-wide. [TUTORIAL §1](TUTORIAL.md) walks through the full macro
expansion for this example.

## Calling convention

Every scheme takes one closure per sort, in the order the sorts were
declared. For a family with two sorts, most schemes take two closures;
`fold_with_aux` and `fold_pair` take four (two algebras per sort). The
list of single-closure schemes is `fold`, `fold_short`,
`fold_with_history`, `fold_with_original`, `prefold`, `rewrite`,
`rewrite_down`, `transform`, `fold_all`, `unfold`, `unfold_short`, and
`postunfold`.

Return values are sort-tagged. A fold returns
`<Store>FoldResult<A_stmt, A_expr, ...>`, an enum with one variant per
sort. Call `.unwrap_<sort>()` when you know the root sort at the call
site, or match on the variants otherwise. Each sort can return a
different type; the parameter list on the mapped enum tells you which
is which.

## Variadic children

Use `Variadic<Sort>` in a variant to declare a variable-length list of
children of that sort. The macro stores short lists inline and longer
lists in a pool. In algebras the list appears as `Variadic<A>` and
iterates with `.iter()`.

```rust
rec_family! {
    family Calc => CalcStore;
    enum Stmt { Call(String, Variadic<Expr>) }
    enum Expr { Lit(i64) }
}
```

## Performance tuning

Two runtime choices affect performance, and they are independent of
each other.

Memo strategy controls how a fold caches intermediate results. The
default, `Dense`, allocates one memo slot per node in the store and is
fastest when you fold most of the store. `Sparse` uses a hashmap and
allocates proportional to the nodes actually visited, which is the
right choice when you fold a small subtree of a large store.
`memo::None` skips dedup checks and is only correct for pure trees.

Dedup controls whether `push_*` deduplicates structurally identical
nodes. `Store::new()` appends unconditionally; `Store::new_dedup()`
hashes and reuses. Dedup costs roughly 2 to 3× more per push but can
shrink highly redundant inputs by orders of magnitude. Use it for
e-graphs, canonicalized IRs, and any pipeline where you fold the
store more than once. Dedup interacts correctly with `mark` and
`restore`: entries pointing past a restored mark are pruned
automatically.

See [`doc/design/memo-and-dedup.md`](doc/design/memo-and-dedup.md) for
the full decision guide with benchmark numbers.

## Crate structure

The workspace has two crates. `amzn-semi-persistent-traversals` is the
core library and contains the memo strategy types, `Variadic`,
`HasVariadic`, and `Ann`. `amzn-semi-persistent-traversals-derive`
contains the `rec_family!` proc macro.

## Documentation

[TUTORIAL.md](TUTORIAL.md) is the extended guide and covers every
scheme with worked examples. [`tests/testorial.rs`](tests/testorial.rs)
contains 24 chapters that build a complete compiler pipeline (pretty
printer, constant folder, type checker, interpreter, bytecode
compiler) using only recursion schemes.
