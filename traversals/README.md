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

## Crate structure

- `amzn-semi-persistent-traversals` — core library: `Arena`, `Functor` trait, all schemes
- `amzn-semi-persistent-traversals-derive` — proc macros: `#[derive(RecFunctor)]` and `rec_family!`

## Documentation

See [TUTORIAL.md](TUTORIAL.md) for the full guide covering every scheme,
the internal design, mutually recursive type families, and deduplication.

See `tests/testorial.rs` for a 30-chapter worked example building a complete
compiler pipeline (pretty printer, constant folder, type checker,
interpreter, bytecode compiler) using only recursion schemes.
