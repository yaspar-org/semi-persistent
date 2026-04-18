# Recursion Schemes in Rust

## The Problem

Every tree traversal has the same structure: match on the variant, recurse into
children, combine results. The traversal logic is identical, only the combining
step differs. This causes:

1. **Stack overflow** on deep trees (100k+ nodes).
2. **Boilerplate explosion** every new operation repeats the recursion skeleton.
3. **The expression problem** new variants force updates to every operation.

Recursion schemes factor out the traversal into reusable, stack-safe combinators.
You write only the algebra.

## The Design

This library uses an **arena-only, functor-based** approach:

- You declare a **functor**: `enum E<R> { Lit(i64), Add(R, R), ... }`
- The arena stores `E<usize>`: children are indices, arity enforced by the type
- Algebras receive `E<A>`: the node with children replaced by results
- All traversals are stack-safe (iterative, explicit heap stack, contiguous memory)

No `Box`. No recursive types. No recursive `Drop`.

**The traversal code is written exactly once.** `fold` uses an Enter/Eval
stack that visits only the reachable subtree. `fold_all` does a single O(n)
linear scan (children always have lower indices than parents). Every other
scheme is a thin wrapper that applies the user's algebra in the right way.

Two constructors control deduplication:
- `Arena::new()` — no dedup, `push` always appends (fastest for building)
- `Arena::new_dedup()` — hash-consing, `push` returns existing Id for identical nodes

---

## Getting Started

### Step 1: Declare your functor

```rust
#[derive(Clone, PartialEq, Eq, Hash)]
enum E<R> {
    Lit(i64),
    Add(R, R),    // exactly 2 children — enforced by the type
    Mul(R, R),
    Neg(R),       // exactly 1 child
}
```

### Step 2: Implement Functor

One trait, one method: map a function over child positions:

```rust
impl<R> Functor<R> for E<R> {
    type Mapped<S> = E<S>;
    fn map<S>(self, mut f: impl FnMut(R) -> S) -> E<S> {
        match self {
            E::Lit(n) => E::Lit(n),
            E::Add(a, b) => E::Add(f(a), f(b)),
            E::Mul(a, b) => E::Mul(f(a), f(b)),
            E::Neg(a) => E::Neg(f(a)),
        }
    }
}
```

Or use `#[derive(RecFunctor)]` to generate this automatically.

No separate `Children` trait: child indices are derived internally from
`Functor::map` using an `FnMut` closure. You implement one thing and get everything.

### Step 3: Build trees in an arena

```rust
type Expr = Arena<E<usize>>;

let mut e = Expr::new();
let one   = e.push(E::Lit(1));             // Id(0)
let two   = e.push(E::Lit(2));             // Id(1)
let sum   = e.push(E::Add(one.0, two.0));  // Id(2)
let three = e.push(E::Lit(3));             // Id(3)
let neg3  = e.push(E::Neg(three.0));       // Id(4)
let root  = e.push(E::Mul(sum.0, neg3.0)); // Id(5)
// Represents: (1 + 2) * (-(3))
```

`push` always appends. Use `Arena::new_dedup()` if you want identical nodes
to share the same `Id`.

---

## Complete Scheme Reference

### Folds (consume a tree)

| Scheme | Algebra signature | Description |
|---|---|---|
| `fold` | `F<A> → A` | Bottom-up fold (subtree only, Enter/Eval stack) |
| `fold_all` | `F<A> → A` | Fold every node in one O(n) linear scan |
| `fold_with_ids` | `F<(Id, A)> → A` | Fold with access to original subtree ids |
| `fold_with_history` | `F<&Ann<A>> → A` | Fold with full history (look back N levels) |
| `fold_with_aux` | aux: `F<B>→B`, main: `F<(A,B)>→A` | Paired folds, main sees auxiliary results |
| `fold_pair` | `F<(A,B)>→A`, `F<(A,B)>→B` | Two mutually recursive folds |
| `prefold` | pre: `N→N`, alg: `F<A>→A` | Normalize each node, then fold |
| `fold_short` | `F<A> → Result<A,A>` | Fold with early exit |
| `fold_with_original` | `(&N, F<A>) → A` | Fold that also sees the original node |
| `fold_mut` | `(F<A>, &mut S) → A` | Fold with mutable state threaded through |

### Zero-clone folds (ref-algebra variants)

The standard folds clone each child result into the mapped node. When `A` is
expensive to clone (String, Vec, Rc), use the ref variants instead — the
algebra receives **borrowed** children and the library never clones results.

| Scheme | Algebra signature | Description |
|---|---|---|
| `fold_ref` | `F<&A> → A` | Like `fold`, children are `&A` |
| `fold_all_ref` | `F<&A> → A` | Like `fold_all`, children are `&A` |

**Key difference:** data fields (non-child fields like `i64`, `StringId`) are
still owned in the mapped node. Only child fields become references. This
means the algebra pattern-matches on a mix of owned data and borrowed children:

```rust
// Standard fold — everything is owned
a.fold(root, |node: E<String>| match node {
    E::Lit(n) => n.to_string(),        // n: i64 (data, owned)
    E::Add(l, r) => format!("{l}+{r}"), // l, r: String (children, owned)
});

// Ref fold — children are borrowed, data is still owned
a.fold_ref(root, |node: E<&String>| match node {
    E::Lit(n) => n.to_string(),        // n: i64 (data, still owned)
    E::Add(l, r) => format!("{l}+{r}"), // l, r: &String (children, borrowed)
});
```

**When to use which:**
- `A` is `Copy` (i64, bool, usize) → use `fold` / `fold_all` (ref overhead not worth it)
- `A` is expensive to clone (String, Vec) → use `fold_ref` / `fold_all_ref`

### Unfolds (build a tree from a seed)

| Scheme | Coalgebra signature | Description |
|---|---|---|
| `unfold` | `S → (N, Vec<S>)` | Unfold a seed into a tree |
| `unfold_short` | `S → (N, Vec<Seed<S>>)` | Unfold with early exit (`Done(Id)` reuses existing node) |
| `postunfold` | post: `N→N`, coalg: `S→(N,Vec<S>)` | Unfold, normalizing each layer after |

### Refolds (unfold then fold)

| Scheme | Description |
|---|---|
| `refold` | Unfold then fold, no arena materialized |
| `refold_with_history` | `unfold` then `fold_with_history`, unfold with history during fold |
| `refold_full` | `unfold` then `fold_with_history`, generalized unfold-with-history |

### Transforms (tree → tree)

| Scheme | Description |
|---|---|
| `transform` | Bottom-up rewrite (post-order). Returns new arena |
| `rewrite` | Bottom-up rewrite with `&mut Arena` — can create new nodes |
| `rewrite_down` | Top-down rewrite (pre-order). Returns new arena |

### Arena constructors

| Constructor | Dedup | Use case |
|---|---|---|
| `Arena::new()` | No | Fast building, no overhead |
| `Arena::new_dedup()` | Yes (hash-consing) | Structural sharing, identical subtrees stored once |

Both return `Arena<N>` (with a const generic controlling dedup internally).
All traversal schemes work identically on both — the only difference is
whether `push` deduplicates.

---

## How It Works: The Traversal Is Written Once

Every scheme follows the same pattern: visit nodes bottom-up, apply the
algebra. Two strategies depending on the use case:

**`fold` (subtree):** Uses an explicit Enter/Eval stack. Only visits nodes
reachable from the root. O(subtree) time and space. Uses `children_into`
(destination-passing SmallVec) to discover children without cloning the node,
and `map_ref` to build the mapped node without cloning it:

```rust
pub fn fold<A: Clone>(&self, root: Id, alg: impl Fn(N::Mapped<A>) -> A) -> A {
    enum Task { Enter(usize), Eval(usize) }
    let mut res: Vec<Option<A>> = vec![None; self.nodes.len()];
    let mut stack = vec![Task::Enter(root.0)];
    let mut ch_buf = SmallVec::<[usize; 8]>::new();
    while let Some(task) = stack.pop() {
        match task {
            Task::Enter(i) => {
                if res[i].is_some() { continue; }       // memoized
                stack.push(Task::Eval(i));
                self.nodes[i].children_into(&mut ch_buf); // zero-alloc child discovery
                for &c in ch_buf.iter().rev() {
                    if res[c].is_none() { stack.push(Task::Enter(c)); }
                }
            }
            Task::Eval(i) => {
                if res[i].is_some() { continue; }
                let node = self.nodes[i].map_ref(|c| res[*c].as_ref().unwrap().clone());
                res[i] = Some(alg(node));                // user's algebra
            }
        }
    }
    res[root.0].take().unwrap()
}
```

**`fold_all` (whole arena):** Linear scan 0..len. Since children always have
lower indices than parents (push order), no topological sort is needed.
O(n) time, single pass, no per-call allocation:

```rust
pub fn fold_all<A: Clone>(&self, alg: impl Fn(N::Mapped<A>) -> A) -> FoldCache<A> {
    let mut res: Vec<A> = Vec::with_capacity(self.nodes.len());
    for i in 0..self.nodes.len() {
        let node = self.nodes[i].map_ref(|c| res[*c].clone());
        res.push(alg(node));
    }
    FoldCache { results: res }
}
```

**`fold_ref` / `fold_all_ref`:** Same strategies but the algebra receives
`N<&A>` — borrowed children, zero clones. See the "Zero-clone folds" section.

And here's `unfold`: the dual. It uses an explicit heap-allocated stack
to stay iterative — no recursion, no stack overflow at any depth. Two stacks:
`work` holds pending tasks, `results` collects completed `Id`s:

```rust
enum AnaTask<N, S> {
    Expand(S),        // expand this seed via coalgebra
    Build(N, usize),  // remap this node's N children from results, push to arena
}

pub fn unfold<N, S>(arena: &mut Arena<N>, seed: S, coalg: impl Fn(S) -> (N, Vec<S>)) -> Id {
    let mut work: Vec<AnaTask<N, S>> = vec![AnaTask::Expand(seed)];
    let mut results: Vec<Id> = Vec::new();

    while let Some(task) = work.pop() {
        match task {
            AnaTask::Expand(s) => {
                let (node, child_seeds) = coalg(s);
                let n = child_seeds.len();
                work.push(AnaTask::Build(node, n));  // runs after children
                for cs in child_seeds.into_iter().rev() {
                    work.push(AnaTask::Expand(cs));   // children first (reversed)
                }
            }
            AnaTask::Build(node, n) => {
                let start = results.len() - n;
                let child_ids: Vec<usize> = results.drain(start..).map(|id| id.0).collect();
                let mut idx = 0;
                let remapped = node.map(|_| { let id = child_ids[idx]; idx += 1; id });
                results.push(arena.push(remapped));
            }
        }
    }
    results.pop().unwrap()
}
```

This is a mechanical CPS transform of the recursive version: the call stack
becomes `work`, return values become `results`. The test suite unfolds a chain
of 1,000,000 nodes without stack overflow.

Every other scheme follows the same patterns. Subtree folds use an Enter/Eval
stack. `fold_all` variants do a single linear scan.
Unfolds use the `work`+`results` explicit stack.
`fold_with_ids` is `fold` where children get `(Id, A)` instead of just `A`.
`fold_with_history` wraps results in `Ann`. `transform` is `fold` that builds
into a new arena.

---

## Advanced: Annotating Trees with Extra Information

A powerful pattern: change what `R` means. In the arena, `R = usize` (child
indices). But the functor is generic over `R`, so you can instantiate it with
richer types.

### Example: Adding type annotations to an expression tree

Suppose you have an untyped expression:

```rust
#[derive(Clone, PartialEq, Eq, Hash)]
enum Expr<R> {
    IntLit(i64),
    BoolLit(bool),
    Add(R, R),
    Eq(R, R),
    If(R, R, R),
}
```

You want to produce a **typed** tree where every node carries its type. Define:

```rust
#[derive(Clone, Debug)]
enum Ty { Int, Bool }
```

Now use `fold_with_ids` to fold the tree into a *new* arena where each node is
paired with its type. The result type `A` is `(Id, Ty)` — an id in the new
arena plus the inferred type:

```rust
fn type_check(src: &Arena<Expr<usize>>, root: Id) -> (Arena<Typed<usize>>, Id) {
    let mut out = Arena::new();

    let (new_root, _ty) = src.fold_with_ids(root, |node: Expr<(Id, (Id, Ty))>| {
        match node {
            Expr::IntLit(n) => {
                let id = out.push(Typed::IntLit(n));
                (id, Ty::Int)
            }
            Expr::Add((_, (a_id, a_ty)), (_, (b_id, b_ty))) => {
                assert!(matches!(a_ty, Ty::Int));
                assert!(matches!(b_ty, Ty::Int));
                let id = out.push(Typed::Add(a_id.0, b_id.0));
                (id, Ty::Int)
            }
            // ... other cases
        }
    });

    (out, new_root)
}
```

This generalizes to any annotation: source spans, cost estimates, free variable
sets, normal form flags. The functor doesn't change — only the algebra does.

---

## Deduplication

`Arena::new_dedup()` creates an arena that hash-conses on push:

```rust
let mut e = Arena::new_dedup();
let a = e.push(E::Lit(1));
let b = e.push(E::Lit(2));
let s1 = e.push(E::Add(a.0, b.0));

let s2 = e.push(E::Add(a.0, b.0));  // returns same Id as s1
assert_eq!(s1, s2);
assert_eq!(e.len(), 3);  // only 3 unique nodes
```

With `Arena::new()` (no dedup), the same code would produce 5 nodes.

Use `unfold_hc` to unfold directly into a dedup arena — shared subtrees are
deduplicated during construction:

```rust
let mut hc = Arena::new_dedup();
let root = unfold_hc(&mut hc, 3u32, |n| {
    if n == 0 { (E::Lit(1), vec![]) }
    else { (E::Add(0, 0), vec![n-1, n-1]) }
});
// Full binary tree of depth 3 has 15 nodes expanded,
// but dedup arena stores only 4 (one per level).
```

---

## Single-Functor Summary

| You write | You get |
|---|---|
| `enum E<R> { ... }` | Type-safe node with enforced arity |
| `impl Functor` (~8 lines) | All 17 schemes, stack-safe, memoized |
| `arena.push(node)` | Hash-consed, cache-friendly storage |

The traversal is written once. The algebra is yours.

---

## Mutually Recursive Functor Families

Everything above uses a single functor: one `enum E<R>`, one arena, one
algebra. Real languages aren't like that. A language has statements,
expressions, types, patterns — each defined in terms of the others.

### The problem

```
Stmt ::= Assign(String, Expr) | Seq(Stmt, Stmt) | Print(Expr)
Expr ::= Var(String) | Lit(i64) | Add(Expr, Expr) | Block(Stmt, Expr)
```

`Stmt` refers to `Expr`. `Expr` refers to `Stmt`. They are mutually inductive.

A single `Arena<N>` is monomorphic — it stores one node type `N`. You can't
put both `Stmt<usize>` and `Expr<usize>` in the same arena because they're
different types.

### The solution: coproduct functor

Given N mutually recursive functors F₁, …, Fₙ, form their coproduct
F = F₁ + F₂ + … + Fₙ. The initial algebra of F is isomorphic to the mutual
fixpoint of (F₁, …, Fₙ).

In Rust: merge all variants into one enum. The arena stores that enum.
Children are `usize` indices regardless of which sort they point to.
The sort distinction is recovered at the algebra level.

### Declaring a family with `rec_family!`

```rust
use amzn_semi-persistent-traversals_derive::rec_family;

rec_family! {
    family Lang;

    enum Stmt {
        Assign(String, Expr),    // "Expr" = child of sort Expr
        Seq(Stmt, Stmt),         // "Stmt" = child of sort Stmt
        Print(Expr),
    }

    enum Expr {
        Var(String),             // "String" = data, not a child
        Lit(i64),
        Add(Expr, Expr),
        Block(Stmt, Expr),       // cross-sort: Stmt child + Expr child
    }
}
```

You write the grammar as you'd write it on a whiteboard. Field types matching
a sibling sort name are recognized as child positions. Everything else is data.

### Variable-arity children — `Variadic<Sort>`

Some nodes have a variable number of children: function calls, match arms,
block statements. Use `Variadic<Sort>` to declare these:

```rust
rec_family! {
    family Lang;
    enum Stmt {
        Block(Variadic<Stmt>),           // 0..N statements
        Print(Expr),
    }
    enum Expr {
        Lit(i64),
        Call(String, Variadic<Expr>),     // f(a, b, c, ...)
    }
}
```

**Building variadic nodes:** Use `alloc_children` to get a `Variadic<usize>`,
then pass it to `push`:

```rust
let mut a = Arena::new();
let one = a.push(Lang::ExprLit(1));
let two = a.push(Lang::ExprLit(2));
let args = a.alloc_children(&[one, two]);           // Variadic<usize>
let call = a.push(Lang::ExprCall("f".into(), args)); // f(1, 2)
```

**In the algebra:** Variadic fields appear as `Variadic<A>` (or `Variadic<&A>`
in ref algebras). Iterate with `.iter()`:

```rust
// Owned algebra
|e: Expr<String, String>| match e {
    Expr::Call(name, args) => {
        let strs: Vec<&str> = args.iter().map(String::as_str).collect();
        format!("{}({})", name, strs.join(", "))
    }
    // ...
}

// Ref algebra — Variadic<&String>, iterate yields &&String
|e: Expr<&String, &String>| match e {
    Expr::Call(name, args) => {
        let strs: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
        format!("{}({})", name, strs.join(", "))
    }
    // ...
}
```

**Storage:** `Variadic` uses `SmallVec<[R; 4]>` internally — up to 4 children
are stored inline with zero heap allocation. This covers the vast majority of
real AST nodes (function parameters, match arms, etc.).

### What the macro generates

**1. The coproduct** — `Lang<__S0, __S1>` with one type param per sort:

```rust
enum Lang<__S0, __S1> {
    StmtAssign(String, __S1),   // Expr child → __S1
    StmtSeq(__S0, __S0),        // Stmt children → __S0
    StmtPrint(__S1),            // Expr child → __S1
    ExprVar(String),
    ExprLit(i64),
    ExprAdd(__S1, __S1),
    ExprBlock(__S0, __S1),
}
```

Each sort's children get their own type parameter. `Stmt` children are `__S0`,
`Expr` children are `__S1`. The type system tracks which sort each child
belongs to.

**2. Per-sort enums** — only the type params they use:

```rust
enum Stmt<__S0, __S1> { Assign(String, __S1), Seq(__S0, __S0), Print(__S1) }
enum Expr<__S0, __S1> { Var(String), Lit(i64), Add(__S1, __S1), Block(__S0, __S1) }
```

If a sort doesn't reference all siblings, it only gets the params it uses:

```rust
enum MonoTy<__S0> { Int, Bool, Fn(__S0, __S0) }  // only self-recursive
enum PolyTy<__S0, __S1> { Forall(String, __S1), Mono(__S0) }
```

**3. `Functor<R>`** for `Lang<R, R>` — when all params are the same, this is
the standard single-`R` functor. This is what `Arena` and all existing schemes
use.

**4. `multi_map`** — map with a separate function per sort:

```rust
impl Lang<__S0, __S1> {
    fn multi_map<__D0, __D1>(
        self,
        f0: impl FnMut(__S0) -> __D0,  // maps Stmt children
        f1: impl FnMut(__S1) -> __D1,  // maps Expr children
    ) -> Lang<__D0, __D1>;
}
```

**5. `dispatch`** — route to per-sort closures (uniform return type):

```rust
impl Lang<__S0, __S1> {
    fn dispatch<T>(
        self,
        f_stmt: impl FnMut(Stmt<..>) -> T,
        f_expr: impl FnMut(Expr<..>) -> T,
    ) -> T;
}
```

**6. Multi-sorted folds** — N algebras, N result types:

```rust
fn fold_multi<A0, A1>(arena, root,
    alg_stmt: Fn(Stmt<A0, A1>) -> A0,
    alg_expr: Fn(Expr<A0, A1>) -> A1,
) -> LangRes<A0, A1>

fn fold_with_ids_multi<A0, A1>(arena, root,
    alg_stmt: Fn(Stmt<(Id,A0), (Id,A1)>) -> A0,
    alg_expr: Fn(Expr<(Id,A0), (Id,A1)>) -> A1,
) -> LangRes<A0, A1>
```

**7. `LangRes<A0, A1>`** — result enum with `unwrap_stmt()` / `unwrap_expr()`.

**8. `From<Stmt<..>> for Lang<..>`** — injection (sort → coproduct).

**9. `TryFrom<Lang<..>> for Stmt<..>`** — projection (coproduct → sort).
Returns `Err(original)` on sort mismatch.

### Injection and projection

The coproduct is the arena's storage type, but you never have to name its
variants directly. `From` and `TryFrom` make the conversion transparent:

```rust
// Building: use sort types, .into() injects into the coproduct
let mut a = Ast::new();
let one  = a.push(Expr::Lit(1).into());
let sum  = a.push(Expr::Add(one.0, two.0).into());
let asgn = a.push(Stmt::Assign("x".into(), sum.0).into());

// Transforms: TryFrom projects back into sort types
let (a2, r2) = a.transform(root, |node| {
    if let Ok(Expr::Lit(n)) = node.clone().try_into() {
        Expr::Lit(n * 10).into()
    } else {
        node
    }
});
```

### Building trees

The arena stores `Lang<usize, usize>` — all params are `usize`:

```rust
type Ast = Arena<Lang<usize, usize>>;

let mut a = Ast::new();
let one  = a.push(Lang::ExprLit(1));
let two  = a.push(Lang::ExprLit(2));
let sum  = a.push(Lang::ExprAdd(one.0, two.0));
let asgn = a.push(Lang::StmtAssign("x".into(), sum.0));
let xref = a.push(Lang::ExprVar("x".into()));
let pr   = a.push(Lang::StmtPrint(xref.0));
let root = a.push(Lang::StmtSeq(asgn.0, pr.0));
```

### Folding — uniform result type (use `dispatch`)

When every sort folds to the same type (e.g. `String` for pretty-printing),
use the standard `fold` with `dispatch`:

```rust
let s = a.fold(root, |node: Lang<String, String>| {
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
```

This works because `Lang<String, String>` collapses both params to the same
type — it's just a regular single-`R` functor fold.

### Folding — different result type per sort (use `fold_multi`)

This is where the multi-parameter design pays off. A type checker where
statements produce `()` and expressions produce `i64`:

```rust
let result = fold_multi(
    &a, root,
    |stmt: Stmt<(), i64>| match stmt {
        Stmt::Assign(_, _val) => (),
        Stmt::Seq((), ()) => (),
        Stmt::Print(_val) => (),
    },
    |expr: Expr<(), i64>| match expr {
        Expr::Var(_) => 0,
        Expr::Lit(n) => n,
        Expr::Add(l, r) => l + r,
        Expr::Block((), e) => e,
    },
);
match result {
    LangRes::Stmt(()) => { /* root was a Stmt */ }
    LangRes::Expr(n)  => { /* root was an Expr */ }
}
```

Each algebra receives its sort's node with children already replaced by
their sort-appropriate results. `Stmt` children are `()`, `Expr` children
are `i64`. This is the multi-sorted initial algebra: N algebras, N result
types, one pass.

### How `multi_map` makes this work

In the single-functor case, `Functor::map` applies one function `R → S` to
all children. In the multi-sorted case, `multi_map` applies a different
function per sort:

```
multi_map(f₀: S₀ → D₀, f₁: S₁ → D₁) : F(S₀, S₁) → F(D₀, D₁)
```

Inside `fold_multi`, the flow for each node is:

1. Clone the node from the arena: `Lang<usize, usize>`
2. `multi_map` it: child of sort 0 → extract `A0`, child of sort 1 → extract `A1`
3. Result: `Lang<A0, A1>`
4. `dispatch` into the right algebra: `Stmt<A0, A1> → A0` or `Expr<A0, A1> → A1`
5. Wrap in `LangRes::Stmt(a0)` or `LangRes::Expr(a1)`

The uniform `Functor::map` is the special case where all params are the same:
`Lang<R, R>` mapped by one function `R → S` gives `Lang<S, S>`. That's why
`Arena<Lang<usize, usize>>` works with all the single-functor schemes unchanged.

### Generalizes to N sorts

The construction is uniform. Three sorts:

```rust
rec_family! {
    family Lang;
    enum Stmt { ... }
    enum Expr { ... }
    enum Ty   { TInt, TBool, TFn(Ty, Ty) }
}
```

- `Lang<S0, S1, S2>` — three type params
- `fold_multi` takes three algebras, returns `LangRes<A0, A1, A2>`
- `multi_map` takes three mapping functions
- Per-sort enums only get the params they actually use:
  `Ty<S2>` (self-recursive only), `Expr<S1, S2>` (uses Expr + Ty), etc.

No limit on the number of sorts.

### Zero-clone multi-sort folds (ref variants)

The macro also generates ref-algebra variants for multi-sort folds:

| Generated function | Description |
|---|---|
| `fold_all_ref_*_multi` | Linear scan, algebras receive `Sort<&A0, &A1, ...>` |
| `fold_ref_*_multi` | Subtree fold, algebras receive `Sort<&A0, &A1, ...>` |

These eliminate child result cloning. The algebra signature changes from
owned children to borrowed children:

```rust
// Standard: algebra receives owned children
fold_lang_multi(&arena, root,
    |s: Stmt<String, String>| { ... },  // children are String
    |e: Expr<String, String>| { ... },
);

// Ref: algebra receives borrowed children
fold_ref_lang_multi(&arena, root,
    |s: Stmt<&String, &String>| { ... },  // children are &String
    |e: Expr<&String, &String>| { ... },
);
```

Data fields (StringId, i64, bool, etc.) remain owned — only child positions
become references. Use the ref variants when the result type is expensive
to clone (String, Vec). For cheap Copy types (i64, bool), the standard
variants are simpler and equally fast.

### Sort safety

The arena is untyped — `usize` doesn't know which sort it points to. If you
pass a `Stmt` id where an `Expr` is expected:

- **Uniform fold** (`dispatch`): silent — every child folds to the same type.
- **Multi-sorted fold** (`fold_multi`): **runtime panic** ("sort mismatch")
  because `multi_map` tries to unwrap the child's result as the wrong sort.

The multi-sorted fold catches sort violations eagerly. The uniform fold
doesn't, because it can't — all results are the same type.

### Ill-formed recursion

**Sort confusion at runtime**: If you write
`Lang::StmtAssign("x".into(), stmt_id.0)` where `stmt_id` points to a `Stmt`
node, the `Assign` variant expects an `Expr` child but gets a `Stmt`.
`fold_multi` catches this eagerly with a panic. Uniform `dispatch` is silent.

**Unproductive sorts**: A sort with no base case (every variant has at least
one child) can never produce a finite tree. Detectable at macro time by
checking the sort dependency graph.

### All existing schemes still work

`fold_with_ids`, `fold_with_history`, `fold_with_aux`, `unfold`, `transform`,
`fold_short` — everything works on `Arena<Lang<usize, usize>>` unchanged.
The coproduct is just another functor. Use `dispatch` inside any algebra to
get per-sort pattern matching.

For heterogeneous folds (different result type per sort), the macro generates
multi-sorted versions that take N algebras:

| Scheme | Generated function | Algebra signature per sort |
|---|---|---|
| `fold` | `fold_multi(arena, root, alg₀, alg₁)` | `Sort<A0, A1> → Ai` |
| `fold_with_ids` | `fold_with_ids_multi(arena, root, alg₀, alg₁)` | `Sort<(Id, A0), (Id, A1)> → Ai` |

Both return `LangRes<A0, A1>` — unwrap with `.unwrap_stmt()` / `.unwrap_expr()`.

The uniform approach (single result type via `dispatch`) remains simpler when
you don't need per-sort result types.

---

## Family Summary

| Feature | Single functor | Family (uniform) | Family (multi-sorted) |
|---|---|---|---|
| Type params | `E<R>` | `Lang<R, R>` | `Lang<S0, S1>` |
| Fold | `fold` | `fold` + `dispatch` | `fold_multi` |
| Result types | one `A` | one `A` | one `Ai` per sort |
| Child mapping | `map: (R→S) → F<R>→F<S>` | same | `multi_map: (S0→D0, S1→D1) → F→F` |
| Sort safety | N/A | none | panic on mismatch |
