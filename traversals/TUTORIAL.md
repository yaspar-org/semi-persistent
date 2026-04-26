# Tutorial: recursion schemes with `rec_family!`

This tutorial walks you through the `semi-persistent-traversals` crate by
building up a small compiler pipeline. Each section covers one scheme;
each scheme is a single method call where you write the algebra and the
library writes the recursion.

The full, tested version of every example lives in
[`tests/testorial.rs`](tests/testorial.rs).

## 1. Define the family

A *family* is a set of types that reference each other. In a small
imperative language, statements can contain expressions (think `print(x)`)
and expressions can contain statements (think `{ x = 1; x + 2 }`); neither
makes sense on its own. `rec_family!` declares all the types of a family
in one place and generates the machinery to store them: one arena per
type, typed IDs that prevent you from mixing them up, and a full suite of
traversals that cross between types automatically.

Here's the full declaration for a language we'll use throughout:

```rust
use semi_persistent_traversals_derive::rec_family;

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
```

Before diving into the syntax, a word on vocabulary.

### Sorts vs types

The word *sort* means "one of the categories in a family of mutually
recursive definitions". The word *type* means what it normally means in
Rust.

These documents keep the two separate because the macro does. A single
sort produces several Rust types, and mixing the words up makes the
generated API hard to read.

For the family above, `Stmt` and `Expr` are the two sorts. The word
`Stmt` appearing on line `enum Stmt { ... }` is a sort label, not a
Rust type; `Stmt` doesn't exist as a Rust type anywhere. Nor does
`Expr`. What *does* exist, after the macro runs, is a collection of
Rust types derived from each sort, shown next.

### What the macro generates

For this family, the macro expands to (abbreviated):

```rust
// --- IDs: one newtype per sort ---
pub struct StmtId(pub usize);
pub struct ExprId(pub usize);

// --- Nodes: one enum per sort, what lives in the arena ---
pub enum StmtNode {
    Let(String, ExprId),                // "Expr" in the macro became ExprId
    Seq(StmtId, StmtId),
    Print(ExprId),
    If(ExprId, StmtId, StmtId),
    While(ExprId, StmtId),
    Noop,
}

pub enum ExprNode {
    Var(String),
    Lit(i64),
    Bool(bool),
    Add(ExprId, ExprId),
    Mul(ExprId, ExprId),
    Neg(ExprId),
    Eq(ExprId, ExprId),
    Block(StmtId, ExprId),              // cross-sort: Stmt became StmtId
}

// --- Mapped nodes: what algebras see, with children replaced by results ---
pub enum StmtNodeMapped<A_stmt, A_expr> {
    Let(String, A_expr),
    Seq(A_stmt, A_stmt),
    Print(A_expr),
    If(A_expr, A_stmt, A_stmt),
    While(A_expr, A_stmt),
    Noop,
}

pub enum ExprNodeMapped<A_stmt, A_expr> {
    Var(String),
    Lit(i64),
    Bool(bool),
    Add(A_expr, A_expr),
    Mul(A_expr, A_expr),
    Neg(A_expr),
    Eq(A_expr, A_expr),
    Block(A_stmt, A_expr),
}

// --- Sort-tagged handles ---
pub enum LangStoreRoot {
    Stmt(StmtId),
    Expr(ExprId),
}

pub enum LangStoreFoldResult<A_stmt, A_expr> {
    Stmt(A_stmt),
    Expr(A_expr),
}

// --- The store: one arena per sort, plus all the scheme methods ---
pub struct LangStore { /* private: Vec<StmtNode>, Vec<ExprNode>, ... */ }

impl LangStore {
    pub fn new() -> Self { ... }
    pub fn new_dedup() -> Self { ... }

    pub fn push_stmt(&mut self, node: StmtNode) -> StmtId { ... }
    pub fn push_expr(&mut self, node: ExprNode) -> ExprId { ... }
    pub fn get_stmt(&self, id: StmtId) -> &StmtNode { ... }
    pub fn get_expr(&self, id: ExprId) -> &ExprNode { ... }
    pub fn len_stmt(&self) -> usize { ... }
    pub fn len_expr(&self) -> usize { ... }

    pub fn mark(&self) -> LangStoreMark { ... }
    pub fn restore(&mut self, mark: &LangStoreMark) { ... }

    pub fn fold<A_stmt: Clone, A_expr: Clone>(
        &self,
        root: LangStoreRoot,
        alg_stmt: impl Fn(StmtNodeMapped<A_stmt, A_expr>) -> A_stmt,
        alg_expr: impl Fn(ExprNodeMapped<A_stmt, A_expr>) -> A_expr,
    ) -> LangStoreFoldResult<A_stmt, A_expr> { ... }

    // ... every other scheme: fold_short, fold_with_history, fold_with_aux,
    //     fold_with_original, fold_pair, prefold, unfold, unfold_short,
    //     postunfold, transform, rewrite, rewrite_down, fold_all
}
```

A few things to notice.

**The enum name gets a `Node` suffix.** The sort is `Stmt`; the Rust enum
is `StmtNode`. Keeping them distinct means you can have your own type
called `Stmt` in the same module if you want, and it also reflects the
distinction above: `Stmt` is a category, `StmtNode` is the concrete
representation.

**Cross-sort fields in the original declaration become typed IDs in the
generated enum.** When you wrote `Let(String, Expr)` inside the macro,
`Expr` wasn't a Rust type — it was a sort label. The macro resolved it
to `ExprId`, the typed handle for `Expr` nodes. `StmtNode::Let` therefore
holds a `String` and an `ExprId`. Passing a `StmtId` to
`StmtNode::Let(..., stmt_id)` is a compile error.

**The mapped enum has one generic parameter per sort in the family.**
Both `StmtNodeMapped` and `ExprNodeMapped` take `<A_stmt, A_expr>` —
always in the order the sorts were declared. This is because any sort
can contain children of any other sort: `Expr::Block(Stmt, Expr)` has
both a `Stmt` child and an `Expr` child, so `ExprNodeMapped` needs the
result-type for each. Even if a sort happens not to reference another
sort in some variant, the parameter order stays consistent family-wide
so that the same two algebras can carry the same two result types
through both enums. The macro prunes *completely unused* parameters
(a sort that references no other sort in any variant), but in any
realistic mutually-recursive family all sort parameters are present.

**Variant payload order changes when children of different sorts appear.**
Compare `StmtNode::Let(String, ExprId)` to
`StmtNodeMapped::Let(String, A_expr)`: the data field stays put, and
only the ID gets replaced by the algebra's result. That's why the same
variant pattern works in both contexts.

### Reading the header line

```rust
family Lang => LangStore;
```

- `family` is a keyword that opens the declaration.
- `Lang` is the *family name*. It shows up as a prefix on a small number
  of generated types used by the unfold schemes: `LangSeed`, `LangLayer`,
  `LangApoSeed`, `LangApoLayer`. You rarely write `Lang` directly.
- `=>` separates the family name from the store name.
- `LangStore` is the *store type*. This is what you instantiate
  (`LangStore::new()`) and call every scheme method on. It's also the
  prefix for `LangStoreRoot`, `LangStoreFoldResult`, `LangStoreMark`,
  `LangStoreZipper`, `LangStoreZipperMut`, and `LangStoreZipperCow`.

The family name and store name can be anything; keep them descriptive.
An e-graph AST might be `family Egraph => ENodes` and you'd instantiate
`ENodes::new()`, get back an `ENodesRoot`, and so on.

### Declaring sorts and their variants

Each `enum` under the header declares one sort. Two rules:

1. **Sort declaration order is the argument order for every multi-algebra
   scheme.** The `Stmt` algebra comes first in `fold(..., alg_stmt,
   alg_expr)` because `enum Stmt` came first in the macro. That order
   also fixes the order of generic parameters on every mapped enum
   (`<A_stmt, A_expr>`) and the variant order of `LangStoreFoldResult`.
   Once set, it cascades everywhere.

2. **A variant field is either data or a child.** The macro distinguishes
   the two by matching field types against the sort names. `String`,
   `i64`, `bool`, `MyCustomStruct` — anything not mentioned as a sort
   name becomes a data field stored inline. `Stmt`, `Expr` — anything
   matching a sort name becomes a typed child ID. A third form,
   `Variadic<Sort>`, declares a variable-length list of children; see
   §N below for details.

## 2. Build an AST

```rust
fn sample() -> (LangStore, LangStoreRoot) {
    let mut s = LangStore::new();
    let one   = s.push_expr(ExprNode::Lit(1));
    let two   = s.push_expr(ExprNode::Lit(2));
    let three = s.push_expr(ExprNode::Lit(3));
    let prod  = s.push_expr(ExprNode::Mul(two, three));   // typed: Mul takes ExprId
    let sum   = s.push_expr(ExprNode::Add(one, prod));
    let bind  = s.push_stmt(StmtNode::Let("x".into(), sum));
    (s, LangStoreRoot::Stmt(bind))
}
```

`LangStoreRoot` is a sort-tagged handle — `Stmt(StmtId)` or `Expr(ExprId)`.
Schemes that take a "root" accept a `LangStoreRoot` so they can start from
either sort.

## 3. `fold` — bottom-up traversal

`fold` takes **one algebra per sort, in declaration order**. Each algebra
receives a mapped node (children already replaced by results) and returns
the result for that node. Sorts can return different types.

Pretty-printer: `Stmt → String`, `Expr → String`.

```rust
let rendered = s.fold(
    root,
    |stmt: StmtNodeMapped<String, String>| match stmt {
        StmtNodeMapped::Let(n, v)   => format!("{n} = {v}"),
        StmtNodeMapped::Seq(l, r)   => format!("{l}; {r}"),
        StmtNodeMapped::Print(e)    => format!("print({e})"),
        StmtNodeMapped::If(c, t, e) => format!("if ({c}) {t} else {e}"),
        StmtNodeMapped::While(c, b) => format!("while ({c}) {b}"),
        StmtNodeMapped::Noop        => "noop".into(),
    },
    |expr: ExprNodeMapped<String, String>| match expr {
        ExprNodeMapped::Var(n)      => n,
        ExprNodeMapped::Lit(n)      => n.to_string(),
        ExprNodeMapped::Bool(b)     => b.to_string(),
        ExprNodeMapped::Add(l, r)   => format!("({l} + {r})"),
        ExprNodeMapped::Mul(l, r)   => format!("({l} * {r})"),
        ExprNodeMapped::Neg(e)      => format!("(-{e})"),
        ExprNodeMapped::Eq(l, r)    => format!("({l} == {r})"),
        ExprNodeMapped::Block(s, e) => format!("{{ {s}; {e} }}"),
    },
);
let rendered: String = rendered.unwrap_stmt();
```

The return is a sort-tagged `LangStoreFoldResult<String, String>`. Call
`.unwrap_stmt()` when you know the root is a `Stmt`; match on it when you
don't.

### What the two `String`s mean

The mapped enums were generated as (recap from §1):

```rust
enum StmtNodeMapped<A_stmt, A_expr> { Let(String, A_expr), Seq(A_stmt, A_stmt), ... }
enum ExprNodeMapped<A_stmt, A_expr> { Block(A_stmt, A_expr), Add(A_expr, A_expr), ... }
```

The first parameter stands for "whatever the `Stmt` algebra returns",
the second for "whatever the `Expr` algebra returns". In this fold
both algebras return `String`, so both parameters become `String`, and
you write `StmtNodeMapped<String, String>` and
`ExprNodeMapped<String, String>` on each algebra's input.

Watch what happens inside each variant:

- `StmtNodeMapped::Let(n, v)`: `n: String` is the data field (it was
  `String` in the original declaration, stays `String` in the mapped
  form); `v` has type *the second parameter*, because the `Let`
  variant's second field was declared `Expr`. In this fold `v: String`.
- `StmtNodeMapped::Seq(l, r)`: `l` and `r` both have type *the first
  parameter*, because `Seq`'s fields were both `Stmt`. In this fold
  `l: String` and `r: String`.
- `ExprNodeMapped::Block(s, e)`: `s` has type *the first parameter*
  (field was `Stmt`), `e` has type *the second parameter* (field was
  `Expr`).

That's why the parameter order is family-wide, not per-sort: both
algebras need to know the same two type variables in the same order,
so that `ExprNodeMapped::Block(s, e)` consistently means "s is
whatever the Stmt algebra returns, e is whatever the Expr algebra
returns" no matter which algebra you're inside.

A concrete variation: to render statements as `Vec<u8>` bytecode while
keeping expressions as `i64` values, you'd write

```rust
s.fold(
    root,
    |stmt: StmtNodeMapped<Vec<u8>, i64>| { /* returns Vec<u8> */ },
    |expr: ExprNodeMapped<Vec<u8>, i64>| { /* returns i64     */ },
);
```

Inside the `Stmt` algebra, `Let(n, v)` would give you `n: String` and
`v: i64` (the Expr result type). Inside the `Expr` algebra, `Block(s, e)`
would give you `s: Vec<u8>` (the Stmt result type) and `e: i64`.

## 4. `fold` with different per-sort types

The interpreter evaluates expressions to `i64` and statements to environment
transformers:

```rust
use std::collections::HashMap;
use std::rc::Rc;

type Env   = HashMap<String, i64>;
type SVal  = Rc<dyn Fn(&Env) -> Env>;  // Stmt result
type EVal  = Rc<dyn Fn(&Env) -> i64>;  // Expr result

let result = s.fold(
    root,
    |stmt: StmtNodeMapped<SVal, EVal>| -> SVal {
        match stmt {
            StmtNodeMapped::Let(name, val) => Rc::new(move |env| {
                let mut e = env.clone();
                e.insert(name.clone(), val(env));
                e
            }),
            StmtNodeMapped::Seq(l, r)   => Rc::new(move |env| r(&l(env))),
            StmtNodeMapped::Print(v)    => Rc::new(move |env| { let _ = v(env); env.clone() }),
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
            ExprNodeMapped::Lit(n)      => Rc::new(move |_| n),
            ExprNodeMapped::Var(name)   => Rc::new(move |env| *env.get(&name).unwrap_or(&0)),
            ExprNodeMapped::Add(l, r)   => Rc::new(move |env| l(env) + r(env)),
            ExprNodeMapped::Mul(l, r)   => Rc::new(move |env| l(env) * r(env)),
            // …
            _ => Rc::new(|_| 0),
        }
    },
);
```

Key property: the `SVal` algebra sees `Expr` children as `EVal` (closures
returning `i64`), and the `EVal` algebra sees `Stmt` children as `SVal`.
Cross-sort references are carried through the fold automatically.

## 5. `rewrite` — bottom-up tree-to-tree transform

`rewrite` gives each rule a `&mut Store` to push into and returns a typed
ID for the sort. Use it to create new nodes, inspect already-rewritten
children, or collapse structure.

Constant folding:

```rust
let (s2, r2) = s.rewrite(
    root,
    // Stmt rule: pass through
    |node, new: &mut LangStore| new.push_stmt(node),
    // Expr rule: fold literal arithmetic
    |node, new: &mut LangStore| match node {
        ExprNode::Add(l, r) => {
            if let (ExprNode::Lit(a), ExprNode::Lit(b)) = (new.get_expr(l), new.get_expr(r)) {
                return new.push_expr(ExprNode::Lit(a + b));
            }
            new.push_expr(ExprNode::Add(l, r))
        }
        ExprNode::Mul(l, r) => { /* … */ new.push_expr(ExprNode::Mul(l, r)) }
        ExprNode::Neg(e) => {
            if let ExprNode::Lit(n) = new.get_expr(e) {
                return new.push_expr(ExprNode::Lit(-n));
            }
            new.push_expr(ExprNode::Neg(e))
        }
        other => new.push_expr(other),
    },
);
```

Because `rewrite` is bottom-up, by the time the rule sees `Add(l, r)` the
children `l` and `r` are already in `new`. Inspecting them via
`new.get_expr(l)` gives you the *rewritten* child, not the original.

## 6. `rewrite_down` — top-down transform

Same signature as `rewrite`, but the rule fires on the way down. The rewritten
node's children are then visited and rewritten in turn. Use when a node needs
to decide based on *itself*, not its children.

```rust
// Replace every Neg(x) with Mul(x, x) top-down
let (s2, r2) = s.rewrite_down(
    root,
    |stmt| stmt,
    |expr| match expr {
        ExprNode::Neg(inner) => ExprNode::Mul(inner, inner),
        other => other,
    },
);
```

On `Neg(Neg(5))`, the outer `Neg` fires first → `Mul(Neg(5), Neg(5))`. Then
the inner `Neg`s fire → `Mul(Mul(5,5), Mul(5,5))`. Result: 625.

## 7. `fold_short` — early exit

Each algebra returns `Result<A, A>`. `Ok(v)` continues; `Err(v)` exits the
fold immediately, returning that value.

```rust
let found = s.fold_short(
    root,
    |stmt: StmtNodeMapped<bool, bool>| match stmt {
        StmtNodeMapped::If(cond_false, _, _) if cond_false => Err(true), // dead code!
        StmtNodeMapped::Seq(l, r) => Ok(l || r),
        _ => Ok(false),
    },
    |expr: ExprNodeMapped<bool, bool>| match expr {
        ExprNodeMapped::Bool(false) => Ok(true),
        _ => Ok(false),
    },
);
```

## 8. `fold_with_history` — look-back at grandchildren

The algebra receives `Ann<A>` instead of `A`. `Ann` exposes the child's
`value` and its `children` (raw IDs), letting you peek one level deeper.

```rust
use semi_persistent_traversals::Ann;

let complexity = s.fold_with_history(
    root,
    |stmt: StmtNodeMapped<Ann<usize>, Ann<usize>>| /* … */,
    |expr: ExprNodeMapped<Ann<usize>, Ann<usize>>| {
        // Penalize deep nesting: binary ops whose children are themselves deep cost extra.
        let penalty = match &expr {
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) => {
                let deep = !l.children.is_empty() && !r.children.is_empty();
                if deep { 2 } else { 0 }
            }
            _ => 0,
        };
        /* … base cost + penalty … */
    },
);
```

## 9. `fold_with_aux` — two folds in one pass (zygomorphism)

Two algebras per sort. The *aux* algebra runs first and sees only
`B`-children; the *main* algebra then sees `(A, B)` children, with
access to both the current result and the aux result.

Type-checking followed by type-aware evaluation:

```rust
let result = s.fold_with_aux(
    root,
    // aux: Stmt → &str
    |_: StmtNodeMapped<&str, &str>| "stmt",
    // aux: Expr → &str  ("int" | "bool" | "err")
    |expr: ExprNodeMapped<&str, &str>| match expr { /* type check */ },
    // main: Stmt → i64
    |_: StmtNodeMapped<(i64, &str), (i64, &str)>| 0,
    // main: Expr → i64  (evaluate, using type from aux to guard)
    |expr: ExprNodeMapped<(i64, &str), (i64, &str)>| match expr {
        ExprNodeMapped::Add((l, lt), (r, rt)) =>
            if lt == "int" && rt == "int" { l + r } else { -1 },
        /* … */
    },
);
```

## 10. `fold_pair` — mutually recursive folds

Two algebras per sort, each returning a different type, both seeing all
children as `(A, B)` pairs. Use when two folds depend on each other's
intermediate results at every node.

## 11. `fold_with_original` — see the pre-mapped node

The algebra receives `(&OriginalNode, MappedNode)`. Use when the cost or
shape of a node depends on its *structure*, not just its children's results.

```rust
let cost = s.fold_with_original(
    root,
    |orig: &StmtNode, mapped: StmtNodeMapped<usize, usize>| { /* … */ },
    |orig: &ExprNode, mapped: ExprNodeMapped<usize, usize>| {
        let own = match orig {
            ExprNode::Add(..) | ExprNode::Mul(..) | ExprNode::Eq(..) => 2, // binary ops
            ExprNode::Neg(..) => 1,
            _ => 0,
        };
        let child_cost = /* sum from mapped */;
        child_cost + own
    },
);
```

## 12. `unfold` and `unfold_short` — top-down construction

`unfold` builds a tree from a seed, top-down. The coalgebra takes a seed
and returns a `LangStoreLayer`: a node with child *seeds* in place of
child IDs. Seeds expand recursively until they bottom out.

```rust
let root = s.unfold(
    LangStoreSeed::Expr(3u32),
    |seed| match seed {
        LangStoreSeed::Expr(0) => LangStoreLayer::Expr(ExprNode::Lit(1), vec![]),
        LangStoreSeed::Expr(n) => LangStoreLayer::Expr(
            ExprNode::Add(ExprId(0), ExprId(0)),       // placeholder ids
            vec![LangStoreSeed::Expr(n - 1), LangStoreSeed::Expr(n - 1)],
        ),
        LangStoreSeed::Stmt(_) => unreachable!(),
    },
);
```

The child IDs in the returned node are placeholders — `unfold` replaces them
with the real IDs once each child has been built.

`unfold_short` is the apomorphism: the coalgebra can return `Done(id)` to
reuse an existing node instead of continuing to expand.

## 13. `prefold` and `postunfold` — normalization passes

- `prefold(pre, alg)` — apply a per-sort `Node → Node` rewrite before
  folding. Use for strength reduction, desugaring, or any transform you
  want "baked in" before the fold sees it.
- `postunfold(post, coalg)` — apply a per-sort `Node → Node` rewrite
  after each unfold layer, before the node is pushed. Use for
  canonicalization (e.g., sort commutative operands).

## 14. Hash-consing with `new_dedup`

`LangStore::new_dedup()` adds a per-sort hashmap. Pushing a node that's
already been pushed returns the existing ID instead of appending a
duplicate:

```rust
let mut s = LangStore::new_dedup();
let a = s.push_expr(ExprNode::Lit(42));
let b = s.push_expr(ExprNode::Lit(42));
assert_eq!(a, b);
assert_eq!(s.len_expr(), 1);
```

Dedup is per-sort: pushing an `Expr` doesn't consult the `Stmt` table.
Dedup interacts correctly with `mark`/`restore` — on restore, dedup
entries pointing past the mark are pruned.

## 15. Memoization strategies

`fold` defaults to dense memoization — a `Vec<Option<A>>` sized to the
full store. Two alternatives via `with_strategy`:

```rust
use semi_persistent_traversals::{Sparse, memo};

// Sparse: hashmap memo, O(reachable) allocation.
// Use when folding a small subtree inside a large store.
let r = s.with_strategy::<Sparse>().fold(root, alg_stmt, alg_expr);

// None: no dedup checks. Fastest for pure trees (no structural sharing).
// INCORRECT on DAGs — will recompute shared subtrees.
let r = s.with_strategy::<memo::None>().fold(root, alg_stmt, alg_expr);
```

See [`doc/design/memo-and-dedup.md`](doc/design/memo-and-dedup.md) for the
full decision guide with benchmark numbers.

## 16. Zippers — cursor-based navigation

Sometimes you need to walk up from a node, check siblings, or patch the
tree at a focused location. Zippers give you a stack of "crumbs" for the
path from root to the focus:

```rust
// Read-only: Zipper
let mut z = LangStoreZipper::new(&s, root);
z.down(1);  // into first child of focus
z.down(1);
z.up();     // back up one crumb
match z.focus() { LangStoreRoot::Expr(id) => /* … */, _ => panic!() }

// Mutation in place: ZipperMut
let mut z = LangStoreZipperMut::new(&mut s, root);
z.down(0);
z.set_focus_expr(ExprNode::Lit(42));  // overwrites in place

// Copy-on-write: ZipperCow — builds a new store containing the spine
// and unchanged subtrees, leaves original untouched
let z = LangStoreZipperCow::new(&s, root);
let (new_store, new_root) = z.set_focus_expr(ExprNode::Lit(3));
```

## 17. The full chapter list

For worked examples of each scheme applied to a real compiler pipeline
(pretty printer, constant folder, type checker, interpreter, bytecode
compiler), see [`tests/testorial.rs`](tests/testorial.rs):

| Ch | Scheme |
|----|--------|
|  1 | `fold` |
|  2 | `rewrite` — constant folding |
|  3 | `rewrite` — double negation |
|  4 | `fold_short` — find a variable |
|  5 | `unfold` — generate an AST |
|  6 | `unfold_short` — build with node reuse |
|  8 | `rewrite` — desugar while loops |
|  9 | `fold` — type inference |
| 10 | `fold` — interpreter |
| 11 | `fold` — free variables |
| 12 | `fold` — precedence-aware pretty printer |
| 13 | `fold_with_history` — depth complexity |
| 14 | `fold_with_aux` — type check + evaluate |
| 15 | `fold_pair` — saturating eval |
| 16 | `prefold` — simplify then eval |
| 17 | `postunfold` — canonicalize during build |
| 19 | `rewrite_down` — top-down desugar |
| 20 | `fold_with_original` — cost model |
| 21 | `fold_short` — dead code search |
| 22 | `prefold` — desugar then eval (multi-sorted) |
| 23 | `fold` — compile to bytecode |
| 24 | `Zipper` — find binder via sibling |
| 25 | `ZipperMut` — walk up and patch |
| 26 | `ZipperCow` — specialize shared subtree |

Each chapter is a standalone `#[test]`, so you can run them individually
and step through in your editor.
