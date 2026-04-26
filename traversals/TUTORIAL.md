# Tutorial: recursion schemes with `rec_family!`

This tutorial walks you through the `semi-persistent-traversals` crate by
building up a small compiler pipeline. Each section covers one scheme;
each scheme is a single method call where you write the algebra and the
library writes the recursion.

The full, tested version of every example lives in
[`tests/testorial.rs`](tests/testorial.rs).

## 1. Define the family

`rec_family!` declares a family of mutually recursive types and generates
a per-sort arena store:

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

### The header line

```rust
family Lang => LangStore;
```

- `family` is a keyword that starts the declaration.
- `Lang` is the **family name**. It's a label used in the macro's internal
  bookkeeping and shows up in the names of generated companion types
  (`LangSeed`, `LangLayer`, `LangApoSeed`, `LangApoLayer` for the unfold
  schemes). You rarely type `Lang` directly in user code.
- `=>` separates the family name from the store name.
- `LangStore` is the **store type** the macro generates for you. It owns
  the per-sort arenas. You create one with `LangStore::new()` or
  `LangStore::new_dedup()` and call every scheme method on it. The store
  name is also the prefix for generated companion types: `LangStoreRoot`
  (sort-tagged handle), `LangStoreFoldResult<A, B, …>` (sort-tagged fold
  return), `LangStoreMark` (snapshot handle), `LangStoreZipper` (and
  `ZipperMut` / `ZipperCow` variants).
- The trailing `;` ends the header.

The family name and store name can be anything you want; keep them
descriptive. For an e-graph AST you might write `family Egraph => ENodes`
and get `ENodes::new()`, `ENodesRoot`, `ENodesFoldResult`, etc.

### The enum declarations

Each `enum` under the header declares one **sort** in the family. Sort
order matters: it determines the argument order for every multi-algebra
scheme (`fold`, `rewrite`, `prefold`, …) — one closure per sort, in the
order the sorts were declared.

Variant fields can be:

- A **data field** (`String`, `i64`, `bool`, any type not mentioned as
  a sort name in this family): stored inline in the node.
- A **child field** referring to a sort name in the same family
  (`Stmt`, `Expr`): stored as a typed ID. `Stmt(Stmt, Expr)` means
  "contains one child of sort Stmt and one of sort Expr"; the macro
  generates `StmtNode::Seq(StmtId, ExprId)` where those IDs point
  into the appropriate per-sort arena.
- A **variadic child field** spelled `Variadic<Sort>`: a variable-length
  list of children, stored inline for short lists and pooled for longer
  ones. See [section on Variadic](#variadic-children-optional) below.

### Generated types per sort

For every sort `S` (e.g. `Stmt`, `Expr`), the macro generates:

- `SNode` — the concrete node enum stored in the arena. Cross-sort
  references are typed IDs: `StmtNode::Let(String, ExprId)`.
- `SId` — a newtype wrapping `usize`. Using an `ExprId` where a `StmtId`
  is expected is a compile error.
- `SNodeMapped<A, B, …>` — the "mapped" node where child IDs have been
  replaced by algebra results. Generic only over the sort result types
  it actually references: if `Stmt` never contains an `Expr`,
  `StmtNodeMapped` is generic only in `A_stmt`.

The store provides per-sort methods: `push_stmt(StmtNode) -> StmtId`,
`get_stmt(StmtId) -> &StmtNode`, `len_stmt() -> usize`, plus `mark()`,
`restore(&mark)`, and the scheme methods covered in the rest of this
tutorial.

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
