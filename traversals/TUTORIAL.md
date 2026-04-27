# Tutorial: recursion schemes with `rec_family!`

This tutorial walks through the `semi-persistent-traversals` crate by
building a small compiler pipeline. Each section introduces one scheme,
explains what problem it solves, and shows a worked example. Every
example is a real `#[test]` in [`tests/testorial.rs`](tests/testorial.rs),
so you can run them and step through in your editor as you read.

The running language is a tiny imperative language with statements and
expressions. We define it once in §1 and reuse it throughout.

## 1. Define the family

A *family* is a set of types that reference each other. The language
here has statements that contain expressions (think `print(x)`) and
expressions that contain statements (think `{ x = 1; x + 2 }`). Neither
type is meaningful on its own. `rec_family!` declares both types in one
place and generates the supporting machinery: per-type arenas, typed
IDs to keep them straight, and traversal schemes that cross between
types automatically.

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

Before walking through the syntax, a note on vocabulary.

### Sorts versus types

The word *sort* is used throughout the crate to mean "one of the
categories in a mutually recursive family". The word *type* keeps its
ordinary Rust meaning.

The two are kept separate because the macro does. A single sort
produces several distinct Rust types, and using one word for both
makes the generated API confusing. In the family above, `Stmt` and
`Expr` are the two sorts. The identifier `Stmt` on the line
`enum Stmt { ... }` is a sort label inside the macro; it is not a Rust
type that you can refer to elsewhere. What does exist after the macro
runs is a collection of Rust types derived from each sort.

### What the macro generates

For the family above, the macro produces (abbreviated):

```rust
// One newtype per sort, used as a typed arena handle.
pub struct StmtId(pub usize);
pub struct ExprId(pub usize);

// One enum per sort, stored in the arena. Cross-sort fields became typed IDs.
pub enum StmtNode {
    Let(String, ExprId),
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
    Block(StmtId, ExprId),
}

// One mapped enum per sort. Algebras receive this: child IDs replaced by results.
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

// Sort-tagged root handle and fold-result enum.
pub enum LangStoreRoot {
    Stmt(StmtId),
    Expr(ExprId),
}

pub enum LangStoreFoldResult<A_stmt, A_expr> {
    Stmt(A_stmt),
    Expr(A_expr),
}

// The store owns one arena per sort and provides all scheme methods.
pub struct LangStore { /* ... */ }

impl LangStore {
    pub fn new() -> Self { /* ... */ }
    pub fn new_dedup() -> Self { /* ... */ }

    pub fn push_stmt(&mut self, node: StmtNode) -> StmtId { /* ... */ }
    pub fn push_expr(&mut self, node: ExprNode) -> ExprId { /* ... */ }
    pub fn get_stmt(&self, id: StmtId) -> &StmtNode { /* ... */ }
    pub fn get_expr(&self, id: ExprId) -> &ExprNode { /* ... */ }
    pub fn len_stmt(&self) -> usize { /* ... */ }
    pub fn len_expr(&self) -> usize { /* ... */ }

    pub fn mark(&self) -> LangStoreMark { /* ... */ }
    pub fn restore(&mut self, mark: &LangStoreMark) { /* ... */ }

    pub fn fold<A_stmt: Clone, A_expr: Clone>(
        &self,
        root: LangStoreRoot,
        alg_stmt: impl Fn(StmtNodeMapped<A_stmt, A_expr>) -> A_stmt,
        alg_expr: impl Fn(ExprNodeMapped<A_stmt, A_expr>) -> A_expr,
    ) -> LangStoreFoldResult<A_stmt, A_expr> { /* ... */ }

    // fold_short, fold_with_history, fold_with_aux, fold_with_original,
    // fold_pair, prefold, unfold, unfold_short, postunfold, transform,
    // rewrite, rewrite_down, fold_all: all follow the same per-sort pattern.
}
```

Four observations about this expansion.

The enum name carries a `Node` suffix. The sort is `Stmt`; the generated
Rust enum is `StmtNode`. Keeping the two names distinct means a user
type called `Stmt` in the same module will not collide with macro
output, and the naming reflects the split between the category (`Stmt`)
and its concrete representation (`StmtNode`).

Cross-sort fields in the original declaration become typed IDs in the
generated enum. When the original declaration says `Let(String, Expr)`,
the word `Expr` there is a sort label, not a Rust type. The macro
resolves it to `ExprId`, so `StmtNode::Let` holds a `String` and an
`ExprId`. Passing a `StmtId` where an `ExprId` is expected is a compile
error, which is what "typed IDs" really buys you.

Both mapped enums take the same pair of generic parameters
`<A_stmt, A_expr>`, in the order the sorts were declared. This is
necessary because any sort can contain children of any other sort.
`ExprNode::Block(Stmt, Expr)` has both a `Stmt` child and an `Expr`
child, so `ExprNodeMapped` needs to know the result type for each. The
parameter order is family-wide rather than per-sort so that a single
pair of algebras can carry the same pair of result types through both
enums consistently. The macro does prune a sort parameter when a sort
is referenced nowhere in any variant, but that rarely matters for
genuinely mutually recursive families.

The mapped enum mirrors the node enum variant by variant, replacing
each child ID with the corresponding sort parameter. Compare
`StmtNode::Let(String, ExprId)` with
`StmtNodeMapped::Let(String, A_expr)`: the `String` data field stays
put, only the `ExprId` became `A_expr`. The same pattern match against
`Let(n, v)` works in both contexts, which is what makes fold algebras
easy to write.

### Reading the header line

```rust
family Lang => LangStore;
```

`family` is a keyword that opens the declaration. `Lang` is the family
name; it shows up as a prefix on a small number of generated companion
types used by the unfold schemes (`LangSeed`, `LangLayer`,
`LangApoSeed`, `LangApoLayer`). You rarely write `Lang` directly. The
`=>` separator is followed by `LangStore`, the store type you
instantiate with `LangStore::new()` or `LangStore::new_dedup()`.
`LangStore` is also the prefix for `LangStoreRoot`,
`LangStoreFoldResult`, `LangStoreMark`, `LangStoreZipper`,
`LangStoreZipperMut`, and `LangStoreZipperCow`. Both names are
arbitrary; pick something descriptive for your domain.

### Declaring sorts and their variants

Each `enum` block under the header declares one sort. Two rules govern
them:

1. The declaration order of sorts is the argument order of every
   multi-algebra scheme. Because `enum Stmt` appears before `enum Expr`,
   the `Stmt` algebra comes first in `fold(..., alg_stmt, alg_expr)`.
   That order also fixes the order of generic parameters on every
   mapped enum (`<A_stmt, A_expr>`) and the variant order of
   `LangStoreFoldResult`. Set it once and it cascades everywhere.

2. A variant's fields are classified by matching their types against
   the sort names. Any type that is not a sort name (`String`, `i64`,
   `bool`, any user type) becomes a data field stored inline in the
   node. Any type that matches a sort name becomes a typed child ID.
   A third form, `Variadic<Sort>`, declares a variable-length list of
   children of that sort, covered in §14 below.

## 2. Build an AST

With the family declared, you build ASTs by pushing nodes into the
store. The typed IDs make it impossible to put a `Stmt` where an `Expr`
is expected.

```rust
fn sample() -> (LangStore, LangStoreRoot) {
    let mut s = LangStore::new();
    let one   = s.push_expr(ExprNode::Lit(1));
    let two   = s.push_expr(ExprNode::Lit(2));
    let three = s.push_expr(ExprNode::Lit(3));
    let prod  = s.push_expr(ExprNode::Mul(two, three));
    let sum   = s.push_expr(ExprNode::Add(one, prod));
    let bind  = s.push_stmt(StmtNode::Let("x".into(), sum));
    (s, LangStoreRoot::Stmt(bind))
}
```

`LangStoreRoot` is a sort-tagged handle, either `Stmt(StmtId)` or
`Expr(ExprId)`. Schemes that accept a root take this enum so they can
start from either sort.

### Smart constructors (optional)

The calls above are wordy. Every construction mentions the store, the
node enum, and the variant name, even though the enum and variant are
already clear from the arguments. Adding the `#[smart_constructors]`
attribute at the top of the `rec_family!` invocation asks the macro to
generate one constructor method per variant:

```rust
rec_family! {
    #[smart_constructors]
    family Lang => LangStore;
    // ... same enums as before ...
}
```

With that attribute, the store gains methods like `s.lit(1)`,
`s.add(l, r)`, `s.let_("x", sum)`, and so on. The method name is the
variant name lowercased, with a trailing underscore when the result
would collide with a Rust keyword (`let_`, `if_`, `while_`). The
sample builder becomes:

```rust
fn sample() -> (LangStore, LangStoreRoot) {
    let mut s = LangStore::new();
    let one   = s.lit(1);
    let two   = s.lit(2);
    let three = s.lit(3);
    let prod  = s.mul(two, three);
    let sum   = s.add(one, prod);
    let bind  = s.let_("x", sum);
    (s, LangStoreRoot::Stmt(bind))
}
```

The generated constructors apply two small ergonomic improvements.
Fields declared `String` become `impl Into<String>` in the method
signature, so `s.let_("x", sum)` accepts a `&str` directly without
a `.to_string()` call. Fields declared `Variadic<Sort>` become
`&[SortId]`, and the method calls the corresponding `alloc_*` pool
helper internally, so you write `s.call("f", &[a, b, c])` instead of
`s.alloc_stmt_expr(&[a, b, c])` followed by a `push_stmt`.

Two limitations. First, the macro generates one method per variant
across all sorts in the family, so two variants in different sorts
that would share a method name (both lowercase to `add`, for example)
produce a `compile_error!` at macro expansion time. Rename one of the
colliding variants, or drop `#[smart_constructors]` and write the
helpers you want by hand.

Second, the methods take `&mut self`, so you cannot nest two calls
on the same store in one expression. Rust's borrow checker rejects

```rust
let _ite = s.if_(s.lit(1), bind, noop);  // error: cannot borrow `s` twice
```

because the inner `s.lit(1)` borrows `s` mutably while `s.if_` also
borrows `s` mutably. The fix is to bind sub-expressions to locals:

```rust
let cond = s.lit(1);
let _ite = s.if_(cond, bind, noop);
```

This is the tradeoff for the compactness the constructors buy you
elsewhere. For a language with deep nesting in its AST construction,
the hand-written helpers in the next paragraph may read better.

### Hand-written helpers

If you do not want the smart constructor API, or you want finer
control over argument ergonomics than `#[smart_constructors]` offers
(different field conversions, currying, custom argument names),
define small free functions:

```rust
fn lit(s: &mut LangStore, n: i64) -> ExprId {
    s.push_expr(ExprNode::Lit(n))
}

fn add(s: &mut LangStore, l: ExprId, r: ExprId) -> ExprId {
    s.push_expr(ExprNode::Add(l, r))
}
```

Free functions compose the same way but stay outside the `LangStore`
impl, which keeps the inherent API surface small and gives you full
control over signatures.

## 3. `fold`: bottom-up traversal

A fold walks the tree from the leaves up and combines child results.
You write an *algebra* for each sort: a function that takes one node
with its child IDs already replaced by the algebra's results and
returns the result for that node. The library handles the traversal,
the stack, and the memoization.

Here is a pretty-printer that turns the AST back into source-like
text. Both sorts produce `String`.

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

The return is a `LangStoreFoldResult<String, String>`. The root is a
`Stmt`, so `unwrap_stmt()` gives the `String` directly; if you did not
know the root sort in advance, you would match on the variants.

### Reading the type parameters

Recall the generated mapped enums:

```rust
enum StmtNodeMapped<A_stmt, A_expr> { Let(String, A_expr), Seq(A_stmt, A_stmt), ... }
enum ExprNodeMapped<A_stmt, A_expr> { Block(A_stmt, A_expr), Add(A_expr, A_expr), ... }
```

The first parameter is the result type of the `Stmt` algebra; the
second is the result type of the `Expr` algebra. Writing
`StmtNodeMapped<String, String>` means both algebras happen to return
`String` in this fold. Inside each variant, the field types are
determined by the variant declaration:

- In `StmtNodeMapped::Let(n, v)`, the binding `n: String` comes from
  the original data field; `v: String` is the result of folding the
  `Expr` child, bound to the second type parameter.
- In `StmtNodeMapped::Seq(l, r)`, both `l` and `r` are `String`s from
  the first type parameter, because both `Seq` fields were declared
  `Stmt`.
- In `ExprNodeMapped::Block(s, e)`, `s: String` is bound to the first
  parameter (the field was `Stmt`) and `e: String` to the second (the
  field was `Expr`).

The parameter order is family-wide, not per-sort. The `Expr` algebra
still sees `<A_stmt, A_expr>` as its mapped-enum parameters, in that
order, because `Block` contains a `Stmt` child whose result type the
algebra must know.

If statements rendered as `Vec<u8>` bytecode and expressions rendered
as `i64` values, the call would look like

```rust
s.fold(
    root,
    |stmt: StmtNodeMapped<Vec<u8>, i64>| { /* returns Vec<u8> */ },
    |expr: ExprNodeMapped<Vec<u8>, i64>| { /* returns i64     */ },
);
```

and inside the statement algebra `Let(n, v)` would bind `n: String` and
`v: i64`, while inside the expression algebra `Block(s, e)` would bind
`s: Vec<u8>` and `e: i64`.

## 4. Folding to different per-sort types: interpreter

A real use of per-sort types shows up in an interpreter. Statements
transform an environment (a mapping from variable names to values);
expressions evaluate to an integer in an environment. The two result
types differ but share the environment they operate on.

```rust
use std::collections::HashMap;
use std::rc::Rc;

type Env   = HashMap<String, i64>;
type SVal  = Rc<dyn Fn(&Env) -> Env>;
type EVal  = Rc<dyn Fn(&Env) -> i64>;

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
            _ => Rc::new(|_| 0),
        }
    },
);
```

Notice how cross-sort references flow. Inside the statement algebra,
`Let(name, val)` binds `val: EVal` because the original field was
`Expr`. Inside the expression algebra, there would be a `Block(s, e)`
arm (omitted for brevity) that binds `s: SVal` because the field was
`Stmt`. The fold routes each child's result to the right algebra
automatically.

## 5. `rewrite`: bottom-up tree transform

`fold` reduces a tree to a value. `rewrite` reduces a tree to another
tree. Each rule receives a node whose child IDs already point into the
new store and must decide what node (if any) to emit. Because the new
store is passed as `&mut Store`, the rule can create new nodes, peek
at already-rewritten children, or collapse a subtree to a simpler one.

A constant folder is the classic example:

```rust
let (s2, r2) = s.rewrite(
    root,
    |node, new: &mut LangStore| new.push_stmt(node),
    |node, new: &mut LangStore| match node {
        ExprNode::Add(l, r) => {
            if let (ExprNode::Lit(a), ExprNode::Lit(b)) = (new.get_expr(l), new.get_expr(r)) {
                return new.push_expr(ExprNode::Lit(a + b));
            }
            new.push_expr(ExprNode::Add(l, r))
        }
        ExprNode::Mul(l, r) => { /* ... */ new.push_expr(ExprNode::Mul(l, r)) }
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

Because the rewrite runs bottom-up, by the time the `Add(l, r)` arm
fires the children at `l` and `r` are already in the new store. Calling
`new.get_expr(l)` returns the rewritten child, so if both children
rewrote to literals, the rule can push a single collapsed `Lit`.

## 6. `rewrite_down`: top-down transform

A bottom-up rewrite sees children before the parent. A top-down rewrite
sees the parent first, rewrites it, and then visits the (possibly new)
children. This ordering is what you want when the rewrite creates new
children that themselves need rewriting.

A small example: replace every `Neg(x)` with `Mul(x, x)`, top-down.

```rust
let (s2, r2) = s.rewrite_down(
    root,
    |stmt| stmt,
    |expr| match expr {
        ExprNode::Neg(inner) => ExprNode::Mul(inner, inner),
        other => other,
    },
);
```

Apply this to `Neg(Neg(5))`. The outer `Neg` is visited first and
rewrites to `Mul(Neg(5), Neg(5))`. Each of the inner `Neg(5)`s is then
visited and rewrites to `Mul(5, 5)`. The final tree is
`Mul(Mul(5, 5), Mul(5, 5))`, which evaluates to 625. A bottom-up
rewrite would miss the inner rewrites, because the outer `Neg` would
already have been consumed before its children were visited.

## 7. `fold_short`: early exit

A fold normally visits every reachable node. Sometimes you want to
stop as soon as a condition is met. `fold_short` gives each algebra
an early-exit hatch: the return type is `Result<A, A>`, where `Ok(v)`
continues the fold with result `v` and `Err(v)` ends it immediately
and returns `v`.

Here is a dead-code detector that exits as soon as it finds an
`If(false, _, _)`:

```rust
let found = s.fold_short(
    root,
    |stmt: StmtNodeMapped<bool, bool>| match stmt {
        StmtNodeMapped::If(cond_false, _, _) if cond_false => Err(true),
        StmtNodeMapped::Seq(l, r) => Ok(l || r),
        _ => Ok(false),
    },
    |expr: ExprNodeMapped<bool, bool>| match expr {
        ExprNodeMapped::Bool(false) => Ok(true),
        _ => Ok(false),
    },
);
```

The expression algebra tags every `Bool(false)` as "true, this is a
literal false". The statement algebra sees that tag arrive as the
first child of an `If`, and if so returns `Err(true)` to abort the
traversal.

## 8. `fold_with_history`: peek at grandchildren

A plain fold gives each algebra only the direct children's results. If
the decision at a node depends on what the grandchildren look like,
you need a scheme that carries more context through the recursion.
`fold_with_history` does exactly that: each algebra receives `Ann<A>`
instead of `A`, where `Ann` bundles a child's result with that child's
own children's raw IDs. You can look one level deeper without running
a second traversal.

A complexity score that penalizes deep nesting uses this:

```rust
use semi_persistent_traversals::Ann;

let complexity = s.fold_with_history(
    root,
    |stmt: StmtNodeMapped<Ann<usize>, Ann<usize>>| /* ... */,
    |expr: ExprNodeMapped<Ann<usize>, Ann<usize>>| {
        let penalty = match &expr {
            ExprNodeMapped::Add(l, r) | ExprNodeMapped::Mul(l, r) => {
                let deep = !l.children.is_empty() && !r.children.is_empty();
                if deep { 2 } else { 0 }
            }
            _ => 0,
        };
        /* base cost + penalty */
    },
);
```

Inside `Add(l, r)`, both `l` and `r` are `Ann<usize>` values. Reading
`l.value` gives the child's fold result; reading `l.children` reveals
the raw IDs of the grandchildren, which lets the algebra detect "this
child is itself an operation, not a leaf".

## 9. `fold_with_aux`: two folds in one pass

Some analyses want one pass to compute a preliminary value and a
second pass to compute a main value that depends on the preliminary.
Running two separate folds wastes work; `fold_with_aux` runs both in
one pass, with two algebras per sort. The aux algebra sees only its
own B-typed children. The main algebra sees `(A, B)` pairs, so it has
access to the aux result at every child along with the main result.

A type-aware interpreter is a natural fit. The aux pass annotates
each expression with its type; the main pass evaluates, and can refuse
to add a `Bool` to an `Int`.

```rust
let result = s.fold_with_aux(
    root,
    |_: StmtNodeMapped<&str, &str>| "stmt",
    |expr: ExprNodeMapped<&str, &str>| match expr { /* type check */ },
    |_: StmtNodeMapped<(i64, &str), (i64, &str)>| 0,
    |expr: ExprNodeMapped<(i64, &str), (i64, &str)>| match expr {
        ExprNodeMapped::Add((l, lt), (r, rt)) =>
            if lt == "int" && rt == "int" { l + r } else { -1 },
        /* ... */
    },
);
```

## 10. `fold_pair`: mutually recursive algebras

`fold_with_aux` has a direction: the aux pass feeds the main pass.
`fold_pair` is symmetric. Two algebras per sort, each producing a
different type, each seeing `(A, B)` pairs at every child. Use this
when two analyses genuinely depend on each other at every node, so
neither can be finished before the other starts.

A saturating evaluator does value and overflow-flag computation
together:

```rust
let (value, overflowed) = s.fold_pair(
    root,
    |_: StmtNodeMapped<(i64, bool), (i64, bool)>| 0i64,
    |_: StmtNodeMapped<(i64, bool), (i64, bool)>| false,
    |expr: ExprNodeMapped<(i64, bool), (i64, bool)>| match expr {
        ExprNodeMapped::Lit(n) => n,
        ExprNodeMapped::Add((l, lo), (r, ro)) => l.saturating_add(r),
        _ => 0,
    },
    |expr: ExprNodeMapped<(i64, bool), (i64, bool)>| match expr {
        ExprNodeMapped::Lit(_) => false,
        ExprNodeMapped::Add((l, lo), (r, ro)) => lo || ro || l.checked_add(r).is_none(),
        _ => false,
    },
).unwrap_expr();
```

Both algebras for the `Add` variant see the left and right children as
`(i64, bool)`: the value and its overflow flag. The value algebra
returns the (possibly saturated) sum; the overflow algebra returns
whether any child had already overflowed or whether this addition
newly overflows.

## 11. `fold_with_original`: see the unmapped node

Most folds only need the children's results. When the decision at a
node depends on the node's own *structure*, not just what its children
folded to, you need access to the original node. `fold_with_original`
passes both: the algebra receives a reference to the original node
alongside the mapped node whose children have been replaced by
results.

A cost model is the standard use. Binary operations cost more than
unary ones, which cost more than leaves, and the cost of each
subtree accumulates.

```rust
let cost = s.fold_with_original(
    root,
    |_orig: &StmtNode, mapped: StmtNodeMapped<usize, usize>| { /* ... */ },
    |orig: &ExprNode, mapped: ExprNodeMapped<usize, usize>| {
        let own = match orig {
            ExprNode::Add(..) | ExprNode::Mul(..) | ExprNode::Eq(..) => 2,
            ExprNode::Neg(..) => 1,
            _ => 0,
        };
        let child_cost = /* sum child costs from mapped */ 0;
        child_cost + own
    },
);
```

The `orig` reference tells the algebra which variant it is looking at
before the mapping erased the IDs; the `mapped` value provides the
already-folded child costs to sum up.

## 12. `unfold` and `unfold_short`: build a tree from a seed

A fold consumes a tree. An unfold produces one, top-down from a seed
value. The *coalgebra* takes a seed and returns a node layer: a node
shape plus one child *seed* for each hole in the node. The library
recurses on each child seed, expanding until a coalgebra returns a
layer with no seeds (a leaf).

A generator for balanced expression trees:

```rust
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
```

The child IDs in the returned node (`ExprId(0)` above) are
placeholders. The library replaces them with the real IDs once each
child has been unfolded and pushed. This placeholder step is
unavoidable because the parent has to describe its shape before its
children exist.

`unfold_short` adds one capability: the coalgebra can return `Done(id)`
to reuse an existing node instead of continuing to expand. This is how
you share a precomputed subtree into a generated structure without
building two copies of it.

## 13. `prefold` and `postunfold`: normalize along the way

A fold is most useful when its input is in a known shape. `prefold`
takes a per-sort rewrite (`Node → Node`) and applies it to every node
before the algebra sees it. Use it for strength reduction
("multiplication by 1 is just the operand"), for desugaring before
evaluation, or for any transform you want to treat as part of the
fold's input rather than as a separate pass.

```rust
let result = s.prefold(
    root,
    |stmt| stmt,
    |expr| match expr {
        ExprNode::Mul(l, r) => ExprNode::Add(l, r),
        other => other,
    },
    alg_stmt,
    alg_expr,
);
```

The example rewrites every `Mul` to an `Add` before the fold sees it,
so the fold only needs to handle `Add`.

`postunfold` is the dual on the construction side. It runs a per-sort
rewrite on each layer the coalgebra produces, after the children have
been resolved but before the node is pushed. Use it for
canonicalization: sort commutative operands so that a downstream dedup
recognizes `Add(1, 2)` and `Add(2, 1)` as the same node.

```rust
let root = s.postunfold(
    LangStoreSeed::Expr(3u32),
    |stmt| stmt,
    |expr| match expr {
        ExprNode::Add(a, b) if a.0 > b.0 => ExprNode::Add(b, a),
        other => other,
    },
    |seed| { /* coalgebra */ },
);
```

## 14. Variadic children

Fixed-arity nodes like `Add(Expr, Expr)` work well for most AST shapes,
but some constructs have a variable number of children. A function call
`f(a, b, c, ...)` takes any number of arguments; a function type
`(T1, T2, ...) -> T` takes any number of parameter types; a block `{ s1;
s2; ...; sn }` contains any number of statements. Declaring these as
fixed arity would force you to nest them artificially (a right-leaning
chain of `Cons` cells, say), and folding them then forces every algebra
to reassemble the list.

`Variadic<Sort>` in a variant declares a variable-length list of
children of that sort.

```rust
rec_family! {
    family Lang2 => Lang2Store;

    enum Stmt {
        Block(Variadic<Stmt>),
        Call(String, Variadic<Expr>),
    }

    enum Expr {
        Lit(i64),
        Var(String),
        FnType(Variadic<Expr>, Expr),
    }
}
```

The store gains one allocation helper per pair of `(owning_sort,
child_sort)`. For the family above it would be
`alloc_stmt_stmt(&[StmtId])` (for `Block`'s child list),
`alloc_stmt_expr(&[ExprId])` (for `Call`'s arguments), and
`alloc_expr_expr(&[ExprId])` (for `FnType`'s parameters). Each helper
copies the slice into an internal pool and returns a `Variadic<SortId>`
value that you embed in the node:

```rust
let x = s.push_expr(ExprNode::Lit(1));
let y = s.push_expr(ExprNode::Lit(2));
let z = s.push_expr(ExprNode::Lit(3));
let args = s.alloc_stmt_expr(&[x, y, z]);
let call = s.push_stmt(StmtNode::Call("f".into(), args));
```

Storage is pool-backed to avoid heap allocations for small lists. Under
the hood, a `Variadic` value is either a pair `(start, len)` pointing
into a per-(owning-sort, child-sort) pool, or a short inline list for
lists built during a traversal. The user never sees this distinction;
all operations go through the typed helpers.

### Variadic children in algebras

Inside a fold, a variadic child list appears as `Variadic<A>` where `A`
is the child sort's result type. Iterate with `.iter()`:

```rust
let result = s.fold(
    root,
    |stmt: StmtNodeMapped<String, String>| match stmt {
        StmtNodeMapped::Block(body) => {
            let parts: Vec<&str> = body.iter().map(String::as_str).collect();
            format!("{{ {} }}", parts.join("; "))
        }
        StmtNodeMapped::Call(name, args) => {
            let parts: Vec<&str> = args.iter().map(String::as_str).collect();
            format!("{}({})", name, parts.join(", "))
        }
    },
    |expr: ExprNodeMapped<String, String>| match expr {
        ExprNodeMapped::FnType(params, ret) => {
            let ps: Vec<&str> = params.iter().map(String::as_str).collect();
            format!("({}) -> {}", ps.join(", "), ret)
        }
        ExprNodeMapped::Lit(n) => n.to_string(),
        ExprNodeMapped::Var(n) => n,
    },
);
```

`.iter()` returns an iterator of `&A`; `.len()` gives the length;
`IntoIterator` is implemented so you can consume a `Variadic<A>`
directly if you own it. The length is inherent to the list, so
algebras do not need a separate "arity" parameter.

### Constraints

Variadic children have the same typed-ID discipline as fixed-arity
children. A `Variadic<Expr>` slot cannot be filled with `StmtId`s. The
allocator helper's name encodes both sorts, and passing a slice of the
wrong typed-ID produces a compile error.

A single variant can mix data, fixed-arity children, and variadic
children in any order. `Call(String, Variadic<Expr>)` puts the name
first and the arguments second; the generated
`StmtNodeMapped::Call(String, Variadic<A_expr>)` preserves that
ordering.

Variadic children participate in hash-consing normally. A deduplicating
store compares variadic child lists by value, so
`Call("f", [a, b])` deduplicates with another `Call("f", [a, b])` that
happens to use the same argument IDs.

## 15. Hash-consing with `new_dedup`

A plain store appends every pushed node, even if it is structurally
identical to an existing one. `LangStore::new_dedup()` adds a per-sort
hashmap: a push first checks whether the same node already exists, and
if so returns the existing ID.

```rust
let mut s = LangStore::new_dedup();
let a = s.push_expr(ExprNode::Lit(42));
let b = s.push_expr(ExprNode::Lit(42));
assert_eq!(a, b);
assert_eq!(s.len_expr(), 1);
```

Dedup operates per sort: pushing an `Expr` does not consult the `Stmt`
table. It also interacts correctly with `mark` and `restore`; on
restore, dedup entries pointing at truncated nodes are pruned, so a
later push of an identical node starts fresh rather than returning a
stale ID.

Dedup trades construction time for memory. See
[`doc/design/memo-and-dedup.md`](doc/design/memo-and-dedup.md) for
numbers and guidance.

## 16. Memoization strategies

`fold` uses dense memoization by default: a vector sized to the number
of nodes in the store, indexed by node ID. Two alternatives are
available via `with_strategy`.

```rust
use semi_persistent_traversals::{Sparse, memo};

let r = s.with_strategy::<Sparse>().fold(root, alg_stmt, alg_expr);
let r = s.with_strategy::<memo::None>().fold(root, alg_stmt, alg_expr);
```

`Sparse` uses a hashmap, so allocation is proportional to the nodes
actually visited rather than the full store. Good for folding a small
region of a large store; worse than dense when the fold visits almost
everything. `memo::None` skips dedup checks entirely and assumes the
input is a pure tree. It is faster than dense on trees but produces
wrong results on DAGs. The design doc covers the tradeoffs.

## 17. Zippers: cursor-based navigation

Schemes like `fold` and `rewrite` are good at doing the same thing
everywhere. When you need to navigate to a specific location in the
tree, check its siblings or ancestors, and possibly patch it in place,
a zipper is the right tool. A zipper is a cursor with focus plus a
stack of breadcrumbs for the path back to the root.

The crate ships three zipper flavors.

`LangStoreZipper` is read-only. Move the focus down into a child with
`down(i)`, back up with `up()`, to a sibling with `down` after `up`.
Read the current node via `focus()`.

```rust
let mut z = LangStoreZipper::new(&s, root);
z.down(1);
z.down(1);
z.up();
match z.focus() {
    LangStoreRoot::Expr(id) => { /* ... */ }
    _ => panic!(),
}
```

`LangStoreZipperMut` allows in-place mutation. `set_focus_expr(node)`
overwrites the current node; every reference to that ID elsewhere in
the store sees the change. Only usable on stores built without dedup,
since mutating a hash-consed node would desynchronize the dedup table
from the arena.

```rust
let mut z = LangStoreZipperMut::new(&mut s, root);
z.down(0);
z.set_focus_expr(ExprNode::Lit(42));
```

`LangStoreZipperCow` produces a new store containing the updated
version of the tree, leaving the original untouched. Internally it
rebuilds the spine from the focus up to the root and reuses everything
else, so the cost is proportional to the tree size rather than the
full store.

```rust
let z = LangStoreZipperCow::new(&s, root);
let (new_store, new_root) = z.set_focus_expr(ExprNode::Lit(3));
```

## 18. The full chapter list

[`tests/testorial.rs`](tests/testorial.rs) contains one chapter per
scheme applied to a realistic piece of a compiler pipeline. Each
chapter is a standalone `#[test]`.

| Ch | Scheme | Example |
|----|--------|---------|
|  1 | `fold` | pretty printer and size |
|  2 | `rewrite` | constant folding |
|  3 | `rewrite` | double negation elimination |
|  4 | `fold_short` | find a variable |
|  5 | `unfold` | generate an AST |
|  6 | `unfold_short` | build with node reuse |
|  8 | `rewrite` | desugar while loops |
|  9 | `fold` | type inference |
| 10 | `fold` | interpreter |
| 11 | `fold` | free variables |
| 12 | `fold` | precedence-aware pretty printer |
| 13 | `fold_with_history` | depth complexity |
| 14 | `fold_with_aux` | type check then evaluate |
| 15 | `fold_pair` | saturating eval |
| 16 | `prefold` | simplify then eval |
| 17 | `postunfold` | canonicalize during build |
| 19 | `rewrite_down` | top-down desugar |
| 20 | `fold_with_original` | cost model |
| 21 | `fold_short` | dead code search |
| 22 | `prefold` | desugar then eval, multi-sorted |
| 23 | `fold` | compile to bytecode |
| 24 | `Zipper` | find a binder via siblings |
| 25 | `ZipperMut` | walk up and patch |
| 26 | `ZipperCow` | specialize a shared subtree |
