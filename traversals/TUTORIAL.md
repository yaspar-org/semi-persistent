# Tutorial: recursion schemes with `rec_family!`

This tutorial walks through the `semi-persistent-traversals` crate by
building a small compiler pipeline. The numbered scheme examples are
executable tests in [`tests/testorial.rs`](tests/testorial.rs). Variadic
storage and traversal behavior is covered separately by
[`tests/variadic_pool.rs`](tests/variadic_pool.rs), while focused contract
tests cover marks, cycles, unfolds, and compile-time restrictions.

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
struct StmtId(pub usize);
struct ExprId(pub usize);

// One enum per sort, stored in the arena. Cross-sort fields became typed IDs.
enum StmtNode {
    Let(String, ExprId),
    Seq(StmtId, StmtId),
    Print(ExprId),
    If(ExprId, StmtId, StmtId),
    While(ExprId, StmtId),
    Noop,
}

enum ExprNode {
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
enum StmtNodeMapped<A_stmt, A_expr> {
    Let(String, A_expr),
    Seq(A_stmt, A_stmt),
    Print(A_expr),
    If(A_expr, A_stmt, A_stmt),
    While(A_expr, A_stmt),
    Noop,
}

enum ExprNodeMapped<A_stmt, A_expr> {
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
enum LangStoreRoot {
    Stmt(StmtId),
    Expr(ExprId),
}

enum LangStoreFoldResult<A_stmt, A_expr> {
    Stmt(A_stmt),
    Expr(A_expr),
}

// The store owns one arena per sort and provides all scheme methods.
struct LangStore<const DEDUP: bool = false> { /* ... */ }

impl LangStore<false> {
    fn new() -> Self { /* ... */ }
}

impl LangStore<true> {
    fn new_dedup() -> Self { /* ... */ }
}

impl<const DEDUP: bool> LangStore<DEDUP> {
    fn push_stmt(&mut self, node: StmtNode) -> StmtId { /* ... */ }
    fn push_expr(&mut self, node: ExprNode) -> ExprId { /* ... */ }
    fn get_stmt(&self, id: StmtId) -> &StmtNode { /* ... */ }
    fn get_expr(&self, id: ExprId) -> &ExprNode { /* ... */ }
    fn len_stmt(&self) -> usize { /* ... */ }
    fn len_expr(&self) -> usize { /* ... */ }

    fn mark(&self) -> LangStoreMark { /* ... */ }
    fn restore(&mut self, mark: &LangStoreMark) { /* ... */ }

    fn fold<A_stmt: Clone, A_expr: Clone>(
        &self,
        root: LangStoreRoot,
        alg_stmt: impl Fn(StmtNodeMapped<A_stmt, A_expr>) -> A_stmt,
        alg_expr: impl Fn(ExprNodeMapped<A_stmt, A_expr>) -> A_expr,
    ) -> LangStoreFoldResult<A_stmt, A_expr> { /* ... */ }

    // Fold and transform methods use callbacks grouped by sort. unfold and
    // unfold_short instead take one sort-tagged coalgebra; postunfold adds
    // per-sort postprocessors before that coalgebra.
}
```

The declaration used plain `family`, so these generated items and
methods are module-private. Write `pub family Lang => LangStore;` when
the generated API should be public; the visibility before `family` is
applied consistently to the generated types and methods.

The `DEDUP` const parameter records whether structural hash-consing is
enabled. It defaults to `false`; `new()` constructs `LangStore<false>`
and `new_dedup()` constructs `LangStore<true>`. Section 15 covers the
behavioral and API differences.

A few observations about this expansion.

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

Both mapped enums in this example take the same pair of generic
parameters `<A_stmt, A_expr>` because both sorts reference both child
sorts. The parameter set is computed per mapped enum, then ordered by
the family's sort declaration order. For example,
`ExprNode::Block(Stmt, Expr)` makes `ExprNodeMapped` generic over both
results. If `Expr` referenced only `Expr` children, its mapped enum
would be `ExprNodeMapped<A_expr>` even if another sort referenced
`Stmt`.

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
label; it names the declaration but does not prefix generated Rust
types. The `=>` separator is followed by `LangStore`, the store type you
instantiate with `LangStore::new()` or `LangStore::new_dedup()`.
`LangStore` prefixes the generated companion types, including
`LangStoreSeed`, `LangStoreLayer`, `LangStoreApoSeed`,
`LangStoreApoLayer`, `LangStoreRoot`, `LangStoreFoldResult`,
`LangStoreMark`, and the zipper types. Both names are arbitrary; pick
something descriptive for your domain.

### Declaring sorts and their variants

Each `enum` block under the header declares one sort. Two rules govern
them:

1. Within each per-sort callback group, callbacks follow declaration
   order. Because `enum Stmt` appears before `enum Expr`, the `Stmt`
   algebra comes first in `fold(..., alg_stmt, alg_expr)`.
   `fold_with_aux` groups all aux callbacks before all main callbacks;
   `fold_pair` groups the A and B callbacks for each sort. Declaration
   order also fixes the relative order of the child-sort parameters
   present on each mapped enum and the variant order of
   `LangStoreFoldResult`.

2. A variant's fields are classified by matching their types against
   the sort names. Any type that is not a sort name (`String`, `i64`,
   `bool`, or a user type implementing `Clone + Debug + Eq + Hash`)
   becomes a data field stored inline in the node. Bare `f32` and `f64`
   fields are also supported, using bitwise equality and hashing so
   NaNs are reflexive and signed zero remains distinct. Any type that
   matches a sort name becomes a typed child ID. A third form,
   `Variadic<Sort>`, declares a variable-length list of children of that
   sort, covered in §14 below.

## 2. Build an AST

With the family declared, you build ASTs by pushing nodes into the
store. The typed IDs make it impossible to put a `Stmt` where an `Expr`
is expected. The arenas represent trees and acyclic term DAGs: insert
children before parents. `push_*` rejects missing or forward child IDs,
and mutable `set_*` operations reject replacements that would create a
cycle. This keeps recursion schemes terminating without adding cycle
detection to every traversal.

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
variant name converted to snake case, with a trailing underscore when
the result would collide with a Rust keyword or generated store method
(`let_`, `if_`, `mark_`, `fold_`). Standard method names are reserved
the same way (`clone_`, `clone_from_`, `drop_`). The sample builder
becomes:

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
`&[SortId]`, so you write `s.call("f", &[a, b, c])` instead of
`s.alloc_stmt_expr(&[a, b, c])` followed by a `push_stmt`. A plain-store
insertion or dedup miss copies the slice into the corresponding typed
pool; a dedup hit returns before allocating a new span.

Two limitations. First, the macro generates one method per variant
across all sorts in the family, so any two variants that would share a
method name (both lowercase to `add`, for example) produce a targeted
macro error. Rename one of the colliding variants, or drop
`#[smart_constructors]` and write the helpers you want by hand.

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

The parameter set is per sort, while the order is family-wide. The
`Expr` algebra sees `<A_stmt, A_expr>` in that order because `Block`
contains both child sorts. A mapped enum that references only `Expr`
would take only `<A_expr>`.

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
Every rule must return an ID whose numeric index exists in the
corresponding output arena. `rewrite` checks that bound after each rule
call and rejects an out-of-range ID. IDs are typed by sort but are not
branded by store, so a valid numeric index always denotes the node at
that position in the output store.

## 6. `rewrite_down`: top-down transform

A bottom-up rewrite sees children before the parent. A top-down rewrite
sees the parent first, rewrites it, and then visits the (possibly new)
children. This ordering is what you want when the rewrite creates new
children that themselves need rewriting.

A small example uses an existing, initially unreachable `Neg(5)` node as
the expansion of `Var("x")`. The rule then rewrites that newly introduced
child from `Neg(5)` to `Mul(5, 5)`:

```rust
let five = s.push_expr(ExprNode::Lit(5));
let neg_five = s.push_expr(ExprNode::Neg(five));
let root = LangStoreRoot::Expr(
    s.push_expr(ExprNode::Var("x".into()))
);

let (s2, r2) = s.rewrite_down(
    root,
    |stmt| stmt,
    |expr| match expr {
        ExprNode::Var(name) if name == "x" => ExprNode::Neg(neg_five),
        ExprNode::Neg(inner) => ExprNode::Mul(inner, inner),
        other => other,
    },
);
```

The root becomes `Neg(Neg(5))`. `rewrite_down` then follows the child
introduced by the root rule and rewrites it, producing
`Neg(Mul(5, 5))`, which evaluates to -25. A bottom-up rewrite only visits
the original root-reachable children before invoking a parent rule, so it
cannot automatically traverse a source node first introduced by that
parent rule. Rules are applied once per visited source node; the newly
produced parent constructor itself is not repeatedly rewritten.

The rewritten graph must remain acyclic. A rule may point to existing
source IDs, but if that introduces a back-edge to a node whose output
mapping is still under construction, `rewrite_down` rejects the cycle.

## 7. `fold_short`: postorder early exit

A fold normally visits every reachable node. Sometimes you want to
stop once an algebra reports a result. `fold_short` gives each algebra
an early-exit hatch: the return type is `Result<A, A>`, where `Ok(v)`
continues the fold with result `v` and `Err(v)` ends it immediately.
Evaluation is postorder, so all children of a node are evaluated before
that node's algebra runs. A parent-level `Err` can stop later work, but
cannot prune that parent's already visited children.

Here is a dead-code detector that exits when postorder evaluation
reaches an `If(false, _, _)`:

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

## 8. `fold_with_history`: inspect one generation of shape

A plain fold gives each algebra only the direct children's results. If
the decision at a node depends on what the grandchildren look like,
you need a scheme that carries more context through the recursion.
`fold_with_history` provides limited shape metadata: each algebra
receives `Ann<A>` instead of `A`, where `Ann` bundles a child's result
with that child's own children's raw arena indices. This exposes one
generation of grandchild arity without a second traversal. The indices
are untyped across sorts and do not expose recursive annotations or
the fold's memo tables; this operation is not a full histomorphism.

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
the untyped arena indices of the grandchildren, which lets the algebra
detect "this child is itself an operation, not a leaf".

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

Most folds only need the children's results. The mapped enum still
preserves the variant and non-child data, so matching on `Add` versus
`Neg` alone does not require a different scheme. Use
`fold_with_original` when the algebra also needs the original child IDs
or, for variadic nodes, the resolved original child list. It passes a
reference to that original node alongside the mapped node whose
children have been replaced by results.

This cost model uses the original IDs to discount a binary operation
whose two edges share one child node, information that is no longer
present when both children fold to equal numeric costs:

```rust
let cost = s.fold_with_original(
    root,
    |_orig: &StmtNode, mapped: StmtNodeMapped<usize, usize>| { /* ... */ },
    |orig: &ExprNode, mapped: ExprNodeMapped<usize, usize>| {
        let own = match orig {
            ExprNode::Add(l, r) | ExprNode::Mul(l, r) | ExprNode::Eq(l, r)
                if l == r => 1,
            ExprNode::Add(..) | ExprNode::Mul(..) | ExprNode::Eq(..) => 2,
            ExprNode::Neg(..) => 1,
            _ => 0,
        };
        let child_cost = /* sum child costs from mapped */ 0;
        child_cost + own
    },
);
```

The `orig` reference exposes whether the two child IDs are identical;
the `mapped` value provides the already-folded child costs to sum up.

## 12. `unfold` and `unfold_short`: build a tree from a seed

A fold consumes a tree. An unfold produces one, top-down from a seed
value. The *coalgebra* takes a seed and returns a node layer: a node
shape plus one child *seed* for each hole in the node. The library
recurses on each child seed, expanding until a coalgebra returns a
layer with no seeds (a leaf). The number of seeds must exactly equal the
number of fixed and variadic child positions in the returned node;
`unfold`, `unfold_short`, and `postunfold` reject mismatched layers.
The seed and layer enums are sort-tagged, so `unfold` and
`unfold_short` each take one coalgebra for the whole family; the
coalgebra matches on `LangStoreSeed::Stmt` versus
`LangStoreSeed::Expr`.

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

`unfold_short` changes the seed attached to each child hole. A child can
be `Continue(LangStoreSeed::...)`, which the coalgebra expands, or a
sort-specific `DoneStmt(id)` / `DoneExpr(id)`, which reuses an existing
node without expansion. This is how you share a precomputed subtree
into a generated structure without building another copy. The initial
root is always a `LangStoreSeed` and is expanded by the coalgebra.

## 13. `prefold` and `postunfold`: normalize along the way

A fold is most useful when its input is in a known shape. `prefold` is
the convenience composition of a bottom-up `Node → Node` rewrite into a
fresh store followed by a fold of that store. Use it for operator-local
normalization or desugaring before evaluation. It is not a fused
traversal and its callback does not receive the output store; use
`rewrite` directly when a rule must inspect rewritten children or
collapse a node to one child.

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

`postunfold` is the dual on the construction side. Its arguments are
one postprocessor per sort, in declaration order, followed by the same
sort-tagged coalgebra used by `unfold`. It runs the matching
postprocessor on each layer after the children have been resolved but
before the node is pushed. Use it for canonicalization: sort
commutative operands so that a downstream dedup recognizes `Add(1, 2)`
and `Add(2, 1)` as the same node.

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

Storage is pool-backed to avoid a separate heap allocation for every
list. Allocators and smart constructors produce a `(start, len)` span
into a per-(owning-sort, child-sort) pool. `Variadic<SortId>` is this
storage/input representation. It provides length queries, but not
pool-free iteration, indexing, mapping, consuming iteration, equality,
or hashing. Those operations cannot be structural without the pool.

Generated traversals resolve spans through the owning store and use a
short inline `ResolvedVariadic<A>` for mapped children passed to
algebras. Rewrite, transform, and original-node callbacks for a sort
with variadic fields receive `<Sort>NodeResolved`; its variadic fields
are also `ResolvedVariadic<SortId>`. These resolved values have ordinary
slice semantics and cannot contain a span.

### Variadic children in algebras

Inside a fold, a variadic child list appears as
`ResolvedVariadic<A>` where `A` is the child sort's result type. Iterate
with `.iter()`:

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
`IntoIterator` is implemented so you can consume a mapped
`ResolvedVariadic<A>` directly if you own it. Indexing, `map_all`, and
`into_vec` are total as well. The owning store resolves pooled spans
before invoking an algebra, so algebras do not need a pool or a separate
"arity" parameter.

Raw nodes returned by `get_<sort>` retain their pool spans. Use
`get_<sort>_resolved(id)` to obtain a `<Sort>NodeResolved` when
inspecting a node directly, or `map_<sort>_children(id, ...)` to map its
children with the owning store's pools. Resolved nodes are accepted by
`push_<sort>` and, on non-deduplicating stores, `set_<sort>`.
Context-free `Node::map_children` is available only for sorts with no
variadic fields.

### Constraints

Variadic children have the same typed-ID discipline as fixed-arity
children. A `Variadic<Expr>` slot cannot be filled with `StmtId`s. The
allocator helper's name encodes both sorts, and passing a slice of the
wrong typed-ID produces a compile error. Spans also carry their pool
identity; inserting a span into a different owning sort or store is
rejected instead of resolving the same offsets against unrelated data.

A single variant can mix data, fixed-arity children, and variadic
children in any order. `Call(String, Variadic<Expr>)` puts the name
first and the arguments second; the generated
`StmtNodeMapped::Call(String, ResolvedVariadic<A_expr>)` preserves that
ordering. `StmtNodeResolved::Call(String,
ResolvedVariadic<ExprId>)` is the corresponding direct-inspection and
rewrite-callback type.

Variadic children participate in hash-consing normally. A deduplicating
store compares variadic child lists by value, so
`Call("f", [a, b])` deduplicates with another `Call("f", [a, b])` that
uses the same argument IDs even if the two lists occupy different pool
spans or one node was built from an inline `Variadic::Resolved` value.
Smart constructors perform this lookup against the borrowed input
slice before allocating a span, so a hit does not grow the pool and a
miss copies the children into the pool exactly once. Calling `alloc_*`
explicitly remains an eager allocation; `push_*` cannot reclaim that
span if it subsequently finds a duplicate node.

## 15. Hash-consing with `new_dedup`

A plain store appends every pushed node, even if it is structurally
identical to an existing one. `LangStore::new_dedup()` adds a per-sort
semantic hash table: a push first checks whether the same node already
exists, and if so returns the existing ID. Hash collisions are checked
with structural equality, including value-based comparison of variadic
children.

```rust
let mut s = LangStore::new_dedup();
let a = s.push_expr(ExprNode::Lit(42));
let b = s.push_expr(ExprNode::Lit(42));
assert_eq!(a, b);
assert_eq!(s.len_expr(), 1);
```

Dedup mode is tracked in the type. `LangStore::new()` returns
`LangStore<false>` and `LangStore::new_dedup()` returns `LangStore<true>`.
Methods that perform in-place mutation, `set_stmt`, `set_expr`, and
`LangStoreZipperMut::new`, are only defined on `LangStore<false>`, so
calling them on a deduplicating store is a compile error rather than a
silent corruption of the dedup map. The `const DEDUP: bool` parameter is
elided by monomorphization: at runtime the `if DEDUP` branches in
`push_*` and `restore` become unconditional code or dead code depending
on which store you built. Both modes retain the same fixed-size
`Option<HashMap<...>>` fields; a plain store keeps them at `None`, so
they do not allocate or grow.

Dedup operates per sort: pushing an `Expr` does not consult the `Stmt`
table. A mark is a store-bound append checkpoint, not a copy of the
nodes. `restore` truncates every arena and variadic pool and prunes
dedup entries pointing at the discarded suffix, so a later push of an
identical node starts fresh rather than returning a stale ID. Foreign
marks, marks ahead of the current store, and marks made before a
successful in-place mutation are rejected.

Dedup trades construction time for memory. See
[`doc/design/memo-and-dedup.md`](doc/design/memo-and-dedup.md) for
numbers and guidance.

## 16. Memoization strategies

`fold` uses dense memoization by default: a vector sized to the number
of nodes in the store, indexed by node ID. Two alternatives are
available via `with_strategy`.

```rust
use semi_persistent_traversals::memo;

let r = s.with_strategy::<memo::Map>().fold(root, alg_stmt, alg_expr);
let r = s.with_strategy::<memo::None>().fold(root, alg_stmt, alg_expr);
```

`memo::Map` (alias `Sparse`) uses a hashmap, so allocation is proportional to the nodes
actually visited rather than the full store. Good for folding a small
region of a large store; worse than dense when the fold visits almost
everything. `memo::None` skips memo-reuse checks, but still uses dense
result storage to assemble parent values. On a tree it evaluates each
node once; on a DAG it evaluates a shared node once per reachable
occurrence. A pure deterministic algebra therefore computes the same
root value as folding the fully unfolded tree, but work and algebra side
effects repeat. The design doc covers the tradeoffs.

## 17. Zippers: cursor-based navigation

Schemes like `fold` and `rewrite` are good at doing the same thing
everywhere. When you need to navigate to a specific location in the
tree, check its siblings or ancestors, and possibly patch it in place,
a zipper is the right tool. A zipper is a cursor with focus plus a
stack of breadcrumbs for the path back to the root.

The crate ships three zipper flavors.

`LangStoreZipper` is read-only. Move the focus down into a child with
`down(i)`, back up with `up()`, or directly to a sibling with
`sibling(i)`. Read the current node via `focus()`. Navigation methods
return `false` when the requested move does not exist and leave the
focus and breadcrumb path unchanged on failure.

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
the store sees the change. The constructor takes `&mut LangStore<false>`,
so passing a deduplicating store is a compile error. Mutation on a
dedup'd store would leave the hashmap pointing at a stale node, and
the type restriction prevents that at compile time.

```rust
let mut z = LangStoreZipperMut::new(&mut s, root);
z.down(0);
z.set_focus_expr(ExprNode::Lit(42));
```

`LangStoreZipperCow` produces a new store containing the updated
version of the root-reachable DAG, leaving the original untouched. It
copies each reachable node once into a fresh store and omits
unreachable source nodes, so output construction is `O(V + E)` over the
reachable DAG. The default dense strategy also initializes mapping and
visit tables for every source node. For a small reachable region of a
large store, call `set_focus_<sort>_with_strategy::<Sparse>(...)` to keep
auxiliary state proportional to the reachable region. Stores do not
share backing storage.

The focus identifies a node ID, not one path occurrence. If that ID is
shared, replacement affects every reachable reference to it in the new
store. A replacement that would introduce a cycle is rejected.

```rust
let z = LangStoreZipperCow::new(&s, root);
let (new_store, new_root) = z.set_focus_expr(ExprNode::Lit(3));
```

The new store inherits the dedup mode of the source: calling
`set_focus_*` on a `ZipperCow` wrapping a `LangStore<true>` produces a
`LangStore<true>` with the reachable graph re-interned.

## 18. The full chapter list

[`tests/testorial.rs`](tests/testorial.rs) contains 24 numbered,
standalone `#[test]` examples for the principal schemes used in this
guide. Additional tests cover `fold_all`, `fold_with_ids`, `transform`,
memo strategies, deduplication, variadics, and contract failures.

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
