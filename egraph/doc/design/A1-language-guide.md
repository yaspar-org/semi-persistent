# Language Guide

[← Overview: Why Semi-Persistent](A0-overview.md) · [Table of Contents](00-table-of-contents.md) · [Developer Guide →](A2-developer-guide.md)


This chapter describes the engine's surface language: how to declare
sorts and operators, write rewrite rules, and drive equality
saturation. It then walks through the compilation pipeline that
transforms source text into executable commands.

The engine reuses the egglog surface syntax (S-expression commands for
sort/function/datatype declarations, rewrite rules, let bindings,
union, check, extract, push/pop, and run) and extends it with:

- Algebraic attributes (`:assoc-comm`, `:assoc-comm-idem`, etc.) on
  operator declarations for native A/C/AC/ACI support.
- Rest variables (`..rest`) in patterns for subsequence, sub-multiset,
  and subset matching on variadic operators.
- Comprehension expressions and splicing (`..{body for x in rest}`,
  `..[body for x in rest]`) for processing rest variables in rule
  actions.
- Namespaced builtin operator names (`IBig::+`, `i64::<<`, `RBig::neg`)
  to disambiguate when multiple numeric types are in scope.
- Predicate guards (`:when ((i64::< a b))`): a primitive computation over
  bound literal values, evaluated at match time rather than matched.

## Sorts and Operators

Every term in the engine has a sort. Sorts are declared explicitly:

```
(sort Expr)
```

Concrete sorts (IBig, RBig, bool, String) are registered
automatically by the literal model and cannot be declared by the
user.

Operators map argument sorts to a return sort:

```
(function Num (IBig) Expr)
(function Add (Expr Expr) Expr)
(function Mul (Expr Expr) Expr)
```

`(constructor …)` declares the same operator as `(function …)` (same
congruence, same matching) and additionally marks it a term former,
which is the declaration extraction tags belong on:

```
(constructor Num (IBig) Expr)
(constructor Add (Expr Expr) Expr :cost 3)  ;; costs 3 per node when extracting
(function    Tmp (Expr) Expr :unextractable) ;; never selected by (extract …)
```

`:cost n` defaults to 1, which is the unweighted node-count model, so a
program that declares no cost extracts exactly as before. See Chapter 16
for the cost model.

The `datatype` command is sugar for a sort declaration plus one
constructor per variant:

```
(datatype Expr
  (Num IBig)
  (Add Expr Expr)
  (Mul Expr Expr)
  (Neg Expr)
  (Zero))
```

### Algebraic Attributes

Operators can be declared with algebraic properties that change how
they are stored and matched:

```
(function Or  (Expr) Expr :assoc-comm-idem) ;; ACI: set semantics
(function Add (Expr) Expr :assoc-comm)      ;; AC:  multiset semantics
(function Seq (Expr) Expr :assoc)           ;; A:   sequence semantics
(function Eq  (Expr Expr) Expr :comm)       ;; C:   commutative binary
```

Variadic operators (A, AC, ACI) take a single argument sort in their
declaration (the element sort, which must equal the return sort) but
accept any number of children at use sites. The e-graph stores them
as variable-length nodes internally. Attributes can also appear on
individual datatype variants:

```
(datatype Expr
  (Num IBig)
  (Add Expr Expr :assoc-comm)
  (Or  Expr Expr :assoc-comm-idem))
```

## Ground Terms and Let Bindings

Ground terms (no variables) are used in `let`, `union`, `check`,
and `extract` commands:

```
(let a (Add (Num 3) (Num 4))) ;; bind name 'a' to a term
(let b (Mul (Num 2) (Num 5)))
(union a b)                   ;; assert a = b
(check (= a b))               ;; verify a and b are equal
(check (!= a (Num 0)))        ;; verify a ≠ 0
(extract a)                   ;; print cheapest term in a's class
```

Checks compare canonical forms under plain congruence. The completion pass can
derive additional AC-entailed equalities that flattening erases (see the AC
completion docs), in one of two opt-in modes:
`--derive-ac-eqs` runs it eagerly on every rebuild, and
`--lazy-ac-eqs` runs it only inside a failing check, in a
mark/complete/restore transaction. Consecutive equality checks share that
temporary transaction; it is restored before the next non-equality command or
at the end of the checked program, so its derived nodes and merges do not
persist in the program state.
Under lazy mode, `(check (!= ...))` passes only when the implemented bounded
completion/rule search reaches its operational fixpoint without deriving the
equality. That is the command's operational criterion, not a proved statement
of semantic non-equality in the abstract AC theory. The two flags are mutually exclusive;
`ac-congruence-completeness.md` §13 has the trade-offs.

A bare S-expression at the top level is an insertion; there is no
separate insert command:

```
;; inserts the term into the e-graph
(Add (Num 1) (Num 2))
```

### Globals in Patterns

Let-bound names can appear in LHS patterns and RHS terms. When the
resolver encounters a name that is already bound in `GlobalCtx`, it
emits a `PatVar::Global` reference instead of creating a fresh
pattern variable. The semantics: a global in a pattern position means
"the child at this position must be in the same e-class as the
global identifier's current binding."

```
(datatype Expr (V i64) (Add Expr Expr) (Dbl Expr))
(let a (V 1))

;; 'a' in the LHS is not a fresh variable — it refers to the
;; e-class of (V 1). This rule fires only on Add nodes whose
;; first child is equivalent to a.
(rewrite (Add a x) (Dbl x))
```

Globals in RHS terms work similarly: `FetchGlobal` reads the
current canonical representative from the binding array.

```
;; 'a' in the RHS inserts the current e-class of a as a child
(rewrite (Add x y) (Pair a x))
```

Globals can also appear in `:when` guards, where they compile to a comparison
of the local and global classes under the index build's representative map:

```
(let zero (V 0))
(rewrite (Add x y) (Mul x y) :when ((= x zero)))
```

`(= x zero)` is the root-binding form below, with a global on one side.

The scheduler treats global children as always-bound, which is a
significant selectivity advantage: a `ByChildPos` index lookup
constrained to a specific global narrows the join to only nodes
that have that e-class as a child. The interpreter canonicalizes
global bindings through the immutable index snapshot when matching; it does
not rewrite the `GlobalCtx` binding array each iteration. RHS evaluation uses
the live e-graph representative.

## Rewrite Rules

A rewrite rule has a LHS pattern and a RHS term. When the LHS
matches, the matched term is unioned with the RHS:

```
(rewrite (Add (Num 0) x) x)       ;; additive identity
(rewrite (Mul (Num 0) x) (Num 0)) ;; zero annihilation
(rewrite (Neg (Neg x)) x)         ;; double negation
```

Variables in patterns are bare identifiers: any name not registered
as an operator is treated as a pattern variable.

### Root Binding: `(= v pat)`

A pattern position may name the e-class it matches:

```
;; z is the class of the whole (Add x y); the action refers to it twice
(rule ((= z (Add x y))) ((union (Mark z) z)))
```

Both sides of `=` are patterns, and the form constrains their roots to one
e-class. Repeating the bound name across conjuncts is what states that two
patterns share a root, rather than being a cross product over two independent
matches:

```
;; fires only when (ncols A) and (nrows C) are the SAME class
(rewrite (MMul (Kron a b) (Kron c d))
         (Kron (MMul a c) (MMul b d))
  :when ((= p (ncols a)) (= p (nrows c))
         (= q (ncols b)) (= q (nrows d))))
```

The bound name is an ordinary pattern variable: it can be reused in child
positions, appear in the right-hand side, and take its sort from the pattern it
names. `=` is reserved for this form, so an operator declared `=` does not
shadow it.

### Conditional Rewrites

The `:when` clause adds guard patterns that must also match:

```
(rewrite (Mul x y) (Mul y x)
  :when ((Add x z)))  ;; only if x appears in some Add
```

### Predicate Guards

A `:when` conjunct headed by a primitive operator is a predicate, not a pattern.
It is evaluated over the literal values the patterns bound, and the match
survives when it computes `true`:

```
;; only fold when the exponent is small
(rewrite (Pow x (Num n)) (Mul x (Pow x (Num (i64::- n 1))))
  :when ((i64::< n 8)))
```

Guards compose, and a constant written in a guard is parsed at the argument
position's sort:

```
;; 3y = 12 becomes y = 4, and only when the division is exact
(rule ((= r (Mul (Num x) y)) (= r (Num z)) (i64::== (i64::% z x) 0))
      ((union y (Num (i64::/ z x)))))
```

Four rules govern them:

- A guard is a top-level conjunct of a `:when` list or a `rule` body. A
  primitive may not appear as a subterm of a pattern, because it names a
  function on values and not a relation the e-graph stores.
- Every operator inside a guard is a primitive, and the whole guard computes a
  `bool`.
- A guard reads variables that some pattern binds in a primitive-sorted
  argument position, and only patterns written before it. `(P (Num a) (Num b))`
  binds `a` and `b`; `(P a b)` binds e-classes, which a primitive cannot
  compute over.
- A guard computes and discards. It never interns the value it computed; a rule
  that wants the value in the e-graph computes it again on the right-hand side.

The guard runs as early as its variables allow, immediately after the last of
them is bound, so a false guard cuts the search before the remaining patterns
are joined.

### Subsumption

The `:subsume` flag marks the matched LHS node as subsumed after
the rewrite fires, removing it from future matching:

```
(rewrite (Add (Num a) (Num b)) (Num (IBig::+ a b)) :subsume)
```

### Multi-Pattern Rules

Rules with multiple LHS patterns and multiple RHS actions express
Datalog-style reasoning:

```
(rule ((Add x y) (Mul x z))
      ((union y z)))
```

The LHS is a conjunction of patterns. All must match simultaneously
(with shared variables). The RHS is a list of actions (union, insert).

## Variadic Pattern Matching

The operator's registered kind determines how patterns are
interpreted. The parser produces a uniform `(Op children...)` syntax;
dispatch happens at resolve time based on the operator's `OpKind`.

### Non-Linear Variables

A variable that appears more than once in a pattern is non-linear.
The first occurrence binds; subsequent occurrences check equality
(same e-class). This works uniformly across all operator kinds:

```
(rewrite (Add x x) (Dbl x)) ;; matches Add nodes where both children
                            ;; are in the same e-class
```

### ACI Patterns (set semantics)

ACI nodes store sorted sets (duplicates removed). Pattern elements
must each match a distinct child. The accepted forms are:

- Exact: `(Or x (A) y)`. The node must contain exactly these elements
  (order irrelevant). Variables bind to distinct children.
- Subset + rest: `(Or x (A) ..rest)`. The node must contain at least
  these elements; remaining children go into `rest` as a set.
- Rest only: `(Or ..rest)`. Matches any Or node, binding all
  children.

```
(sort E)
(function Or (E) E :assoc-comm-idem)
(function A () E)
(function B () E)
(function C () E)
(function F (E) E)
```

Example: `(Or x (A) ..rest)` against `(Or (A) (B) (C))`:

```
match 1: x = B,  rest = {C}
match 2: x = C,  rest = {B}
```

Two matches because `x` can bind to any non-A child. The concrete
element `(A)` is consumed first, then `x` iterates over the
remaining distinct children.

Example: `(Or x y)` (exact, no rest) against `(Or (A) (B))`:

```
match 1: x = A, y = B
match 2: x = B, y = A
```

Both orderings match because ACI is unordered. Against
`(Or (A) (B) (C))`: no match (3 children, 2 pattern elements).

Example: `(Or x (F x) ..rest)` (non-linear) against
`(Or (A) (F (A)) (B))`:

```
match: x = A, rest = {B}
```

The non-linear `x` requires `(F x)` to be in the same set. Only
`x = A` satisfies this because `(F (A))` is present.

### AC Patterns (multiset semantics)

AC nodes store sorted multisets (elements with multiplicities).
Matching is a partition of the node's distinct children: every pattern
element binds a distinct child and takes that child's *whole*
multiplicity, which must satisfy the element's annotation. A bare
variable `x` (and a bare concrete element like `(Zero)`) implicitly
means `:1`: it only binds a child whose total multiplicity is exactly
one. Children not bound by any element go to the rest variable, again
with their whole multiplicity. Chapter 9 (Pattern Matching Execution)
is the normative statement of these semantics. The accepted forms are:

- Exact: `(Add x (Zero) y)`. Total multiplicities must match
  exactly.
- Sub-multiset + rest: `(Add x (Zero) ..rest)`. Consume the listed
  elements; remaining multiplicities go into `rest`.
- Rest only: `(Add ..rest)`. Matches any Add node.
- With multiplicity: `(Add x:k ..rest)`. Bind `x` to a child and
  `k` to its total multiplicity.

```
(sort E)
(function Add (E) E :assoc-comm)
(function Zero () E)
(function A () E)
(function B () E)
(function F (E) E)
```

Example: `(Add x (Zero) ..rest)` against `(Add (Zero) (A) (A) (B))`:

```
match: x = B, rest = {A:2}
```

The concrete `(Zero)` binds the Zero child (total multiplicity 1).
`x` cannot bind A: A's total multiplicity is 2 and a bare variable
requires exactly 1. To also catch A, write `x:k` and read the
multiplicity from `k`.

Example: `(Add x:k y:j ..rest)` against `(Add (A) (A) (A) (B) (B))`:

```
match 1: x = A, k = 3, y = B, j = 2, rest = {}
match 2: x = B, j = 2, y = A, k = 3, rest = {}
```

Each variable consumes the full multiplicity of its matched child
(maximal partition semantics). The rest gets whatever is left.

Example: `(Add x:k>=2 ..rest)` against `(Add (A) (A) (A) (B))`:

```
match: x = A, k = 3, rest = {B:1}
```

Only A qualifies (multiplicity 3 ≥ 2). B has multiplicity 1, which
fails the constraint.

Example: `(Add (Zero) ..rest)` against `(Add (Zero) (Zero) (A))`:

```
no match
```

The Zero child's total multiplicity is 2, and the bare concrete
element requires exactly 1. `(Add (Zero):2 ..rest)` matches with
`rest = {A:1}`, and `(Add (Zero):k ..rest)` matches any multiplicity,
binding `k = 2`.

Multiplicity constraint summary:

| Syntax | Meaning |
|--------|---------|
| `x` | implicit `:1` (child's total multiplicity is exactly 1) |
| `x:3` | child's total multiplicity is exactly 3 |
| `x:k` | bind k to the child's total multiplicity (k ≥ 1) |
| `x:k>=2` | bind k, require k ≥ 2 |
| `x:k<5` | bind k, require k < 5 |

A bound multiplicity variable is readable on the right-hand side
wherever an `i64` is expected: as a primitive argument
(`(Const (i64::* a k))`) and in a literal position (`(Const k)`).

RHS elements of a variadic operator also take a multiplicity, either
a literal or a checked u64 expression over bound multiplicities
(`u64::+ u64::- u64::* u64::/ u64::% u64::min u64::max`):

```
(rewrite (Mul (Add b ..s):k ..rest)
         (Add (Mul b (Add b ..s):(u64::- k 1) ..rest)
              (Mul (Add ..s) (Add b ..s):(u64::- k 1) ..rest)))
```

A multiplicity of 0 omits the element without evaluating it, so at
`k = 1` this rule is ordinary distributivity and at `k >= 2` it keeps
`k-1` copies of the repeated factor. The expression is interval-checked
at rule install against the LHS constraints: with a bare `:k` the
multiplicity is only known to be at least 1, so `(u64::- k 2)` is
rejected until the element is annotated `:k>=2`. Division and remainder
need a divisor provably nonzero; overflow stays a runtime trap, checked
like the literal primitives.

Non-linear multiplicity variables (same `:k` on multiple elements)
must bind to the same value:

```
;; x and y must appear the same number of times
(rewrite (Add x:k y:k ..rest) (Balanced x y))
```

### Caveat: migrating binary rules to AC patterns

Partition semantics (chapter 9): the elements plus the rest variable
partition the node's distinct children, and no two elements may bind
the same child. A binary pattern has no such constraint, because its
two positions are independent. So a rule that was written against a
binary operator can silently lose its repeated-child matches when the
operator becomes AC and the rule is restated in n-ary form.

Concretely, the binary rule

```
(rewrite (Mul x (Add a b)) (Add (Mul x a) (Mul x b)))
```

matches `(Mul t t)` with `t = (Add a b)`, binding `x = t`. After
flattening, that node is the multiset `Mul{t:2}`, one distinct child
at multiplicity 2, and the n-ary restatement

```
(rewrite (Mul x (Add a b) ..rest) ...)
```

does not match it: `x` and `(Add a b)` are two elements and there is
only one distinct child. To cover the repeated child, write the
multiplicity variant explicitly:

```
(rewrite (Mul (Add a b):k>=2 ..rest) ...)
```

The same applies to a *single* element facing a repeated child: an
element takes its child's whole multiplicity, and unannotated it
requires exactly 1, so `(rewrite (Add (Const 0) ..rest) (Add ..rest))`
does not fire on `Add{0:2, x}`. Its multiplicity variant
`(rewrite (Add (Const 0):k>=2 ..rest) (Add ..rest))` drops all copies
at once. Where the right-hand side needs the count, read it as an
i64: a constant fold's multiplicity variant is

```
(rewrite (Add (Const a):k>=2 ..rest) (Add (Const (i64::* a k)) ..rest))
(rewrite (Mul (Const a):k>=2 ..rest) (Mul (Const (i64::pow a k)) ..rest))
```

This is deliberate. Partition semantics is what makes AC matching
well defined and enumerable; generating the variants
automatically is a combinatorial blowup (every subset of mutually
unifiable elements could coincide). When you translate a binary rule
whose element subpatterns can unify with each other, or whose element
can face a repeated child, decide per rule whether the repeated-child
case matters and write its multiplicity variant if it does. The keep-`k-1`-copies
shape (distributing one factor out of `(x+y)^k · z`) is written with
an RHS multiplicity expression, `(Add b ..s):(u64::- k 1)`; see the
multiplicity section above.

### A Patterns (sequence semantics)

A nodes store ordered sequences. Pattern elements match positionally
against a contiguous subsequence. The accepted forms are:

- Exact: `(Seq x (A) y)`. Children must be exactly these elements in
  this order.
- Suffix match: `(Seq x (A) ..rest)`. Fixed elements at the start;
  rest captures the tail.
- Prefix match: `(Seq ..pre (A) x)`. Rest captures the head; fixed
  elements at the end.
- Prefix + suffix: `(Seq ..pre x ..suf)`. Fixed elements in the
  middle; rest variables capture both ends.
- Rest only: `(Seq ..rest)`. Matches any Seq node.

```
(sort E)
(function Seq (E) E :assoc)
(function A () E)
(function B () E)
(function C () E)
(function F (E) E)
```

Example: `(Seq x (A) ..rest)` against `(Seq (B) (A) (C) (C))`:

```
match: x = B, rest = [C, C]
```

`x` binds to position 0, `(A)` must be at position 1, rest gets
positions 2 onward.

Example: `(Seq ..pre x (A))` against `(Seq (B) (C) (A))`:

```
match: pre = [B], x = C
```

`(A)` must be at the end, `x` binds to the element just before it,
`pre` gets everything before `x`.

Example: `(Seq ..pre x ..suf)` against `(Seq (A) (B) (C))`:

```
match 1: pre = [],     x = A, suf = [B, C]
match 2: pre = [A],    x = B, suf = [C]
match 3: pre = [A, B], x = C, suf = []
```

Three matches because `x` can slide to any position. Each split
produces different pre/suf bindings.

Example: `(Seq ..pre (A) x ..suf)` against `(Seq (B) (A) (C) (A) (D))`:

```
match 1: pre = [B],       x = C, suf = [A, D]
match 2: pre = [B, A, C], x = D, suf = []
```

Two matches because `(A)` appears at positions 1 and 3. For each,
`x` binds to the element immediately after `(A)`.

Only A operators support two rest variables (prefix + suffix). AC
and ACI are unordered, so prefix/suffix is meaningless.

### Comprehensions (RHS)

Comprehension splices construct variadic RHS terms from matched
rest variables:

```
;; map F over each element of a set
(rewrite (Or ..rest) (Or ..{(F x) for x in rest}))

;; retain multiset elements whose count exceeds an LHS-bound threshold
(rewrite (Box (N limit) (Add marker:1 ..rest))
         (Add ..{x:k for x:k in rest if (i64::< limit k)}))
```

Set comprehensions use `..{...}`, sequence comprehensions use
`..[...]`. A filter must compute a concrete literal value, such as the result
of a Rust literal-model primitive. It is not an e-graph query: an ordinary
application such as `(Positive x)` is rejected. Bind graph conditions on the
LHS with a rewrite guard or a general-rule conjunct.

## Push/Pop Scoping

`(push)` snapshots the entire e-graph state (nodes, classes,
union-find, caches, rules, globals). `(pop)` restores to the most
recent snapshot:

```
(push)
  (union a b)
  (run 10)
  (check (= a b))
(pop)
;; a and b are no longer equal
```

`(push :shrink)` reclaims excess capacity before snapshotting. This
is useful after a large search branch when the next branch will be
much smaller. Plain `(push)` lets capacity ratchet to the high-water
mark, which is better for tight loops with similar-sized branches.

## Saturation

`(run N)` executes up to N iterations of equality saturation:

```
(run 10)    ;; up to 10 iterations
```

Each iteration: rebuild (propagate merges, re-canonicalize) → build
indexes → schedule each rule → match via leapfrog join → apply
actions. If no new facts are derived, saturation stops early.

### Rulesets

A run fires one ruleset. Untagged rules are in the default ruleset,
which is what `(run N)` runs; `:ruleset name` puts a rule in a declared
ruleset, which only `(run name N)` runs:

```
(ruleset expensive)
(rewrite (Add x y) (Add y x))                  ;; default ruleset
(rewrite (Mul (Add x y) z)
         (Add (Mul x z) (Mul y z)) :ruleset expensive)

(run 10)            ;; commutativity only
(run expensive 2)   ;; distribution only
```

Ruleset declarations and their numeric ids are resolved statically across the
whole program before interpretation. Installed rules are scoped: `(push)`
records the current rule-vector length, and `(pop)` removes rules installed
after that push. Once a ruleset has been declared at an earlier source
position, later commands can still resolve its name across `push`/`pop`; a rule
added to it inside a pushed scope does not survive the matching pop.

### Run Goals

`:until` stops a run as soon as a goal over two ground terms holds,
which is how a search reports time-to-goal rather than time-to-budget:

```
(run 1000 :until (= lhs rhs))
(run fast 50 :until (!= a b))
```

The goal is checked after rebuild and before every iteration, including the
first, so a goal that already holds costs no iterations. Its terms are built
once, before the run: the same nodes a `(check …)` of the goal would add.

## Statistics

```
(print-size)                      ;; node count per operator, then the total
(print-size Add)                  ;; one operator's node count
(print-stats)                     ;; last run's counters, on stdout
(print-stats :file "stats.json")  ;; the same numbers, as JSON
```

`print-stats` reports nodes, classes, iterations, match steps, wall
time, whether the run saturated, and whether its `:until` goal was met.
Match-step counting is normally off. The presence of a `print-stats` command
arms it before that checked command batch executes; the CLI
`--count-match-steps` option can also arm it. The counter is an implementation
step count, not a time estimate.

## Compilation Pipeline

Source text passes through three phases before execution:

```
source text ──→ Parse ──→ Sortcheck ──→ Interpret
                  │           │             │
           SurfaceCommand  CCommand    execute against
           (spans, strings) (OpId,     live e-graph
                            SortId,
                            dense ids)
```

### Phase 1: Parse

The parser produces a source-mapped AST with no registry access.
All applications use the uniform `(Op children...)` shape. Operator
kinds are unknown at this stage. Rest variables (`..name`) are parsed
structurally into prefix/suffix positions. Literals are raw string
tokens.

### Phase 2: Sortcheck

Sortcheck processes commands sequentially against a live e-graph.
Declaration commands (`sort`, `function`, `datatype`) register sorts
and operators into the registries. For rewrite and rule commands,
LHS patterns go through two sub-steps:

`flatten_surface` walks the pattern tree, assigns fresh synthetic
variables to nested applications, and produces a flat list of atoms.
Each atom is classified by operator kind (Plain, C, A/APrefix/ASuffix/
ABoth, ACExact/ACSub, ACIExact/ACISub). Invalid combinations (e.g.,
prefix rest on an AC operator, multiplicity on an ACI operator)
produce clear error messages. Two forms are recognized by name first:
`(= p q)`, which flattens both sides and emits one `Eq` between their
roots, and a top-level primitive application, which becomes a
predicate-guard atom.

`resolve` maps string variable names to dense typed identifiers
(VarId, SeqVarId, SetVarId, MsetVarId, MultVarId, LitValVarId).
It infers sorts from operator signatures and produces a
`ResolvedQuery` containing typed atoms and a `MatchShape` describing
the variable allocation.

Ground terms are sort-checked bottom-up: each operator's argument
sorts are verified against the registry, and the result is a `CTerm`
with resolved OpIds and SortIds.

Literals in ordinary commands are classified by the `LitModel` (e.g., `"42"`
becomes `IBig(42)`) but are not interned merely by checking those commands.
This is the deferred-interning invariant for terms and patterns, not a claim
that the whole sortcheck pass is pure: declarations mutate the live
registries, and an algebraic `:identity` declaration builds and stores its
ground unit node during registration.

### Phase 3: Interpret

The interpreter executes `CCommand` values against the live e-graph.
Operator, sort, rule-set, and pattern-variable references are dense ids.
Global ground terms still carry their names and perform a `GlobalCtx` lookup,
and AU option spellings are validated here. Declaration commands are no-ops
(already registered during sortcheck). Ground
terms are built bottom-up, interning literals on first use. Rewrite
and rule commands are stored as compiled rules. `(run N)` triggers
the saturation loop.

### Dynamic Scheduling

Sortcheck first flattens each nested pattern into a conjunction of
relational atoms with stable atom ids. Atom order is then a scheduling
choice, not a top-down walk of the source pattern.

In the default `Static` mode, each matching round builds a plan from
the current index snapshot. The planner alternates between two phases:

1. The eager phase lowers every unused atom that needs no fresh
   unbound-node scan, including enabled equalities, predicate guards,
   literal checks or extractions, and atoms whose node variable is already bound.
   It repeats to a fixpoint because one lowered atom can enable another.
   A bound node denotes an e-class representative, so an atom requiring
   a particular operator may emit a class-local re-join:
   `ByRepr(bound_class) ∩ ByOp(required_op)`.
2. The cost phase chooses one remaining relational atom. Its base cost
   is the cardinality of that atom's active full, delta, or
   full-minus-delta driver slice. Bound keys scale that cost using the
   measured fan-out of the relevant `ByRepr`, `ByChildPos`, or
   `ByContains` access path. Optional deterministic sampling can refine
   a cross-index estimate. After lowering the chosen atom, planning
   returns to the eager phase.

`--runtime-scheduling` performs the same eager/lower cycle at each
per-binding decision point. Its cost phase reads the shortest concrete
cursor that each candidate join would open for the current bindings,
so sibling partial bindings may choose different atom orders.
`--auto-scheduling` selects static or runtime ordering per rule and
round from measured index skew. Runtime scheduling stores used atoms
and bound node variables in two `u64` masks; a query with more than 64
atoms or more than 64 node variables uses its static plan. These modes
change execution order, not the resolved atom set or the per-atom
semi-naive index mode.

## Annex: Full Grammar

```ebnf
(* ═══════════════════════════════════════════════════════════════════
   Surface Language — Unified EBNF
   ═══════════════════════════════════════════════════════════════════ *)

(* ── Lexical ── *)

letter      = 'A'..'Z' | 'a'..'z' | '_' ;
digit       = '0'..'9' ;
ident       = letter , { letter | digit } ;
symbol      = '<<' | '>>' | '<=' | '>=' | '!=' | '==' | '=>'
            | '+' | '-' | '*' | '/' | '%' | '<' | '>' | '&' | '|' | '^' | '~' ;
qualified   = ident , '::' , ( ident | symbol ) ;       (* e.g. IBig::+, RBig::neg *)
op          = qualified | ident | symbol ;
prim_op     = op ;                (* one of the literal model's primitives *)
comment     = ';' , { char - '\n' } , '\n' ;

(* ── Literals ── *)

uint_lit    = digit , { digit } ;
int_lit     = [ '-' ] , uint_lit ;
rat_lit     = int_lit , '/' , digit , { digit } ;
float_lit   = [ '-' ] , digit , { digit } , '.' , { digit } ,
              [ ( 'e' | 'E' ) , [ '+' | '-' ] , digit , { digit } ] ;
bool_lit    = 'true' | 'false' ;
string_lit  = '"' , { char - '"' | '\\"' | '\\\\' | '\\n' | '\\t' } , '"' ;
literal     = rat_lit | float_lit | int_lit | bool_lit | string_lit ;

(* ── Ground terms ── *)

term        = literal
            | ident
            | '(' , op , term* , ')' ;

(* ── Patterns (LHS) ── *)
(* Dispatch by operator kind at resolve time, not parse time. *)

pattern     = literal
            | ident
            | '(' , '=' , pattern , pattern , ')'         (* root binding *)
            | '(' , prim_op , pattern* , ')'              (* predicate guard,
                                                             top-level only *)
            | '(' , op , pat_child* , ')' ;

pat_child   = '..' , ident                               (* rest variable *)
            | pattern , ':' , mult_spec                   (* element + multiplicity *)
            | pattern ;

mult_spec   = int_lit                                     (* exact: x:2 *)
            | ident                                       (* bind: x:k *)
            | ident , cmp_op , int_lit ;                  (* constrained: x:k>=2 *)

cmp_op      = '>=' | '<=' | '==' | '!=' | '>' | '<' ;

(* ── RHS terms ── *)

rhs         = literal
            | ident
            | '(' , op , rhs_child* , ')' ;

rhs_child   = '..' , splice
            | rhs ;

splice      = ident                                       (* plain: ..rest *)
            | '{' , rhs , comp_tail , '}'                 (* set comprehension *)
            | '{' , rhs , ':' , mult_expr ,
                    mcomp_tail , '}'                       (* multiset comprehension *)
            | '[' , rhs , comp_tail , ']' ;               (* sequence comprehension *)

comp_tail   = 'for' , ident , 'in' , ident , filter? ;
mcomp_tail  = 'for' , ident , ':' , ident , 'in' , ident , filter? ;
mult_expr   = uint_lit
            | ident
            | '(' , mult_op , mult_expr , mult_expr , ')' ;
mult_op     = 'u64::+' | 'u64::-' | 'u64::*' | 'u64::/'
            | 'u64::%' | 'u64::min' | 'u64::max' ;
filter      = 'if' , rhs ;

(* ── Commands ── *)

program     = command* ;

command     = '(' , 'sort' , ident , ')'
            | '(' , 'function' , op , '(' , ident* , ')' , ident , decl_tag* , ')'
            | '(' , 'constructor' , op , '(' , ident* , ')' , ident , decl_tag* , ')'
            | '(' , 'datatype' , ident , variant* , ')'
            | '(' , 'ruleset' , ident , ')'
            | '(' , 'rewrite' , pattern , rhs , rewrite_tag* , ')'
            | '(' , 'birewrite' , pattern , pattern , birewrite_tag* , ')'
            | '(' , 'rule' , '(' , pattern* , ')' , '(' , action* , ')' ,
                    ruleset_tag* , ')'
            | '(' , 'let' , ident , term , ')'
            | '(' , 'union' , term , term , ')'
            | '(' , 'run' , ident? , int_lit , until? , ')'
            | '(' , 'check' , check_body , ')'
            | '(' , 'extract' , term , ')'
            | '(' , 'print-size' , op? , ')'
            | '(' , 'print-stats' , ( ':file' , string_lit )? , ')'
            | '(' , 'antiunify' , term , term , au_option* , ')'
            | '(' , 'checkau' , term , term , checkau_option* , ')'
            | '(' , 'push' , ':shrink'? , ')'
            | '(' , 'pop' , ')'
            | '(' , op , term* , ')' ;                    (* sugar: ground term insertion *)

variant     = '(' , ident , ident* , decl_tag* , ')' ;

decl_tag    = alg_attr | extract_tag ;

alg_attr    = ':assoc-comm-idem' | ':assoc-comm' | ':assoc-left'
            | ':assoc-right' | ':assoc' | ':comm' | ':idempotent'
            | ':nilpotent' , int_lit? | ':identity' , term
            | ':cancellative' | ':inverse' , ident ;

extract_tag = ':cost' , int_lit | ':unextractable' ;

rewrite_tag = when_clause | subsume | ruleset_tag ;
birewrite_tag = when_clause | ruleset_tag ;
when_clause = ':when' , '(' , pattern* , ')' ;
subsume     = ':subsume' ;                                (* not on birewrite *)
ruleset_tag = ':ruleset' , ident ;

until       = ':until' , '(' , ( '=' | '!=' ) , term , term , ')' ;

au_option   = ':playouts' , int_lit
            | ':algorithm' , ( 'exact' | 'uct' )
            | ':cycles' , ( 'sides' | 'sides-current' | 'pair' ) ;

checkau_option = au_option | ':max_size' , int_lit ;

check_body  = '(' , '='  , term , term , ')'
            | '(' , '!=' , term , term , ')'
            | term ;

action      = '(' , 'union' , rhs , rhs , ')'
            | '(' , 'set' , '(' , ident , rhs* , ')' , rhs , ')'
            | '(' , op , rhs_child* , ')' ;
```

---
[← Overview: Why Semi-Persistent](A0-overview.md) · [Table of Contents](00-table-of-contents.md) · [Developer Guide →](A2-developer-guide.md)
