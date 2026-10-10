# Chapter 7 — Rules and Pattern Matching

[← Ch 6: AC Congruence Closure](06-ac-congruence-closure.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Indexes and Leapfrog →](08-indexes-and-leapfrog.md)

## 7.1 Surface Language and Parser

### Design Philosophy

The engine uses a unified S-expression syntax for all constructs. The key
design decision: the surface syntax does not distinguish operator
kinds. All operator applications use `(op children...)` regardless
of whether the operator is plain, commutative, associative, AC, or
ACI. The operator's registered kind is resolved during sortcheck
(§7.2), not during parsing.

As a result, the parser is simple and context-free. It does not need
access to the operator registry. Kind-specific validation (e.g.,
"operator 'f' is plain; rest variables not allowed") happens in
the sortcheck phase, where registry metadata is available. These errors name
the invalid form, but precise source spans are not universal: some top-level
flatten/resolve errors are currently wrapped with `Span::Dummy`.

Rest variables use `..name` prefix syntax. Multiplicity annotations
use `:k` suffix syntax. Brackets survive only in RHS comprehensions
(`{...}` for set/multiset, `[...]` for sequence).

### LHS Patterns: `SurfacePattern`

```rust
enum SurfacePattern {
    Var(String, Span),
    Lit(String, Span),
    App {
        op: String,
        prefix: Option<(String, Span)>,   // ..pre
        children: Vec<SurfacePatChild>,
        suffix: Option<(String, Span)>,   // ..suf
        span: Span,
    },
}

enum SurfacePatChild {
    Elem(SurfacePattern),
    ElemMult(SurfacePattern, MultSpec),
    Seq(String, Span),                      // ..name between children (sequence rules)
    Filter { name, mult, base, except, span }, // (..name[:k] base [:except other])
}
```

`Lit` handles literal constants in patterns (e.g., `42`, `true`).
Literals follow a distinct code path from `Var`: they are resolved to
concrete `@`-prefixed ops during sortcheck, while variables become
pattern bindings.

Rest variables are structurally first/last only. The parser extracts
them into `prefix`/`suffix` fields. A lone `(op ..rest)` places
`rest` in `suffix`.

### RHS Terms: `RhsTerm`

```rust
enum RhsChild {
    Term(RhsTerm),
    TermMult { term, mult, span },                     // term:mult
    Splice(String, Span),                              // ..rest
    SetComp { body, var, source, filter, span },       // ..{body for v in src}
    MsetComp { body, mult, var, mult_var, source, filter, span },
    SeqComp { body, var, source, filter, span },       // ..[body for v in src]
    RowComp { body, mult, binders, source, filter, ordered, span }, // for (x y) in (prim …)
}
```

Comprehension syntax uses real `{}`/`[]` delimiters.

### Ground Terms: `Term`

```rust
enum Term {
    Lit(String, Span),
    App { op: String, children: Vec<Term>, span: Span },
    Counted { term: Box<Term>, count: BigUint, span: Span }, // child:count
}
```

A counted child is written `x:k`, with no space before the count. In a ground term the
count is a `BigUint` of any size, checked against the configured width when the term is
built; sortcheck accepts it only under an A or AC operator and refuses a count of 0
(§7.7, "Occurrences and empty applications"). A count in a rule is read as a `u64`
(`count_number`), and one past 2^64 − 1 is a parse error that names the multiplicity.

### Commands

```
(sort Name)
(function Name (ArgSort...) RetSort [algebra-tags] [extraction-tags])
(constructor Name (ArgSort...) RetSort [algebra-tags] [extraction-tags])
(datatype Name (Ctor ArgSort... [algebra-tags] [extraction-tags])...)
(let name term)
(union term term)
(op term...)  ; a bare top-level term inserts it
(ruleset name)
(rewrite lhs rhs [:when (guard...)] [:subsume] [:flatten] [:ruleset name])
(birewrite lhs rhs [:when (guard...)] [:flatten] [:ruleset name])
(rule (pattern... guard...) (action...) [:flatten] [:ruleset name])
(run [ruleset] N [:until (= a b) | :until (!= a b)])
(push) (push :shrink) (pop)
(check term) (check (= a b)) (check (!= a b))
(extract term)
(cost-model name :script "f.roto" | :rust "id" | :asp "f.lp" | :minizinc "f.mzn")
(extract term :cost name [:rung selection|levels|splits|binary|orders] [:budget N]
              [:solver internal|dpw|roundingsat|greedy|(opb|asp|minizinc "cmd" "arg"...)]
              [:file "path"] [:proof "dir"] [:band lo hi :count n])
(dump-egraph term :file "path")
(antiunify left right [:playouts N] [:algorithm exact|uct]
                     [:cycles sides|sides-current|pair])
(checkau left right [:max_size N] [:playouts N] [:algorithm exact|uct]
                    [:cycles sides|sides-current|pair])
(print-size) (print-size Op)
(print-stats) (print-stats :file "path.json")
```

A `rewrite` whose left-hand side is a sequence pattern also takes `:let ((name expr)...)`,
evaluated after the match and before the guards; an ordinary rewrite does not. The left-hand
side of a rewrite may be a sequence pattern over an A, AC, or ACI root:
filters `(..name[:k] pattern [:except other])`, bare sequences `..name` (several
under A, at most one under AC or ACI), and simple items beside them; its right-hand
side may use comprehensions `..{ body for g in gs }`, `..{ body for (x y) in
(prim …) }`, and `..[ … ]` under A, reductions (`count`, `min`, `max`, `sum`),
element-wise primitives, and the sequence primitives `zip`, `union-by`, `narrow`,
`narrowed`, and `concat`. §7.6 gives the typing and the semantics; the parser
is `parser.rs` (`parse_filter`, `parse_seq_tags_rhs`, and the comprehension forms).

There is no `(insert term)` command. In a rule head, an application without
the `union` or `set` keyword is an insert action; at the top level, the bare
application itself is the insertion form.

The command language exposes `exact` and `uct` as algorithms. Expansion-time
and rollout-time Exact delegation are separate `AuConfig` library flags
(`hybrid_exact` and `rollout_hybrid`); they are not additional
`:algorithm` spellings in the interpreter.

algebra-tags: `:comm` `:assoc` `:assoc-left` `:assoc-right` `:idempotent`
`:nilpotent [n]` `:identity term` `:cancellative` `:inverse Op`, plus the
pre-combined aliases `:assoc-comm` and `:assoc-comm-idem`.

extraction-tags: `:cost n` (default 1) and `:unextractable`.

`(birewrite a b)` is sugar, expanded by the parser into the two rewrites
`a -> b` and `b -> a`; both sides parse as patterns, and each is read
back as the other direction's right-hand side. `pattern_as_rhs` rejects a `:mult`
annotation and a sequence pattern on a birewrite side, and
`:subsume` is rejected because subsuming the node the reverse direction
has to match would make the pair asymmetric.

Rulesets scope which rules a run fires: an untagged rule is in the
default ruleset that `(run N)` runs, and `:ruleset name` puts a rule in
the ruleset that `(run name N)` runs. See §9.1 for the run
semantics, the `:until` goal, and the statistics commands.

`:when` and `:subsume` are rewrite tags. A multi-pattern `(rule ...)` places
primitive guard conjuncts directly in its body; after the head, only
`:ruleset` and `:flatten` are accepted. The parser rejects `:when` or `:subsume` there rather
than silently ignoring either tag.

`:flatten` (decided 2026-09-30) makes a rule match every n-ary operator it uses
(`:assoc` and folds, AC, ACI) on the flattened form of a node: a child class that
holds a node of the parent's operator also contributes that node's children,
recursively, each such member or the class kept whole being one view. Nothing
stored changes; a rule without the tag matches as before. It is accepted on
`rewrite` (ordinary and sequence), `birewrite` (both directions carry it), and
`rule`, in any tag position; a second `:flatten` in one rule is a parse error. A
tagged rule whose pattern has no n-ary operator is installed with a warning that
the tag has no effect. The matching mode is `Step::Flatten` for ordinary rules
(§7.5, "Flattened Matching") and the view assembly of `Collect` for sequence
rules (§7.6). An operator that is only `:comm` has no flattened form, and the
tag leaves it as it is.

### Functions and Constructors

`(function …)` and `(constructor …)` parse to the same command and register the
same operator; the keyword sets one bit. A constructor is a term former: its
nodes carry `FLAG_CONSTRUCTOR`, and it is the declaration form that the
extraction tags are meant for. Every variant of a `(datatype …)` is a
constructor. Congruence, matching, and canonization treat the two identically:
unlike egglog, where `function` is a partial map with a mandatory merge lattice
and `constructor` is the eqsort term former.

The extraction tags are accepted on either form, because extraction is a
property of the operator rather than of the declaration keyword: `:cost n` sets
the per-node cost the extractor charges, and `:unextractable` removes the op's
nodes from the extractor's candidate set (§11.1).

## 7.2 Sortchecking and Resolution

### The Three-Phase Pipeline

The engine processes programs in three phases. Operator, sort, ruleset, and
pattern-variable references are resolved before interpretation, and the
interpreter performs no sort inference. This is not a claim that every source
name disappears: ground-term globals and AU option spellings are intentionally
late-bound, as detailed below.

```
source → parse (parser.rs) → Vec<SurfaceCommand>
       → sortcheck (sortcheck.rs) → Vec<CCommand<OpId, SortId, L>>
       → interpret (interpret.rs) → execute against EGraph
```

### `sortcheck_program`

Processes commands sequentially against a live EGraph. Declaration commands
register sorts and operators; an AC identity declaration also builds its
ground unit term at this point. Pattern commands are flattened and resolved.
Ordinary ground terms are classified and sort-checked without being built.

#### Algebraic Signature Invariants

Registration rejects algebraic signatures for which canonization would not be
well sorted:

- `A`, `AC`, and `ACI` operators are closed over one sort. Their sole argument
  sort equals their return sort because flattening nests results back into
  argument positions, and singleton canonization returns the child's e-class.
- A binary commutative operator has equal argument sorts because canonization
  may exchange the two positions. Its return sort may differ, as in a
  commutative equality operator `Eq : E x E -> Bool`.

The surface checker reports these as sort errors. `OpRegistry` asserts the same
invariants for direct Rust callers, making malformed algebraic metadata
unrepresentable downstream.

### `flatten_surface` — Op-Kind Validation

Walks `SurfacePattern` tree, assigns synthetic variable names to
nested `App` nodes, validates against operator kind:

| Op kind | prefix | suffix | ElemMult | Atom variant |
|---------|--------|--------|----------|-------------|
| Plain/C/Lit | ✗ | ✗ | ✗ | `Plain` |
| A, no rest | ✗ | ✗ | ✗ | `AExact` |
| A, prefix only | ✓ | ✗ | ✗ | `APrefix` |
| A, suffix only | ✗ | ✓ | ✗ | `ASuffix` |
| A, both | ✓ | ✓ | ✗ | `ABoth` |
| AC, no rest | ✗ | ✗ | opt | `ACExact` |
| AC, with rest | ✗ | ✓ | opt | `ACSub` |
| ACI, no rest | ✗ | ✗ | ✗ | `ACIExact` |
| ACI, with rest | ✗ | ✓ | ✗ | `ACISub` |

Invalid combinations produce diagnostic messages. Some retain a source span;
the top-level sortcheck pipeline currently maps several flatten/resolve errors
to `Span::Dummy`, so exact source locations are not guaranteed.

Two forms are recognized before the table, by the operator name.

**`(= p q)`, the root-binding form.** Both subpatterns flatten as they would
alone, and one `Atom::Eq` constrains their roots to one e-class. The name `=` is
reserved rather than looked up in the registry, so a declaration cannot shadow
the form and silently change what an existing `(= …)` means. The idiomatic use is
`(= v pat)`, which names `pat`'s root: the left side is a bare variable, so the
`Eq` costs one `CopyBinding` once `pat`'s root is bound. Repeating the name
across conjuncts is the ordinary non-linear case, and it is how a rule states
that two patterns share a root rather than forming a cross product.

**A primitive application, a predicate guard.** Legal only as a top-level
conjunct of a rule body or a `:when` list, because a guard is a constraint and
not a subterm. It flattens to `Atom::Pred`, carrying a `PredExpr` tree over
primitive operators, literal constants, and the variables other patterns bind to
literal payloads. Everywhere else in a left-hand side a primitive is still
rejected: it names a function on values, not a relation the e-graph stores.

### `resolve` — Name Resolution

Maps string variable names to dense typed ids:

| Variable kind | Dense id type | Storage in Match |
|--------------|---------------|-----------------|
| Node binding | `VarId` | `Match::nodes` |
| Global binding | `GlobalVarId` | `GlobalCtx::bindings` |
| A rest | `SeqVarId` | `Match::seq_pool` |
| ACI rest | `SetVarId` | `Match::set_pool` |
| AC rest | `MsetVarId` | `Match::mset_pool` |
| Multiplicity | `MultVarId` | `Match::mults` |
| Literal value | `LitValVarId` | `Match::lit_vals` |
| Literal sequence | `LitSeqVarId` | `Match::lit_seq_pool` |

`MatchShape` records the names of each variable kind in id order, serving as the single
source of truth for the binding environment layout.

Every occurrence of the same local variable name resolves to one `VarId`.
Whichever executable atom is selected first binds that slot. Later occurrences
are constrained by the operation appropriate to their atom: an index lookup,
`CheckChildEq`, or an A/AC/ACI decomposition check. `CheckEq` is specifically
the lowering of an explicit `Atom::Eq` whose two local slots are already
bound; if only one side is bound, the equality lowers to `CopyBinding`.

An `Eq` atom also unifies the two sides' sorts, since they denote one e-class.
That is what gives `(rewrite (= v pat) rhs)` a sort to check `rhs` against: `v`
alone constrains nothing, and takes its sort from `pat`.

#### Predicate Guards

`Atom::Pred` resolves to `RAtom::Pred`, which holds a `PredGuard`: the guard
expression with each primitive's `eval` and the model's `is_truthy` captured as
function pointers, plus `deps`, the indices of the `LitBind` atoms that bind the
values it reads. Three things are checked here:

- Every variable in the guard is already a literal-value variable. A guard may
  only read variables that some earlier pattern binds in a primitive-sorted
  argument position, so a guard written before its binder is rejected.
- Every operator in the guard is a primitive, and its arity matches.
- The guard computes a `bool`. Literal constants are parsed at the argument
  position's sort, so `0` in an `i64` position is an `i64`.

`deps` is filled once every atom is resolved, by `link_pred_deps`.

#### Whole-Query Checks

Two properties are not properties of a single atom, so they are checked once the
atom list is complete. Both reject queries the matcher cannot execute; both would
otherwise surface as a panic in `ematch` or, worse, as a silently dropped
constraint.

`check_rest_vars_linear` — **a rest variable has at most one writer.** `pre` and
`suf` of one variadic atom count as two, so `(S ..r x ..r)` is rejected along
with a rest shared between two atoms. Unlike a node variable, a repeated rest
name cannot lower to a check: `ExpandA`, `DecomposeAC` and `DecomposeACI` write
their spans unconditionally, and the `Step` enum has no span comparison, so the
second writer would overwrite the first and the constraint would vanish — which
admits matches the pattern excludes. Expressing the constraint instead of
rejecting it needs a new `Step`.

`check_nodes_bindable` — **every node variable of the `MatchShape` is bindable.**
`MatchPool::push` unwraps every node slot, so a plan that leaves one unbound
aborts when the first match is materialized. Every atom kind but `Eq` and `Pred`
binds its own node variable and its local children, so bindability is the closure
of those seeds under `Eq`, which copies a binding in whichever direction is
already bound. An `Eq` with neither side in the closure is lowered by neither
scheduler phase — `try_eager_lower` returns `None` and phase B's argmin skips
`Eq` — and is silently dropped; this is the local counterpart of the case
`Step::BindGlobal` handles for a global.

#### Global Name Resolution

When a child or variadic element name exists in `GlobalCtx`, the resolver emits
`PatVar::Global(gid)` instead of a fresh `VarId`. Such positions use the
`PatVar` enum:

```rust
pub enum PatVar {
    Local(VarId),
    Global(GlobalVarId),
}
```

A `PatVar::Global` child is considered bound for scheduling, so a pattern such
as `(Add a x)` can immediately use `a` in a `ByChildPos` lookup. An explicit
root equality such as `(= x a)`, where `a` is global, resolves instead to
`EqGlobal(x, gid)` and lowers to `BindGlobal` or `CheckEqGlobal` according to
whether `x` is already bound. In the RHS, a global becomes
`RhsOp::FetchGlobal(gid)`: apply reads the stored binding and canonicalizes a
standalone one with `eg.find`; as a direct child the binding is passed raw, because
`EGraph::add` canonicalizes its children. The binding array itself is not continuously rewritten to
canonical representatives.

#### RHS Collection Sorts

`ResolvedQuery` records the element sort of every `SeqVarId`, `SetVarId`, and
`MsetVarId`. Reusing one rest name at two different element sorts is rejected
while the query is resolved.

RHS resolution uses this metadata in two ways. A direct `..rest` splice must
have the destination operator's element sort. A comprehension binder has the
source collection's element sort, while its body has the destination
operator's element sort. The latter permits a typed map from one sort to
another, such as `..[(F x) for x in rest]` with `F : A -> B`, without treating
the source `x` as a `B`.

Splices, comprehensions, and multiplicity annotations are legal only as
children of variadic operators. Fixed-arity RHS applications must supply their
declared number of ordinary children. These checks keep malformed child arrays
from reaching `EGraph::add`, whose sort and arity assertions are debug-only
invariants rather than user-facing validation.

### `check_term` — Ground Term Sort-Checking

Walks `Term` bottom-up:
1. Look up op → `OpId`, get arg sorts and return sort.
2. Recursively check children → get child sorts.
3. Verify child sort matches declared arg sort.
4. Return `CTerm::App { op, sort, children }`.

For globals: look up in `GlobalCtx` → `CTerm::Global(name, sort)`.
For literals: classify via `LitModel::parse_as`/`parse_any` →
`CTerm::Lit(value, sort)`.

### `CCommand` / `CTerm`

```rust
pub enum CTerm<O, S, L> {
    Lit(L, S),
    App { op: O, sort: S, children: Vec<CTerm<O, S, L>> },
    Global(String, S),
    Counted(Box<CTerm<O, S, L>>, BigUint),
}

pub enum CCommand<O, S, L> {
    Decl(Command),
    Let(String, CTerm<O, S, L>),
    Insert(CTerm<O, S, L>),
    Union(CTerm<O, S, L>, CTerm<O, S, L>),
    Check(CTerm<O, S, L>),
    CheckEq(CTerm<O, S, L>, CTerm<O, S, L>),
    CheckNeq(CTerm<O, S, L>, CTerm<O, S, L>),
    Extract(CTerm<O, S, L>),
    ExtractWith { term, model: cost_models::Handle, rung: String, budget, solver,
                  file, proof, band },
    CollectionRule(Arc<collection::Rule<O, S, L>>),
    DumpEGraph { root: CTerm<O, S, L>, file: String },
    Rewrite {
        query: ResolvedQuery,
        rhs_locals: RhsLocalShape,
        rhs: RRhsTerm,
        root_vid: VarId,
        subsume: bool,
        ruleset: Option<RulesetId>,
        span: Span,
    },
    Rule {
        query: ResolvedQuery,
        rhs_locals: RhsLocalShape,
        actions: Vec<ResolvedAction>,
        ruleset: Option<RulesetId>,
        span: Span,
    },
    Run {
        ruleset: Option<RulesetId>,
        limit: u64,
        until: Option<CGoal<O, S, L>>,
    },
    PrintSize(Option<O>),
    PrintStats(Option<String>),
    AntiUnify { left: CTerm<O, S, L>, right: CTerm<O, S, L>, ... },
    CheckAu { left: CTerm<O, S, L>, right: CTerm<O, S, L>, ... },
    Push(bool),
    Pop,
}
```

After sortcheck, operator, sort, rule-set, and pattern-variable references are
dense ids and no sort inference remains. Two intentionally late-bound strings
remain: `CTerm::Global` stores the global name and `build_cterm` looks it up in
`GlobalCtx`; the AU commands also retain the algorithm and cycle-mode spellings
and validate them when interpreted. Declaration commands are already applied
to the live e-graph during sortcheck and are interpreter no-ops.

### `GlobalCtx`

```rust
pub struct GlobalCtx<S, G = ()> {
    index: HashMap<String, GlobalVarId>,
    sorts: Vec<S>,
    bindings: Vec<G>,
    shadows: Vec<(GlobalVarId, String, GlobalVarId)>, // restored by truncate
}
```

During sortcheck: `G = ()` (no runtime bindings, only sorts).
During interpretation: `G = Cfg::G` (actual e-class bindings).

`GlobalVarId` indices are assigned in command order. Since sortcheck
and the interpreter process commands in the same order, the indices
match between the two phases.

## 7.3 Query Compilation and Scheduling

### The Full Pipeline

A rule goes from surface syntax to fired action through a pipeline
that cleanly separates the pattern language from the execution
machinery. This separation is critical: it allows the scheduler to
choose any variable ordering (top-down, bottom-up, middle-out)
based on runtime cardinalities.

```
Parse       → Vec<SurfacePattern>     (tree-shaped AST, string-named)
Flatten     → Vec<Atom>               (flat constraints, synthetic vars)
Resolve     → ResolvedQuery           (dense typed ids, sorts checked)
Schedule    → QueryPlan               (ordered execution steps)
Execute     → MatchPool               (push continuations, §7.4)
Apply       → mutations               (union, insert, subsume; set is not implemented)
```

Stages 1–3 run once when a rule is parsed and installed. In the default static
mode, scheduling builds a plan from each matching round's index statistics
(and separately for each semi-naive flavor). The primary saturation path then
executes flattened atoms through push-style continuations and stores the
matches in a reusable `MatchPool` before applying actions. Rust control flow is
depth-first, but matching is not a recursive top-down walk of the source
pattern. A separate `MatchIterator` offers lazy pull execution of a static plan;
runtime per-binding scheduling uses the push path.

### Atom Types (`RAtom`)

Flattening walks the pattern tree, assigns synthetic variable names to
nested nodes, and produces flat atoms. Each atom is one relational
constraint on the e-graph. The variants cover the full spectrum of
operator kinds and matching shapes; the scheduler decides in what
order to apply them.

| Variant | Matches |
|---------|---------|
| `Plain { node, op, children }` | Fixed-arity node with specific op |
| `LitBind { node, op, val }` | Literal node, bind value to variable |
| `Lit { node, op, sort, value }` | Literal node with specific known value |
| `Eq(a, b)` | Two variables in same e-class |
| `EqGlobal(local, global)` | Variable equals a global binding |
| `AExact / APrefix / ASuffix / ABoth` | A-node with optional rest vars |
| `ACExact / ACSub` | AC-node exact or sub-multiset |
| `ACIExact / ACISub` | ACI-node exact or subset |
| `Comm { node, op, elems }` | `:comm` node, matched as a two-element multiset by `DecomposeAC` |
| `Collect { node, op, collect }` | A sequence rule's assembly at an `op` node (§7.6) |
| `Pred { guard, deps }` | Primitive predicate over bound literal values |

`Pred` is the one atom that matches nothing. It carries an expression over
primitive operators, literal constants, and the variables other atoms bind to
literal payloads, and it keeps the partial match when that expression evaluates
to true. A primitive names a function on values rather than a relation the
e-graph stores, so there is no bucket to scan for it; `deps` names the `LitBind`
atoms that fill the value slots it reads, which is what tells the scheduler when
it can run.

The surface form `(= v pat)` produces no atom of its own: `pat` flattens exactly
as it would alone, and one `Eq` ties `v` to its root.

### The Scheduling Algorithm

The scheduler must be free to bind variables in any order. Consider
`(foo x (bar x y) (baz y))`: if `bar` is rare, start there; if `baz`
is rare, start there. A fixed top-down traversal would be stuck with a
bad plan when the rare operator isn't at the root.

Two alternating phases in a loop:

#### Phase A: Eager Pass (fixpoint)

Process atoms that are "free" given current bindings (they add no
fan-out, only constrain):

- `Eq(a, b)` with both bound → `CheckEq`
- `Eq(a, b)` with one bound → `CopyBinding`
- `EqGlobal` with local bound → `CheckEqGlobal`
- `EqGlobal` with local unbound → `BindGlobal`
- `Plain`/`Lit`/`LitBind` with node already bound: re-join within e-class.
- `Pred` with every atom in `deps` already lowered → `CheckPred`.

The guard's condition is on the *atoms* that have run, not on the variables that
are bound, and it has to be: a `LitBind` atom's node variable is bound by the
enclosing pattern's `ExtractChild`, one step before the `ExtractLitVal` that
fills the value slot the guard reads. Firing the guard as soon as its dependency
atoms have run puts the check immediately after the last of them, so a false
guard cuts the search before the remaining atoms are joined.

Guards are lowered in atom order within one pass of the eager fixpoint, so
of two guards that become free at the same point, the one written first is
checked first. A guard whose dependencies are a subset of another's is
therefore never checked after it, which is what lets a partial primitive be
protected: `(i64::!= x 0)` before `(i64::== (i64::% z x) 0)` rejects the
match before the remainder is computed, because the first reads `x` alone.

#### Phase B: Cost-Based Selection

Pick the cheapest unprocessed atom. At a high level the base cost is the
atom's active `by_op` cardinality, reduced by measured fan-outs for bound
`by_repr`, `by_child_pos`, or `by_contains` probes:

```
cost(atom)                    = card(active by_op slice) × estimated selectivities
cost(Lit or LitBind)          = card(active literal-op slice)
cost(Eq/EqGlobal/Pred)        = 0
```

The actual estimator uses size-biased per-path measurements, per-atom
semi-naive cardinalities, and optional sampling as described in §8.3;
the formula above is schematic rather than executable pseudocode.

`Eq`, `EqGlobal` and `Pred` are never selected here: they have no join to cost,
and Phase A owns them.

Emit the selected atom via `emit_atom` (a `Join`, then `ExtractChild` steps for a
`Plain` atom or the decomposition step for a variadic one; a `Comm` atom's step is
`DecomposeAC` with no rest), then return to Phase A. A `Collect` atom is lowered by
`schedule_inner` itself, to `Join ByOp` plus `Step::Collect` or to `Step::Collect` alone.

#### Where the loop runs

By default both phases run once per query and produce the step array the
matcher walks. Under `ematch::set_runtime_scheduling` they run at each depth
instead, against the live environment: the same two phases over the same
`try_eager_lower` and `emit_atom`, with Phase B's estimate replaced by the
length of the shortest bucket the atom's join would open for the bindings in
hand. Static/runtime differential tests compare their match sets (§7.4,
"Which Snapshot"); this is finite implementation evidence, not a
machine-checked equivalence theorem. The flag is off by default and §8.3
documents the mode.

### E-Class–Aware Re-Join

When a `Plain` or `LitBind`
atom's node variable is already bound (from `ExtractChild` of a
parent), the bound value is the canonical representative of an
e-class, not necessarily a node with the required op.

Example: `(Mul (Num x) (Num y))`. After matching `Mul` and extracting
its children, child 0 is bound to the class rep. If that class
contains both an `Add` node and a `Num` node (because `Add(4,5)` was
rewritten to `Num(9)`), the class rep might be the `Add` node.

Naively emitting `CheckChildEq` would check the rep directly and
fail because the rep has op `Add`, not `Num`.

The fix: emit a `Join` that intersects `ByRepr(bound_class)` with
`ByOp(required_op)`:

```
Join { target: n, lookups: [ByRepr(n), ByOp(Num)] }
```

This finds all `Num` nodes in the class, rebinding `n` to each one.
Then children are extracted from the actual `Num` node. Same treatment
for `LitBind`: re-join to find the `@IBig` node in the class before
extracting the literal value.

### Execution Steps

| Step | Semantics |
|------|-----------|
| `Join { target, lookups, atom_id }` | Leapfrog intersection, bind target to each result. `atom_id` identifies which query atom this join scans: used by semi-naive evaluation to delta-restrict one atom at a time (§9.2); ignored by naive matching |
| `ExtractChild { target, parent, pos }` | Read child at position from parent node |
| `ExtractLitVal { node, val }` | Extract literal value id from node |
| `CheckChildEq { parent, pos, expected }` | Verify child and expected have the same build-snapshot representative |
| `CheckEq { a, b }` | Verify the two bindings have the same build-snapshot representative |
| `CheckEqGlobal { local, global }` | Verify local and global have the same build-snapshot representative |
| `BindGlobal { target, global }` | Bind an unbound local to a global's snapshot class |
| `CopyBinding { target, other }` | Bind target to `other`'s build-snapshot class |
| `ExpandA { node, children, pre, suf, view }` | Enumerate subsequence matches |
| `DecomposeAC { node, elems, rest, idempotent, view }` | Enumerate sub-multiset matches |
| `DecomposeACI { node, elems, rest, view }` | Enumerate subset matches |
| `Flatten { node, op, kind, out }` | Under `:flatten`: write each distinct flattened view of the bound `op` node into view register `out`, and continue once per view; the decomposition after it reads its children from that register (`view: Some(out)`) instead of the node (§7.5, "Flattened Matching") |
| `Collect { node, plan }` | A sequence rule's assembly at `node`, bound or found by the step's own filter drive (§7.6) |
| `CheckLit { node, value }` | Verify node's literal payload equals `value` |
| `CheckPred { guard }` | Evaluate the guard over bound literal values, keep the match when it is true |

> **Note**: `CheckLitEq` and `EvalLit` do not exist as `Step` variants.
> Literal constants are handled by `CheckLit`; `ExtractLitVal` binds a literal
> payload for later guards or RHS use.
> Primitive op evaluation during matching happens only in `CheckPred`, which
> computes a value and discards it after testing it; the primitives that build
> terms run during RHS application (§7.7).

### Example Plan

Pattern: `(Mul (Num x) (Num y))` with 1 Mul node, 4 @IBig nodes.

```
Step 0: Join { target: n4, lookups: [ByOp(Mul)] }         // scan 1 node
Step 1: ExtractChild { target: n0, parent: n4, pos: 0 }   // left child class
Step 2: ExtractChild { target: n2, parent: n4, pos: 1 }   // right child class
Step 3: Join { target: n0, lookups: [ByRepr(n0), ByOp(Num)] }  // find Num in class
Step 4: ExtractChild { target: n1, parent: n0, pos: 0 }   // @IBig child class
Step 5: Join { target: n1, lookups: [ByRepr(n1), ByOp(@IBig)] }
Step 6: ExtractLitVal { node: n1, val: x }                // bind x
Step 7: Join { target: n2, lookups: [ByRepr(n2), ByOp(Num)] }
Step 8: ExtractChild { target: n3, parent: n2, pos: 0 }
Step 9: Join { target: n3, lookups: [ByRepr(n3), ByOp(@IBig)] }
Step 10: ExtractLitVal { node: n3, val: y }               // bind y
```

The scheduler picks Mul first (cardinality 1) over @IBig (cardinality 4).
Steps 3, 5, 7, 9 are the e-class re-joins; without them, the match
would silently fail when the class rep has a different op.

### Dumping a Plan

Setting `EGRAPH_DUMP_PLAN` (to any value) prints every plan the scheduler
produces to stderr: a header `=== plan: N atoms, M steps ===`, then one line per step
(`step[0]: Join target=v4 atom=0 lookups=[…]`), with variables named by
their resolved index (`v3` is variable 3 of the query's `MatchShape`). The
variable is read once and cached, so leaving it unset costs one load per plan.

The dump answers what is bound when a step runs, which is the question behind
both classes of matcher defect: a re-join keyed on a variable no earlier step
binds, and a variadic expansion whose fixed children were bound elsewhere. A
`Join` on `v0` scheduled after an `ExpandA` that lists `v0` among its children
is the shape to look for.

## 7.4 Pattern Matching Execution

### Flattened-Atom Continuation Execution

Sortcheck has already flattened each source pattern into relational atoms.
The primary matcher executes either a static plan over those atoms or a
dynamic per-binding middle-out schedule. Each lowered step invokes a
push-style continuation after binding a variable or satisfying a constraint.
Rust calls explore those continuations depth-first; that is continuation
control flow, not recursive top-down traversal of the source pattern.

`run_query_into` stores emitted bindings in a reusable `MatchPool`;
`run_query` is a convenience wrapper that returns owned matches in a fresh
`Vec`. The matching phase itself is read-only: it neither mutates the e-graph
nor interns literal values. Its index buckets and class comparisons use the
round's build snapshot so they describe the same graph state.

### Which Snapshot: the Round's Index Build

The snapshot is the e-graph as of the round's `IndexStore::build`, and it stays
that snapshot for every rule of the round. It is not the e-graph as of the
query: a round runs each rule's actions before the next rule matches, so by the
time the last rule of a round runs, the e-graph holds nodes and class merges
the index does not.

This matters because canonicalization has to agree with the buckets. The three
keyed indexes are keyed by `class_repr` as of the build, so a matcher that
canonicalizes a lookup key with the live union-find and then probes those
buckets reads a bucket belonging to a different class. A merge of classes `c1`
and `c2` after the build moves `ByRepr` and `ByChildPos` in opposite
directions: a `ByRepr` probe for a node of `c1` lands on the surviving repr's
bucket, which holds only the nodes that were already there, and a `ByChildPos`
probe for a child of `c1` misses every parent filed under the absorbed repr.
`CheckChildEq` had the third behaviour, accepting any pair the live union-find
had joined. Which of the three a query performs is decided by the join order,
so the defect made the match set depend on the plan. Focused regressions retain
the failing shape without treating one workload's match counts as a current
result.

`IndexStore::repr` therefore records the build's canonicalization and every
canonicalization the matcher performs reads it (`ematch::canon`). The support
for the resulting properties has to be stated separately:

- **Plan-invariant match set, tested rather than proved.** Static join-order
  permutations and static-versus-runtime scheduling are compared by focused
  differential tests, including
  `ematch::match_set_is_independent_of_join_order` and
  `nonlinear_check_uses_the_rounds_classes`. There is no machine-checked
  theorem that every plan emits the same bindings.
- **Monotonicity argument.** A snapshot equality remains an equality in the
  live e-graph because actions merge classes but do not split them. Thus a
  binding accepted using the snapshot's classes remains valid when its action
  runs. This is an implementation argument, not a verified matcher-soundness
  theorem.
- **Next-round visibility.** Nodes and merges produced by an earlier rule are
  absent from the current index. If the round changed the graph, the next
  iteration rebuilds a full index containing the new state. The naive driver
  scans that full index; the semi-naive driver derives its delta from the
  touched log and uses documented full-scan fallbacks for constraints whose
  enabling merge is not represented by a relation delta. Finite differential
  tests exercise this accounting. There is no end-to-end proof that the two
  drivers terminate at the same semantic least fixpoint.

### `Match` — Binding Environment

The binding environment separates variables by kind. Node bindings
(plain `VarId`s) use `Option<Cfg::G>` because variables may be unbound
between continuation steps. Multiplicity and literal-value bindings
are stored directly. The three "rest" kinds (sequence, set, multiset)
use a pool-plus-span indirection: the pool stores all elements
contiguously, and each variable holds a `(start, len)` span into
the pool. This layout avoids per-variable allocation even when
hundreds of rest bindings are live. A fourth pool holds the literal columns of a
sequence pattern's filters; only sequence matches fill it.

```rust
pub struct Match<Cfg: EGraphConfig> {
    nodes: Vec<Option<Cfg::G>>,       // VarId → e-node id (None if unbound)
    mults: Vec<Cfg::M>,               // MultVarId → multiplicity
    lit_vals: Vec<Cfg::V>,            // LitValVarId → literal value id
    seq_pool: Vec<Cfg::G>,            // all seq slices packed contiguously
    seq_spans: Vec<PoolSpan<Cfg>>,    // SeqVarId → (start, len) into seq_pool
    set_pool: Vec<Cfg::G>,            // all set slices packed contiguously
    set_spans: Vec<PoolSpan<Cfg>>,    // SetVarId → (start, len) into set_pool
    mset_pool: Vec<Cfg::C>,           // packed AC children (id + mult)
    mset_spans: Vec<PoolSpan<Cfg>>,   // MsetVarId → (start, len) into mset_pool
    lit_seq_pool: Vec<Cfg::V>,        // literal sequences of a sequence match
    lit_seq_spans: Vec<PoolSpan<Cfg>>, // LitSeqVarId → (start, len) into lit_seq_pool
}
```

The `MatchShape` (from resolution, §7.2) records the names of
each variable kind and is the single source of truth for the binding
environment layout.

### Predicate Guards

`CheckPred` is the one step that computes rather than looks up. It evaluates the
guard expression bottom-up over the literal values in the match environment and
keeps the partial match when the result is true by the model's `is_truthy`. Both
function pointers it needs, the primitive's `eval` and the model's truth test,
are captured at resolve time and stored in the step, which is what keeps the
matcher generic over the literal value type alone rather than over the whole
literal model.

The step is read-only like every other matching step: the value it computes is
tested and dropped, never interned. Interning it would mint literal nodes during
matching, which the frozen-snapshot argument above rules out; a rule that wants
the value in the e-graph computes it again on the right-hand side, where
`RhsOp::PrimApp` interns it (§7.7).

The guard's placement is the scheduler's (§7.3, Phase A): immediately after
the last `ExtractLitVal` that fills a slot it reads. It cannot run earlier than
that, and running it later would join atoms whose results the guard is about to
discard.

### `MatchIterator` — Separate Pull-Based Engine

In addition to the primary push-continuation path, `MatchIterator` executes a
static plan and yields matches one at a time through an explicit depth-first
stack:

```rust
pub struct MatchIterator<'a, Cfg, L, S, const T, const P> {
    plan, eg, index, globals,
    env: Match<Cfg>,
    frames: Vec<Frame<'a, Cfg>>,
    cursor, done, guard_fault,
}

impl MatchIterator { fn next_match(&mut self) -> bool { ... } }   // then read env()
impl Iterator for ClonedMatchIter { type Item = Match<Cfg>; ... } // via cloned_iter()
```

Each `Frame` on the stack represents a choice point (e.g., which
element of a `Join` result to try next). `next_match()` resumes from the
last choice point, advancing or backtracking as needed. The iterator does not run
every static plan: its `Collect` arm, its `Flatten` arm, and its view-reading
decomposition arms fail the branch (`Enter::Failed`).

Callers that stop consuming it can avoid materializing later matches. The
saturation drivers do not currently use this path: they execute
`run_query_scheduled_into` (the trace driver, `saturate_trace`, runs `run_query_into` on a
static plan), collect the round snapshot's matches in a
`MatchPool`, and apply every collected match. In particular, `:subsume` does
not make saturation stop after the first match.

Pushing a frame and resuming it are two paths to the same search, so both
have to run it: the sliding-window frame scans forward to the first split
that binds when it is pushed, exactly as `backtrack` does when it advances.
Entering at split 0 and reporting failure there dropped the frame with the
later splits untried, which a pre-bound or global fixed element reaches
(fixed elements that are all fresh always bind at split 0). The same holds
for the two decomposition frames: a first assignment that does not consume
the whole multiset is undone before the frame is dropped, so the element
variables do not stay bound for whatever the search enters next.

## 7.5 Matching A, AC, ACI, and C operators

AC matching implements *maximum-partition* matching over the classes that exist:
- each scalar pattern variable takes one child entry, with its whole multiplicity;
- `..rest` takes exactly the entries left over;
- without `..rest`, every entry must be taken.

Two restrictions are deliberate. A variable binds an e-class, never a sub-sum that no
node spells: `?x` cannot become `a+b` if no node `a+b` exists. And a multiplicity is
never split between variables. Classical AC matching admits both, and is NP-complete
(Benanav, Kapur, Narendran 1987).

The completeness problem that matters in practice is nesting. A node stored as `+(a, c)`,
where `c`'s class holds `+(b, d)`, has the flat content `+(a, b, d)`, which a pattern
over three operands does not match.

A rule tagged `:flatten` closes that gap at match time. The matcher enumerates the
node's flattened views by opening member classes of the same operator, and normalizes
each view with the same function as §5.1. Two rules keep this tractable:
- **Demand.** A class is opened only when a pattern item takes an element from inside
  it. The demand rule cut a self-referencing test from 10,615 matches to 128 (13.6 s to
  9.4 s).
- **Bounds.** At most 2^20 views, 2^24 steps of work, and 2^24 stored view elements per
  node. A node over a bound is skipped and reported (`OVER_BOUND`), never silently
  dropped. A view whose multiplicity overflows the width is skipped alone and reported
  with its nested form (`MULT_OVERFLOW`, `apply::report_flatten_skips`).

Views cover nesting for A, AC, and ACI operators; a `:comm` operator is matched in both
orders instead. Sequence patterns (filters, runs, `:except`) are matched by the same
views.

Guarantee: completeness relative to maximum partition plus views is argued in the
design, and checked by differential tests against brute-force references
(`tests/flatten_differential.rs`, `tests/seq_reference.rs`); the `:flatten` reference
reuses `nary_canon::normalize` and the demand rule, so it checks the enumeration and the
decompositions, not those two. It is not machine-proved, and it has two known
exceptions: a view whose opening contributes only by inverse cancellation or the
nilpotent clamp is dropped by the demand rule, and a degenerate stored node (`And{K}` in
`K`'s class) matches an untagged `(And x)` but has no view under `:flatten` (see "The
demand rule" below). Patterns are matched as written: a pattern that construction would
store in another form (an identity child, an inverse pair, a repeated element, a nested
same-operator application, a single element) matches nothing, without a warning.

Details: below, "Sub-Multiset Matching
(AC operators)", "The matching relation we implement", and "Flattened Matching
(`:flatten`)"; [§7.6, Sequence Patterns](#76-sequence-patterns-in-the-relational-matcher);
the book section [Matching completeness over A, C, AC, and
ACI](../../../doc/book/src/05-rules-and-patterns.md#matching-completeness-over-a-c-ac-and-aci).

### Subsequence Matching (A operators)

`ExpandA` enumerates all ways to match a fixed sequence of pattern
elements against a contiguous subsequence of an A-node's children.

For pattern `(concat ..pre x y ..suf)` against node with children
`[a, b, c, d, e]`:

```
Split 0: pre=[]      x=a  y=b  suf=[c,d,e]
Split 1: pre=[a]     x=b  y=c  suf=[d,e]
Split 2: pre=[a,b]   x=c  y=d  suf=[e]
Split 3: pre=[a,b,c] x=d  y=e  suf=[]
```

Each split binds the prefix/suffix rest variables as slices into the
pool and the fixed elements as individual bindings, then invokes the
continuation.

A fixed element whose variable an earlier step already bound is checked
against the child at that position rather than rebound, and the split's
cleanup leaves it bound: the binding belongs to the step that made it, and
the expansion is one more constraint on it. Both engines therefore record
which variables a split bound and clear exactly those, on the failure path
and after the continuation returns. Clearing every local child is unsound,
with two failure shapes the fixtures pin: the next split rebinds the
variable from its own children, so the rule fires on positions the earlier
atom excluded, and a re-join keyed on that variable reads it as unbound and
panics. `DecomposeAC` and `DecomposeACI` carry the same rule for a
pre-bound element variable.

For exact match (`AExact`): children count must equal pattern count.
For prefix-only (`APrefix`, written `(op ..pre x y)`): rest at start, fixed elements at end.
For suffix-only (`ASuffix`, written `(op x y ..suf)`): fixed elements at the start, rest at end.

### Sub-Multiset Matching (AC operators)

`DecomposeAC` enumerates all ways to match pattern elements against a
subset of an AC-node's `(id, multiplicity)` children.

#### Maximum Partition Semantics

This section is the normative statement of AC matching; the language
guide's AC section and its migration caveat summarize it for rule
authors. A match is a partition of the node's distinct children among
the pattern elements and the rest variable:

1. Each pattern element binds a distinct child and takes that child's
   whole multiplicity. The element's annotation constrains the total:
   an unannotated element binds only a child whose total multiplicity
   is exactly 1.
2. No two elements bind the same child, so a repeated child needs an
   element that names its multiplicity (`x:2`, `x:k>=2`). This is why
   an n-ary lift of a binary rule needs its multiplicity variant: the
   binary pattern's two positions can coincide on one term, the two
   multiset elements cannot (language guide, migration caveat).
3. The rest variable takes every unbound child, each with its whole
   multiplicity.

#### Multiplicity Constraints

Each multiplicity variable has a global interval `[min, max]`, computed at
compile time by intersecting all constraints. Resolution uses the interval only to
reject an empty intersection; at match time `ematch::mult_matches` checks each
occurrence's own annotation against the child's total multiplicity, and equality with
the variable's earlier binding, which has the effect of the intersection:

| Syntax | Interval |
|--------|----------|
| (omitted) | [1, 1] |
| `:3` | [3, 3] |
| `:k` | [1, ∞] |
| `:k >= 2` | [2, ∞] |
| `:k < 5` | [1, 4] |

Non-linear multiplicity variables (same `:k` on multiple elements)
must bind to the same value. The first occurrence binds, subsequent
occurrences check equality, an O(1) comparison rather than a loop.

If the interval intersection is empty (e.g., `>= 10` and `< 10`),
the query is statically unsatisfiable, and resolution rejects the rule ("unsatisfiable
multiplicity for 'k': … (empty interval)"); the e-graph is never touched.

#### Cost and Correctness of AC Matching

`DecomposeAC` enumerates bindings of pattern elements against a node's
multiset. It is worth being precise about what is enumerated, because
"enumerate all sub-multisets" overstates it, and about which costs are
intrinsic versus avoided.

What we do and do not enumerate:

1. Bound or concrete pattern elements scan the residual. When a pattern element's
   variable is already bound (its e-class is known), the matcher does a
   linear `position` search for that class in the residual multiset, checks its total
   multiplicity against the element's annotation (`mult_matches`), and removes the child.
   This is O(d) for `d` distinct residual entries, though it avoids branching.
   (In `decompose_ac_elem`, this is the `if let Some(repr) = bound_repr` path.)
2. Only unbound scalar variables cause branches, and they branch
   over the distinct residual elements, not over sub-multisets. The matched
   multiplicity is taken whole, so we do not enumerate "1 of this element,
   or 2, or 3…". This is the overview's *maximal partition matching*: the
   multiplicity sub-count blowup is avoided, and branching is restricted to
   distributing unique residual elements among unbound variables.
3. The `rest` variable absorbs the entire remainder in one binding. A
   pattern `(+ ?x ..rest)` yields `O(distinct elements)` matches (bind `?x`
   to each distinct element, `rest` captures the rest as one multiset-typed
   binding), not `O(2ⁿ)` over sub-multisets of the residual.

So for a pattern with `k` unbound scalar variables against a node with `d`
distinct children, there are at most `d!/(d-k)! <= d^k` candidate scalar
assignments before constraints prune them. Traversal work also includes the
per-level residual scans. For fixed `k` this is polynomial in `d`, but the
algorithm remains exponential in the pattern-arity parameter. Leapfrog narrowing over the indices
(`by_op ∩ by_contains[e]`, [§8.1](08-indexes-and-leapfrog.md#81-index-construction)/[§8.2](08-indexes-and-leapfrog.md#82-leapfrog-triejoin))
can restrict the candidate nodes before `DecomposeAC`; how selective that
restriction is depends on the graph and query.

Two examples show which exponential was removed and which remains:

- Against `{a:1_000_000_000, b:1_000_000_000, c:1_000_000_000}`, the pattern
  `(+ ?x ?y ..rest)` considers at most `3 * 2 = 6` ordered scalar bindings.
  It does not enumerate a billion possible counts for either child or every
  residual sub-multiset.
- Against 30 distinct children, the same two scalar variables admit up to
  `30 * 29 = 870` bindings; three scalar variables admit up to
  `30 * 29 * 28 = 24,360`. High distinct-child count and pattern arity still
  matter, so "avoids exponential matching" without naming the multiplicity
  parameter would be false.

##### The matching relation we implement

A correctness claim only means something against a relation defined
independently of the algorithm. Classical AC matching (Contejean, RTA 2004;
also Hullot 1979) asks:

> Given a pattern `p` and a subject `s`, a match is a substitution `σ` with
> `pσ =_AC s`, where `=_AC` is equality modulo associativity and
> commutativity.

The shipped relation is a strict specialization, **maximum-partition
matching**. Let the subject be `M = {(g_j, c_j)}` with distinct `g_j`. A
solution injectively assigns each scalar pattern element to one entry, requires
its multiplicity predicate to accept that entry's whole `c_j`, and assigns the
rest variable exactly the unassigned entries. Without a rest variable, every
entry must be assigned. Repeated occurrences of one scalar cannot consume one
entry twice.

Every emitted substitution is intended to satisfy both this relation and the
corresponding classical multiset equation, but this is an algorithmic argument
backed by finite unit, property, and differential tests, not a verified
theorem. Completeness is open even for the stated maximum-partition relation.
The implementation deliberately does not enumerate the additional
sub-multiplicity distributions admitted by classical AC matching, so it is not
complete for classical AC matching by design. AC matching in that broader
sense is NP-complete (Benanav, Kapur, Narendran 1987); Contejean's
inference-rule algorithm is a different algorithm verified complete in Coq.
The [Chapter 6](06-ac-congruence-closure.md)
verification plan is where that would be taken up.

One scope note, so the relation itself is not misread. The variables in `σ`
range over what exists: an e-class id for a scalar, an existing sub-multiset
for `rest`. A scalar variable is not quantified over implicit sub-sums:
matching `(+ ?x ?y)` against a node stored only as `+(a, b, c)` does not
admit `?x = a+b`, because `a+b` is not an e-class id. Allowing that binding is
term-valued classical AC matching against a ground subject, outside the shipped
relation; general AC unification is broader because both sides may contain
variables. Materializing all sub-sums is one expensive way to expose such
bindings, with up to `2^d` candidates for `d` distinct children and generally
`product_i (m_i + 1)` for child multiplicities `m_i`. Ordinary congruence
rebuild does not synthesize absent sub-sums. Existing or explicitly built
sub-sum nodes can become matchable, and opt-in completion derives some
equalities hidden by flattening, but neither mechanism establishes complete
classical AC matching.
See
[Chapter 6 §5b](06-ac-congruence-closure.md).

The other loss of completeness is nesting: a node stored as `+(a, c)` where `c`'s
class holds `+(b, d)` is the flat content `+(a, b, d)`, which a pattern over three
operands does not match, because construction flattened only what it built. A rule
tagged `:flatten` matches every flattened view of the node instead ("Flattened
Matching" below), which restores completeness over nesting for A, AC, and ACI
operators without storing a flat node, with the two exceptions stated in the guarantee
above.

### Subset Matching (ACI operators)

`DecomposeACI` enumerates all ways to match pattern elements against a
subset of an ACI-node's children (no multiplicities, since all counts
are structurally 1 due to idempotency).

Each pattern element must match a distinct child. The rest variable
captures the unmatched children. This is the set analogue of the
maximum-partition relation above; its implementation has finite test evidence,
not a soundness or completeness theorem.

### Flattened Matching (`:flatten`)

A rule tagged `:flatten` matches each n-ary atom against every *view* of its node
rather than only the stored children (`doc/goal-flatten-and-engine-completion.md` in the
ltl-eqsat repository, decisions 2 and 3). The scheduler emits `Step::Flatten { node, op, kind, out }` before
the atom's `ExpandA`, `DecomposeAC`, or `DecomposeACI`. The step enumerates the views
(`crate::flatten`), writes each into view register `out` of the match pool, and runs
the continuation once per distinct view. The decomposition then reads its children
from the register. Nothing stored changes.

For a node of operator `f`, each child class `X` is either kept whole or opened: one
of its `f` members is spliced in its place, unless `X` is already open on the path
(the root's own class is not on the path). "Member" is what the round's index holds:
`by_repr[X]`, filtered by each node's round operator. A view is canonized by the one
normalization of an n-ary child list (`crate::nary_canon`): coalescing or
deduplication, the identity drop, the nilpotent clamp, and inverse-pair cancellation,
with multiplicities multiplied through each opened member. A view whose canonical form
is not a node (a single class, the unit, or empty) is not matched.

**The demand rule** (`doc/goal-canonical-flatten-views.md` in the ltl-eqsat repository,
decision 2). A class is
opened only when an item takes an element from inside it. Each raw view carries its
opening tree. A leaf of the tree is an opened instance with no opening below it. A
match is kept when, for some tree giving its canonical view, every leaf directly holds
a class the items take; interior openings are then needed through the leaves below
them. Keeping is always an option, so when an opening only feeds the bare rest, the match
exists with that class whole; `every_dropped_match_has_its_refolded_match` pins this for
patterns with a rest. Two cases escape the rule. A leaf group holds the opened member's
raw elements, recorded before normalization, so an opening that contributes only by
inverse cancellation or the nilpotent clamp is dropped although no refolded match exists
(`add{a,d,e,f,K}` with `K ≡ add{neg a, neg d}` loses `(add x y)` with `{e, f}`; found by
reading, no test). A degenerate stored node such as `And{K}` has only a single-class view,
which is not matched. The
enumerator (`crate::flatten::enumerate`) records each view's trees as a
`flatten::Demand`. The decomposition reading the view (`DecomposeAC`, `DecomposeACI`,
`ExpandA`) and the sequence assembly (`seq_collect::assemble_views`) check it once the
items have their elements. The walk is pruned by the same rule: an instance that closes
as a leaf with no takeable element abandons the branch. Per-instance counters make the
check constant-time. An element is takeable when the decomposition's items are all
bound and it is one of their classes; otherwise every element is.

The walk follows the e-graph's nesting, so it is an explicit-stack depth-first search
over pending tasks, the view so far, the open classes and instances, and an undo trail.
A chain of 10^5 nested conjunctions costs no Rust stack. Three bounds stop one node's
enumeration, each counted with checked arithmetic: 2^20 combinations, 2^24 options
taken, and 2^24 stored elements. A node over any of them is skipped and counted
(`flatten::OVER_BOUND`, `MatchPool::flatten_skipped`). A count past the configured width
skips only the opening or view it makes unrepresentable, not the node: it is counted in
`MatchPool::flatten_overflowed`, and the first is kept as a `flatten::FlattenOverflow`
with its cause. Saturation prints a warning naming the rule and, for an overflow, the
nested form of the term (`apply::report_flatten_skips`), and the run continues. The
sequence path still skips the whole node when one of its views overflows
(`flatten::views_u64`). The sequence path
also bounds the matches assembled over all of a node's views at 2^20.

Four constraints on scheduling follow:

- **No `by_contains` filter on a flattened atom's join.** A bound element can sit in a
  view without being a stored child, so the filter would skip a node whose views still
  match. That is the index-filter soundness requirement of §9.2. The join drives
  from `by_op`, or re-joins in the class through `by_repr` when the node is bound. The
  cost model prices the atom accordingly.
- **Static plans only.** The runtime scheduler (`Adaptive::fits`) and the pull engine
  never receive a `Flatten` step or a register-reading decomposition; a flattened query
  is scheduled statically, as a sequence pattern's `Collect` is.
- **Naive under semi-naive.** A view changes when a class below the node gains an `f`
  member, and no variant's delta holds the root then, so `needs_naive_match` returns
  true for a flattened ordinary query (§9.2). Sequence rules under `:flatten`
  are semi-naive: their delta climbs through nesting (§7.6).
- **`:comm`-only operators are untouched.** A view splices the children of members
  of an A, AC, or ACI operator (`FlatKind` is `Assoc`, `Ac`, or `Aci`); a commutative
  operator has no flattened form, and its pattern is matched through `RAtom::Comm` and
  `DecomposeAC`, which tries both assignments of the two children, as without the tag.

In proofs mode, a union found through a view carries `Justification::Rewrite` with the
rule's id, as any rewrite's does (`flatten_differential::a_flattened_union_cites_the_rule`).
The rule's left-hand side instance equals the root node only modulo associativity. Semper's
proofs are explanation steps and replay no instance, so they need no associativity step.

#### Alternatives considered and rejected

- **AC completion to supply the flat node.** Completion orients toward the reduced
  form: with `(And g1 cc)` built and then `cc ≡ (And g2 g3)`, the rule `{g2, g3} → cc`
  makes the flat multiset `{g1, g2, g3}` reducible to `{g1, cc}`, so the flat term is
  proved equal when something builds it but is never created, eager or lazy
  (`tests/egg/seq_flatten_completion.egg`). Views give the three-operand match with
  completion off (`tests/egg/seq_flatten.egg`).
- **Storing flattened nodes.** Materializing every flat spelling changes the graph
  every rule sees and its size, with up to `2^d` sub-sums for `d` distinct children.
  Views are computed at match time and stored nowhere, so a rule without the tag
  matches as before.
- **Every combination as a view.** The first version matched every opening tree. A
  match from a view that opens a class none of whose spliced elements is taken by an
  item only feeds the bare rest, so it repeats a match of a less-opened view. The
  demand rule drops those: on the self-referencing-classes stress test the matches fell
  from 10,615 to 128 and the time from 13.6 s to 9.4 s, and each of the 1,268 matches
  the old rule kept and the new one drops was found to have its refolded match among the
  kept, as measured (`seq_differential::flatten_self_referencing_classes_finish` prints
  the counts and asserts none of them).
- **Keeping a class whole only when it has a member of another operator.** An
  earlier demand rule; the refolding property needs the match with an unneeded class
  kept whole, so keeping is always an option, and a tagged rule's matches include every
  untagged match at a non-degenerate node.
- **A view normalization of its own.** Views were first normalized with sort, sum,
  and dedup only, without the identity drop, the nilpotent clamp, inverse cancellation,
  or the degenerate arities, so a view and a built node could disagree on one content.
  Views now go through `nary_canon::normalize` (§5.2).
- **A `by_contains` filter on a flattened join.** A view can hold a class that is not
  a stored child, so the filter would skip matchable nodes; a flattened atom's join has
  none.

Tests: `tests/flatten_differential.rs` compares the engine with a brute-force
reference over random e-graphs, with and without the tag. It also covers a 10^5-deep
chain, the view bound, and proofs mode. The egg programs are `flatten_nested.egg`,
`flatten_identity.egg`, `flatten_inverse.egg`, `flatten_nilpotent.egg`, and
`flatten_rest_only.egg`, each with a `_control`; `flatten_cycle.egg`,
`flatten_two_members.egg`, `flatten_assoc.egg`, `flatten_ac_mult.egg`,
`mult_flatten_view_overflow.egg`, `flatten_with_nary_no_warning.egg`, and
`flatten_without_nary_warns.egg`; and the `seq_flatten*.egg` programs.

## 7.6 Sequence Patterns in the Relational Matcher

This section records how sequence patterns (`doc/sequence-patterns.md` in the
ltl-eqsat repository) are typed, lowered to atoms, matched by the relational engine
of §7.3 to §7.5 and Chapter 8, evaluated semi-naively as in §9.2, and consumed by the
right-hand side. It describes the engine as built (`seq_engine.rs`, `seq_query.rs`,
`seq_collect.rs`, `seq_rhs.rs`). The semantics are fixed by the design document and
by the reference matcher (`egraph/tests/seq_ref/mod.rs`); the engine changes how
matches are found, not which, and the differential tests pin that. One example runs
through the section. The designs this engine replaced are at the end, under
"Alternatives considered and rejected", and in "Collection rules (superseded)".

### The running example

The examples of this section rewrite formulas of mission-time LTL (MLTL), the temporal
logic with interval-bounded operators that §11.2 introduces, where `Global (Interval l u)
p` is `G[l,u] p`. The measurements are on the 1,172 MLTL specifications Johannsen and Rozier
publish with their artifact [JR26](11-extraction.md#references), fetched for the tests that use them and not stored
here, and on the 17 NASA specifications of the same artifact.

Factoring over a conjunction, with the element comprehension `for g in gs`:

```lisp
(rewrite (And (..gs (Global (Interval l u) p)) ..rest)
         (And (Global (Interval K0 K1)
                      (And ..{ (Global (Interval (- l K0) (- u K1)) p) for g in gs }))
              ..rest)
  :let ((K0 (min l)) (K1 (+ K0 (min (- u l)))))
  :when ((>= (count gs) 2) (> K1 0)))
```

against

```
c1 = { g1: (Global i1 pa) }                    i1 = (Interval 2 5), pa = (Var "a")
c2 = { g2: (Global i2 pa), f2: (Future i3 pb) } i2 = (Interval 3 9)
c3 = { v3: (Var "x") }
n  = (And c1 c2 c3)
```

`c2` has two members: an earlier rewrite made `G[3,9] a` equal to `F[…] b`.

### Where sequence patterns are allowed

A sequence pattern is the left-hand side of a `rewrite` whose root is an A, AC, or
ACI operator. Filters occur at the root only, so they do not nest. A `:comm`-only
root is rejected, as are two bare sequences under AC or ACI (their split would be
arbitrary) and an `:except` cycle. Under A any number of bare sequences may sit
between items, and a filter takes a maximal run of consecutive children. Under AC a
filter child carries its multiplicity: an unannotated filter takes only children of
multiplicity 1, and `(..xs:k P)` takes any multiplicity and binds it. The checker
(`collection.rs`, `check`) enforces these restrictions with the offending span.

### Typing

A filter's pattern is an ordinary pattern, and inside it every variable is typed as
it would be in an ordinary rule: in `(Global (Interval l u) p)`, `l` and `u` are
`i64` (the arguments of `Interval`) and `p` is `MLTL`. Outside the filter the same
names denote one value per element the filter takes, so they have a sequence type
over the same sort. That is the depth rule of `doc/sequence-patterns.md`: a
variable's type is its sort in the pattern, lifted to a sequence by its enclosing
filter (at most one, since filters do not nest).

| name | in the pattern | in `:let`, `:when`, and the right-hand side |
| --- | --- | --- |
| `gs` (the filter) | none | `Seq(MLTL)`, the children taken |
| `l`, `u` | `i64` | `Seq(i64)` |
| `p` | `MLTL` | `Seq(MLTL)` |
| `rest` (bare) | none | `Seq(MLTL)` |
| `K0`, `K1` (`:let`) | none | `i64` |

A sequence is consumed in three ways, and in no other:

- **Reductions.** `(count s)` is `i64` for any sequence; `(min s)`, `(max s)`,
  `(sum s)` take `Seq(T)` to `T` when `T` has the primitive (`i64::min`, `i64::+`).
  `(min l)` has no value on an empty `l`, and then the rule does not fire, which is
  what lets `:let` bind a reduction the `:when` guards depend on.
- **Element-wise primitives.** A primitive applied to sequences of equal length is
  applied per element: `(- u l)` is `Seq(i64)`, so `(min (- u l))` is `i64`. A scalar
  argument is broadcast.
- **Comprehensions and splices.** `..gs` splices the children back.
  `..{ body for g in gs }` iterates the filter's elements; inside `body` the filter's
  pattern variables are scalars again, bound to the element's values (`l : i64`,
  `u : i64`, `p : MLTL`, and `g : MLTL`, the child itself). A binder `g:k` also binds
  the child's multiplicity under AC. Tuples appear only for primitives that return
  them: `(union-by p l u)` is `Seq((MLTL, i64, i64))`, consumed by
  `..{ body for (q a b) in (union-by p l u) }`, and `(zip l u p)` builds one. The
  bracket follows the target operator's kind: `..{ }` under AC and ACI, `..[ ]`
  under A.

Anything else a sequence is given to (a term argument, a scalar primitive with no
sequence operand, a guard) is the error "a sequence used as a scalar". The resolver
infers the types by these rules in `seq_rhs.rs`, the module that also evaluates the
right-hand side. The sequence primitives are `zip`, `union-by`, `narrow`,
`narrowed`, and `concat`, selected by name inside the sequence engine
(`seq_rhs::is_rows_prim`), not entries of the literal model's primitive registry
(Chapter 10); a program cannot register a new one. A term under an AC or ACI operator with one operand is that
operand, by the unit law.

### Relational formulation

**The filter relations.** For each filter `i`, `F_i(c, m, ȳ)` holds when member `m`
of class `c` matches the base pattern with bindings `ȳ`. The base is an ordinary
pattern, so `F_i` is an ordinary conjunctive query with root variable `m`, compiled
to atoms and run by the leapfrog join. Member choice is a property of `F_i`: each row
is one member with one binding, and every row gives a match.

In the example, `F0` has one row for `c1` (`m = g1, l = 2, u = 5, p = pa`), one for
`c2` (`m = g2, l = 3, u = 9, p = pa`; `f2` is not a `Global`), and none for `c3`.

**The assembly.** A match at `n` is an assignment of `n`'s children to items
(`doc/sequence-patterns.md`, Semantics) such that every child a filter takes has a
row, every child a bare sequence takes has none, and each filter child contributes
one row. It is an aggregation grouped by `n`: it depends on all of `n`'s children,
including the absence of rows for the rest. An ordinary join of `n = And(…, m, …)`
with `F0` would produce one match per (node, matching child) pair, where the rule
needs one match holding both children and the knowledge that `c3` has no row. That
is why the assembly is one atom of the outer query and not ordinary atoms.

The outer query is therefore non-monotone in `F_i`: a new row can remove a match (a
child moves from the rest into a filter) as well as add one. Removal needs no
action, because rewrites only add equalities; see "Soundness".

### Lowering

| item | role |
| --- | --- |
| filter sub-queries (`seq_query::SubQuery`): ordinary atoms resolved as a `ResolvedQuery` with a distinguished root variable | the relations `F_i` |
| simple items beside filters: their own sub-queries (`CollectSpec::ones`) | probed per child; the assembly assigns the child |
| `RAtom::Collect { node, op, collect }`, carrying a `CollectSpec` | the assembly at `node` |
| `Step::Collect { node, plan }`, carrying a `CollectPlan` | executes the assembly |

`CollectSpec` (`seq_engine.rs`) holds the assembly (`Assembly`: the rule's
`seq_collect::Spec`, each simple item's scalar slots, and the layout of the match
pools), the filters' and simple items' sub-queries, the root operator, the filters
the rule requires non-empty, and the `:flatten` tag. `schedule_inner` lowers the atom
itself, because the item plans are priced with the round's statistics, into
`Step::Collect { node, plan }`, preceded by `Join { n ← ByOp(root) }` when the drive
is the root's.

For the example:

```
F0, root m:
  A0:  m  = Global(i, p)       Plain
  A1:  i  = Interval(x1, x2)   Plain
  A2:  x1 = @i64 → l           LitBind
  A3:  x2 = @i64 → u           LitBind

outer:
  C0:  n = Collect(And, [ Filter(F0 → gs; cols l, u, p), Bare(rest) ])
```

### Plans

Each sub-query has two plans, both ordinary `QueryPlan`s over its atoms
(`seq_query::FilterPlans`).

**Bound-root plan** (the root class is given; used to probe one child):

```
Step 0: Join { target: m,  lookups: [ByRepr(root), ByOp(Global)] }   // Global members of the class
Step 1: ExtractChild { target: i,  parent: m, pos: 0 }
Step 2: ExtractChild { target: p,  parent: m, pos: 1 }
Step 3: Join { target: i,  lookups: [ByRepr(i), ByOp(Interval)] }
Step 4: ExtractChild { target: x1, parent: i, pos: 0 }
Step 5: ExtractChild { target: x2, parent: i, pos: 1 }
Step 6: Join { target: x1, lookups: [ByRepr(x1), ByOp(@i64)] }
Step 7: ExtractLitVal { node: x1, val: l }
Step 8: Join { target: x2, lookups: [ByRepr(x2), ByOp(@i64)] }
Step 9: ExtractLitVal { node: x2, val: u }
```

**Free-root plan** (all rows of the round): the same atoms scheduled by selectivity
with `m` unbound, so it may start from `ByOp(Global)`, from `ByOp(Interval)`, or
from a literal, middle-out as any rule body. A filter whose base is a variable
(`every_class`: every class is its own row) has no free-root plan and is always
probed.

`CollectSpec::plans` chooses, once per rule and round, a `CollectPlan`: the drive
(`Drive::Root` or `Drive::Filters`), whether part 2 runs, the driving filters, and
an access path per filter.

### Choosing where to start

The ordinary scheduler starts a query from its most selective atom (§7.3). A
sequence rule has two parts, and only the filter sub-queries can go first: their
rows name the classes a candidate node must contain. The assembly cannot start from
a child, because at a candidate node every child must be examined (a filter takes
every child it matches, and the rest must hold none). So selectivity chooses how
candidate nodes are found; each candidate is assembled in full.

**Example.** `(And (..gs (Global (Interval 0 1000) p)) ..rest)` over 100,000 `And`
nodes and three `Global[0,1000]` nodes. Root-driven, the plan assembles at 100,000
nodes. Filter-driven, it runs `F0`'s free-root plan (three rows), takes the parents
of the rows' classes, and assembles at those few nodes.

**Where a filter-driven plan starts.** Every sub-query gets two plans
(`SubQuery::plans`): a bound-root plan (`schedule_with_bound`), which runs at a candidate
whose root class is known, and a free-root plan (`schedule_with_stats`), scheduled as an
ordinary query from its most selective atom (§7.3). A filter-driven rule therefore works
outward from the middle of the pattern: inside the filter, from the free-root plan's
cheapest atom toward both the base's root and its leaves; up to the rule's root, through
`by_contains` (the climb under `:flatten`); and down to the other children, through the
bound-root plans and probes. The constraints are the assembly's. The root is bound when
the assembly runs; plans are static (`Adaptive::fits` declines a `Collect` query);
simple items never drive and are always probed at the candidate's children
(`Source::one`); and a filter whose base is a variable has no free-root plan
(`every_class`), so it cannot drive. The middle-out start holds for filters only. No test
pins the atom a free-root plan starts at: `check_subqueries` (`tests/seq_differential.rs`)
asserts that free-root rows equal bound-root rows.

**The drive** (`seq_engine::drive`). The candidates are the root-operator parents
(`by_contains`) of the classes holding a driving filter's rows, one sorted,
deduplicated list per rule and round, computed inside the `Collect` step; the step
binds each candidate itself. Under `:flatten` the candidates are the climb
(`seq_engine::climb`): the `by_contains` parents of the root operator, their
classes, their parents, and so on, an explicit stack with a visited set. A node the
climb does not reach has no row's class in any view.

**Two parts.** A filter may match no child, so a node with no row at all still
matches, with every filter empty and the bare sequences holding all its children.
Rows cannot find such nodes, so the matches split into two disjoint parts:

- *Part 1, candidates*: the drive's list, assembled in full.
- *Part 2, the other nodes*: `ByOp(f)` minus the candidates (a filter of the bucket
  by the candidates' sorted set), assembled with every filter's rows empty
  (`FilterRows::Empty`), probing no filter. Under A this gives the splits among the
  gaps with every run empty. Without a bare sequence, a node with children has no
  part-2 match.

The two parts together are all nodes of `ByOp(f)`, so the match set is the
root-driven plan's, which the differential tests check under every forced plan.

**When part 2 is dropped.** A rule that cannot fire with filter `g` empty needs no
part 2 and drives from `g` alone (`SeqRhs::required_nonempty`). The analysis is
conservative. `g` is required non-empty when:

- a `:when` conjunct is `(>= (count g) k)` with `k ≥ 1`, or `(> (count g) k)` with
  `k ≥ 0`;
- a `:let` or `:when` applies `min` or `max` to one of `g`'s columns, which has no
  value on an empty sequence;
- a conjunct requires a non-empty result of a sequence primitive whose rows come
  from `g`.

With several filters required non-empty, the candidates are the nodes holding a row
of each: the intersection of the per-filter lists. Marking a filter non-empty
wrongly would lose part 2's matches, so the analysis is tested against the
reference: for each filter it marks, part 2's matches fail the rule's `:let` and
`:when`.

| rule (`rules/mltl_nary_decl.egg`) | required non-empty | plan |
| --- | --- | --- |
| factoring (`And`, `Or`) | `gs` (`:let (K0 (min l))`) | drive from `gs`; no part 2 |
| narrowing | `fs` (`(> (count (narrowed …)) 0)`) | drive from `fs`; no part 2 |
| merging (`And`, `Or`) | `gs` | drive from `gs`; no part 2 |

On the MLTL rules part 2 never runs: every rule has a filter required non-empty.

**The choice.** Filters drive when the driving filters' estimated rows
are fewer than `|ByOp(f)|`. The estimate `est_rows` is an upper bound: the
cardinality of the operator a sub-query's root atom scans when that atom is `Plain`,
`Lit`, or `LitBind`, 1 for a global base, and unbounded otherwise, which selects the
root drive; every driving filter must also be drivable (not `every_class`). It reads the
root operator only, not the free-root plan's cheaper start. Runtime scheduling declines `Collect` queries (`Adaptive::fits`),
so the choice is made once per rule and round. A test override
(`set_plan_override`) forces the drive and the access path for the plan-invariance
tests.

**Measured** (`tools/measure_seq_drive.sh`, which regenerates
`results/flatten_task5_drive_*.tsv`; in-round, naive, release build, `--jobs 8`).
Over the 1,172 specifications at 2 rounds, the cost model drives from the filters in
1,650 of 2,311 steps for merging and factoring under `And`, 891 for both under `Or`,
and 1,075 for narrowing; on those steps the candidates are 1.5% to 2.3% of
`|ByOp(f)|`. The sequence rules' matching time is 102.6 ms against 261.4 ms with the
root drive forced (0.39×). On the 17 NASA specifications the ratio is 0.71×, 0.69×,
and 0.61× at 2, 3, and 4 rounds. Both configurations reproduce the recorded figures
exactly, which is the plan invariance on those specifications.

### Execution

**Filter rows per child.** `Collect(n)` obtains `F_i(c, ·, ·)` for each child `c` by
one of two access paths, fixed by the drive:

- *Probe*: run the bound-root plan with `root := c`. Used under the root drive, and
  always for a filter without a free-root plan.
- *Materialize*: under a filter drive, run the free-root plan once per round and
  group its rows by class (the round snapshot's representative); a child's rows are
  a lookup. The drive needs those rows anyway to find the candidates.

Both paths give the same rows, so the access path changes cost, not the match set.
Two rules whose filters share one base share its rows: the free-root rows are
cached per call of `apply_rules`, keyed by the plan's steps and the filter's
variables (`RowCache`), so the base's plan runs once per round
(`two_rules_on_one_base_share_its_rows`).

**Assembly.** One function assembles at a node, `collect_with`, whatever the drive,
the access path, or the semi-naive strategy: it reads the node's children through
the snapshot (`ematch::round_canon`), takes the filter rows from the chosen source,
and calls `seq_collect::assemble` (or `assemble_views` under `:flatten`). The
assignments follow the definitions as the reference does:

- under AC and ACI, the simple items' injective assignment first, then per residual
  child the (filter, row) choices with `:except` applied, odometer-enumerated, with
  unmatched children going to the bare sequence (or no match);
- under A, the parse over items in order, with maximality at gaps.

Rows are deduplicated by binding values before assembly. A node exceeding 2^20
matches (`seq_collect::MAX_MATCHES`) is skipped with a warning and counted, and the
run continues.

**Trace of the example** (probe path):

| child | `F0` rows (bound-root plan) | goes to |
| --- | --- | --- |
| c1 | `g1: l=2, u=5, p=pa` | gs |
| c2 | `g2: l=3, u=9, p=pa` | gs |
| c3 | none | rest |

One match: `gs = [c1, c2]`, `l = [2, 3]`, `u = [5, 9]`, `p = [pa, pa]`,
`rest = [c3]`. Had `c2` a second `Global` member, it would have two rows and
`Collect` would emit two matches.

**`:flatten`.** A tagged rule's `CollectSpec::flatten` makes the assembly run at each
of the node's flattened views (`crate::flatten::views_u64`) and union the matches as
a set (`seq_collect::assemble_views`), under the node's match bound. Each view is
canonized by the one normalization (`nary_canon::normalize`, §5.2). A match is
kept by the demand rule: for some opening tree giving its view, every leaf of the
tree directly holds a class that a filter or a simple item takes, that is, one the
bare sequences do not hold (§7.5, "Flattened Matching"). A view bound counts as
a skipped node, as the match bound does. Filter bases and simple items are plain
patterns, so no sub-query is flattened.

**Snapshot.** Every class comparison, `ByRepr` probe, and child canonicalization
reads the round's snapshot (`IndexStore::repr`, §7.4). Sequence rules are
matched in each round, on the same snapshot as the ordinary rules, as
entries of the rule list (`saturate::Rule::Sequence`), after the round's ordinary rules.

**Application** (`seq_engine::apply_rules`). Every rule is matched and every guard
read before any right-hand side is built. The matches are applied in (root node,
rule) order, the order the reference applies them in.

**Pull engine.** `MatchIterator`'s `Collect` arm fails the branch; no caller hands
it a sequence query.

### The match representation

`Match` (§7.4) holds node bindings, literal values, and three rest pools
(`seq_pool`, `set_pool`, `mset_pool`) with a span per rest variable. A sequence match
also needs per-element values of the filter's pattern variables, which are classes
(`p`) or literal values (`l`, `u`):

| binding | where it lives |
| --- | --- |
| `gs`, `rest` (children) | `set_pool` (ACI), `mset_pool` (AC), or `seq_pool` (A), one span each |
| `p` (class column) | `seq_pool`, one span, parallel to `gs` |
| `l`, `u` (literal columns) | `lit_seq_pool: Vec<Cfg::V>`, one span each, parallel to `gs` |
| `K0`, `K1` (`:let`) | literal-value slots, filled before the guards run |

For the example, with spans written `[start, len)`:

```
set_pool     = [c1, c2 | c3]          gs → [0,2)   rest → [2,1)
seq_pool     = [pa, pa]               p  → [0,2)
lit_seq_pool = [2, 3 | 5, 9]          l  → [0,2)   u  → [2,2)
lit_vals     = [K0 = 2, K1 = 5]
```

Columns of one filter share the filter's order, so element `j` of `gs`, `l`, `u`, and
`p` is one row. `MatchSet` stores the literal columns. The `Collect` handler writes
each match into the pools (`fill`), continues, and restores the pools and node
scalars (`Match::mark`/`restore`, `unfill`) on every path.

### Guards and `:let`

`:let` binds, after the match and in order, each expression into a literal-value
slot; a binding may reference earlier ones. The guards' expressions gain reductions
and element-wise application over sequence columns. A reduction with no value makes
the match fail, as a false guard does. Because the guards read the whole match, a
sequence rule's `:let` and `:when` run after `Step::Collect`; the sub-queries' own
guards, if their patterns have any, run inside them.

In the example: `K0 = min [2, 3] = 2`; `K1 = 2 + min [5−2, 9−3] = 5`; `(>= 2 2)` and
`(> 5 0)` hold.

### The right-hand side

The resolver turns the right-hand side, `:let`, and `:when` into a tree (`SeqRhs`,
`seq_rhs.rs`) whose leaves are the match layout's ids (`VarId`, `LitValVarId`,
`MultVarId`, `SeqVarId`, `LitSeqVarId`, a filter's `ColRef`s); the evaluator reads
any `MatchView`. Comprehension binders are indices into per-evaluation vectors,
saved before each row and restored after it on every path. The ordinary rules'
instantiation (`apply.rs`) is unchanged, which keeps their hot path as it was.

- **Element comprehension over a filter.** `..{ body for g in gs }` iterates `gs`'s
  span and, for element `j`, binds `g` to the child and each pattern variable to its
  column's element `j`.
- **Tuple comprehension over a primitive's result.**
  `..{ body for (q a b) in (union-by p l u) }` evaluates the primitive into a table
  of rows (classes and literals) and iterates it with the same per-column binding.
- **Reductions and element-wise primitives**, as in the guards.

The resolver also enforces the comprehension bracket per target kind, rejects a bare
binder over AC children, records each splice across kinds in `SeqRhs::plan`, and
warns where a result depends on class ids (`SeqRhs::warnings`). An application wider
than `seq_rhs::MAX_WIDTH` (2^20 children) is not built.

The example's right-hand side, for the match above:

```
(And (Global (Interval 2 5)
             (And (Global (Interval 0 0) pa)      ; element 1: l−K0 = 0, u−K1 = 0
                  (Global (Interval 1 4) pa)))    ; element 2: 3−2 = 1, 9−5 = 4
     c3)                                          ; ..rest
```

which is merged into `n`'s class with `Justification::Rewrite { rule_id }`.

### Semi-naive evaluation

Sequence rules follow the saturation strategy: under `--use-semi-naive` the ordinary
rules and the sequence rules are both semi-naive, and under naive saturation (the
default) both are naive. There is one switch. The design is
`doc/goal-semi-naive-sequence-rules.md` in the ltl-eqsat repository.

**What may change.** A root node's matches can differ from the previous round's only
if the node is in the delta index, or one of its child classes (under `:flatten`, a
class in one of its views) is affected. A class is affected when it is the root class
of an item sub-query's delta row (the sub-query run in its §9.2 variants
against the round's delta), or the class of a node subsumed this round
(`EGraph::subsume` logs the node in the touched log, and the semi-naive driver passes
the subsumed nodes in `RoundDelta` to the round's sequence batch,
`saturate::apply_sequence_batch`). Class merges need no separate case:
merges log the absorbed members, so a member whose class changed is in the delta and
its rows are delta rows. `Δ_collect` is the delta's root nodes together with the
root-operator parents of the affected classes (under `:flatten`, the climb from the
affected classes and from every touched node's class). `seq_engine::delta_nodes`
computes it, and `tests/seq_semi_coverage.rs` pins it as the oracle: on 400 random
programs with merges, new nodes, subsumptions, and nesting, no root node outside it
gains a match.

A sequence rule is a grouped aggregate, so its derivative is a guard followed by a
full recompute of each affected group (Alvarez-Picallo et al., "Fixing incremental
computation", arXiv:1811.06069, §4.3). At a node in `Δ_collect` the assembly runs in
full and emits all that node's matches, new or not, the conservative superset
§9.2 allows.

**Three strategies, chosen per rule and round.**

- *Naive*: the plan above.
- *Semi-filter*: naive's rows and candidates; a candidate is assembled only if it is
  in the delta or one of its child classes is affected (`seq_engine::Keep`, applied at
  the `Collect` step by `ematch::collect_admits`). Under `:flatten` the test descends
  from the candidate through the classes its views splice, bounded by
  `flatten::MAX_WORK`; a descent over the bound keeps the candidate.
- *Semi-enumerate*: the nodes of `Δ_collect` listed beforehand
  (`seq_engine::parents_bounded`), assembled under the root drive with probed rows,
  so no filter's rows are materialized.

Every strategy assembles through `collect_with`, and semi-filter's nodes are a subset
of naive's candidates. On the random programs of the coverage tests, semi-filter's
assembled nodes equal `Δ_collect` ∩ naive's candidates (706 of 1,442 offered nodes
assembled), and semi-enumerate's matches equal semi-filter's.

**The choice is made before the work it decides about.** `semi_estimate` computes,
from bucket lengths only:

- `guard` (a field of `SemiEstimate`): over every item sub-query except an
  `every_class` one, and each of its join atoms, the variant's
  driver estimate (the least, over the sub-query's join atoms, of the atom's relation
  in that variant: delta, full ∖ delta, or full), plus `GUARD_SETUP = 4`
  node-assemblies per variant for the variant's plan, index, and query setup;
- `saving`: naive's assembly estimate (saturating, 0 for no candidates) times `1 − q`,
  where `q`, the expected
  fraction of candidates passing the test, is
  `min(1, (|delta ∩ ByOp(root)| + guard · fan) / |ByOp(root)|)` and `fan` is the
  root operator's mean `by_contains` fan-out, rounded up and at least 1.

The guard runs only if `guard < saving` (`SemiEstimate::guard_pays`). Semi-enumerate is taken when the
delta's root nodes number at most `|ByOp(root)| / ENUMERATE_DIVISOR` (4), and
`parents_bounded` charges each `by_contains` bucket's length before walking it and
gives up over its budget, so a hub class falls through to semi-filter. The estimate
reads the `Collect` plan the rule's query already built, so it schedules nothing.

**Measured** (`tools/measure_seq_semi.sh`, tables in
`results/seq_semi_step6_strategy_{before,after,final}.tsv`). Without `GUARD_SETUP`,
the 1,172 specifications chose a semi-naive strategy in 1,539 of 11,555 rule rounds and those
rounds cost 1.7 to 2.0 times naive: a guard variant costs about 28 µs even when it
returns no row, against about 6 µs per node assembled. With it, every rule round on
those specifications chooses naive; the remaining overhead of the estimate was measured at
1.062 times naive after the estimate stopped rescheduling the rule's sub-queries,
against a run-to-run variance of 0.971 between two naive runs. Naive's filter drive
is already selective on them (about 0.16 candidates per round out of about 9
root nodes), so semi-naive has no saving to take there. A hub case (a class with
10,000 conjunction parents and one subsumed row) declines the guard; it measured
exactly naive's 10,002 match steps. The test `a_hub_class_chooses_semi_filter`
(`tests/seq_semi_estimate.rs`) asserts that the choice is not semi-enumerate and that the
run stays within twice naive's match steps; the 10,002 is printed, not asserted.

**Fallback.** When an item sub-query needs the naive path (`needs_naive_match`, for
example a global in an element position) or has no join atom, the rule is matched
naively.

### Soundness

A match is relative to the round's snapshot, including its negative part: the rest
children had no row then. A later merge can give a rest child a matching member, and
the equality the rule added is then justified only if the rule's validity did not
depend on that absence. The rules of `rules/mltl_nary_decl.egg` do not: they read
the filters' children and pass the rest through unchanged, and each is derived from
pairwise rules. A rule valid only because a rest child is not of a filter's shape
(one guarded by `(== (count gs) 0)`, say) is unsound in an e-graph in general. The
checker cannot decide this.

### Proofs

Unions made by a sequence rule carry `Justification::Rewrite { rule_id }`, as for
ordinary rules; the rule is registered as an ordinary rule.

### Tests

- **Reference differential** (`tests/seq_differential.rs`): the engine against the
  reference and against `collection::pass` (the retired matcher, kept as a test
  reference), with every forced plan (root drive, filter drive with each access
  path), under naive and semi-naive saturation. Plan invariance is the same match set
  under all of them.
- **Reference semantics** (`tests/seq_reference.rs`) and `:flatten` against brute
  force (`tests/flatten_differential.rs`).
- **Coverage** (`tests/seq_semi_coverage.rs`): `Δ_collect` covers every new match, on
  400 random programs and one program per cause, and the strategies select its nodes.
- **Estimates** (`tests/seq_semi_estimate.rs`): each estimate against brute-force
  counts; a delta equal to the full index chooses naive; a one-node delta chooses the
  guard; the hub case; shared rows.
- **Non-emptiness analysis**: for each filter the analysis marks, the reference's
  part-2 matches fail the rule's `:let` and `:when`.
- **Typing and right-hand side**: one rejection per misuse of a sequence, with its
  message; comprehensions against the reference evaluator.
- **Reproduction**: the corpus figures (`results/seqpat_step4c_*`), naive and
  semi-naive, identical terms and byte-identical dumps between the two
  (`tools/semper_chain.sh`).

### Alternatives considered and rejected

- **A separate pass after each round** (the first design's `collection::pass`, "route 1").
  It visited every live node of each rule's root operator, rebuilt a member list per
  class, and read the live union-find rather than the round's snapshot, at
  `O(N + Σ members × pattern)` per round regardless of what changed. Replaced by the
  `Collect` atom on the round's snapshot. Route 1 and the engine build the same
  e-graph on all 1,172 specifications (`dump_canon.py`), so the pass is kept only as
  the test reference.
- **An after-round schedule for the engine** (`SEMPER_SEQ_SCHEDULE=after-round`). It
  matched sequence rules after each round of the ordinary rules, to reproduce route
  1's figures while the engine was checked. Retired on 2026-10-02 with the switch:
  with a round cap it stops at a different e-graph from in-round matching (18 of the
  1,172 specifications differ in e-graph, all at equal optimum memory), and nothing needs
  the reproduction any more.
- **A `Lookup::ByCandidates` and a `Step::CollectEmpty`.** The design first gave the
  candidates their own index family and part 2 its own step. A per-round bucket with a
  single reader, the step that computed it, is a list; the climb under `:flatten` is
  not a bucket intersection; and a separate part-2 step would duplicate the A parse.
  Both are done inside the `Collect` step.
- **The access path chosen per round by the cost model.** Materialization is what the
  filter drive needs to find its candidates, and a root drive has no candidates to
  materialize for, so the access path follows the drive.
- **Semi-naive by per-node seeded assembly, with a fraction α decided after the
  guard.** The first semi-naive version seeded the query's root with each node of
  `Δ_collect`, enumerated `Δ_collect` through `by_contains` fan-outs, and fell back to
  naive when `|Δ_collect| / |ByOp(root)|` exceeded α, a test made after the guard had
  run. It lost row materialization, added a query setup per node, and paid the guard
  before deciding: in-round semi-naive ran 2.29 times slower than naive. Replaced by
  the three strategies above, chosen before the work.
- **Comparing the guard with naive's whole estimate.** The decision first ran the
  guard when its estimate was below naive's total. §9.2's variants are disjoint
  (the atoms before the delta atom read full ∖ delta), so a delta equal to the full
  index leaves every variant but the first empty, and the guard costs about one naive
  sub-query run, which is less than naive's total. The first form would run the guard
  exactly when it saves nothing; the comparison is with the work it can save.
- **A separate switch for sequence rules** (`SEMPER_SEQ_SEMI`). It made sequence
  rules semi-naive inside an otherwise semi-naive run. Removed on 2026-10-02 by the
  user's decision: `--use-semi-naive` covers every rule.
- **A literal-sequence comprehension with tuples of names everywhere.** A
  comprehension over a filter binds the pattern's own variables, so it needs no tuple;
  tuples remain only for primitives that return rows (decided 2026-09-29).

### Collection rules (superseded)

This section records the first design for rewrites over every operand of an n-ary
node at once, and why each of its decisions was replaced. The language and the
engine that replaced it are the rest of §7.6. The first design's matcher survives as
`collection::pass`, which no command reaches: it is the reference
`tests/seq_differential.rs` checks the engine against.

#### The problem it addressed

A pairwise rule over an AC operator, such as merging two windows of `G` over the
same operand, fires `k(k-1)/2` times on a `k`-ary conjunction and nests one level per
firing. The n-ary form (merge every mergeable window at once) needs a pattern that
filters the operands by shape, reads their payload, aggregates, and rebuilds each
one. The remainder `..rest` binds the operands but cannot look inside them. The rules
were introduced to replace a Rust driver (`examples/mltl_nary.rs`) that applied three
n-ary MLTL rewrites between saturation rounds.

#### The first design, and what replaced each part

| decision | first design | replaced by | why |
| --- | --- | --- | --- |
| syntax | `(each name pattern)` items | filters `(..name pattern)`, with `:except`, multiplicities, and bare sequences anywhere under A | `each` named no sequence variable for the rest of the rule to use; it is now an ordinary operator name |
| member choice | of the members of a child class that match, the one with the smallest node id | every member that matches gives a row, and every row a match | the smallest id depends on allocation order, so the match set depended on the order rules ran in |
| maximality | one match per node, each operand to the first collection in written order | the assignments of `doc/sequence-patterns.md`, Semantics, enumerated, with maximal runs only under A | written order made a rule's matches depend on the order of its items |
| roots | ACI only, a suffix rest, no ordinary operand beside the collections | A, AC (with multiplicities), and ACI roots; simple items beside filters | the MLTL rules needed AC multiplicities and A runs |
| schedule | one pass after each round of the ordinary rules, over the live graph | the `Collect` atom, matched in the round on the round's snapshot | the pass cost `O(N + Σ members × pattern)` per round regardless of what changed, and could not be semi-naive |
| matching | a pass over every node of the root operator | compiled joins with a filter drive (§7.6, "Choosing where to start") | at 2 rounds over the 1,172 specifications the filter drive assembles at 1.5% to 2.3% of the root operator's nodes |

#### Evidence the first design gave

With `rules/mltl_nary_decl.egg` (the ltl-eqsat repository): the four check programs
passed with the rules and failed without them; on the 17 NASA specifications of
[JR26](11-extraction.md#references) at 2, 3, and 4 rounds the e-graph sizes and memory figures equalled the driver's;
over all 1,172 at 2 rounds every figure equalled the driver's (mean memory reduction
10.80%), and all extracted terms were equivalent to their inputs under the settled
finite-trace semantics. The engine of §7.6 reproduced these figures before the
schedule moved into the round, and builds the same e-graph as `collection::pass` on
all 1,172 (`dump_canon.py`).

## 7.7 Rule Application and RHS Evaluation

### From Matches to Mutations

§7.3 to §7.5 describe how the engine finds matches (read-only).
This section describes what happens with each match: the RHS is
evaluated against the binding environment, producing new e-nodes
and merges. Within execution of a prepared rule, mutation is confined to
action/RHS evaluation; command execution and rebuild can also mutate the
e-graph outside that phase.

Sortcheck resolves the RHS to `RRhsTerm`. When the interpreter installs the
checked rewrite or rule, `compile_rhs` converts that resolved tree to
`RhsOp`. Each match then drives a bottom-up evaluation of the compiled tree,
building terms and interning literal values as needed.

### Compiled RHS

```rust
enum RhsOp<O, V> {
    FetchNode(RhsNodeRef),        // a query variable or a comprehension local
    Lit(O, V),
    LitVar(O, LitValVarId),
    MultVar(O, RhsMultRef),
    App { op: O, args: Vec<RhsArg<O, V>> },
    PrimApp { op: O, args: Vec<RPrimArg<O, V>> },
    FetchGlobal(GlobalVarId),
}

enum RhsArg<O, V> {
    One(RhsOp<O, V>),
    OneMult { body: Box<RhsOp<O, V>>, mult: ResolvedMultExpr },
    SpliceSeq(SeqVarId),
    SpliceSet(SetVarId),
    SpliceMset(MsetVarId),
    SetComp { body, var, source, filter },
    MsetComp { body, mult, var, mult_var, source, filter },
    SeqComp { body, var, source, filter },
}
```

| Variant | Purpose |
|---------|---------|
| `FetchNode` | Read bound e-node id from match environment |
| `Lit` | Intern a known literal value and create its literal node |
| `LitVar` | Reconstruct `@sort(val)` literal node from a bound `LitValVarId` |
| `MultVar` | Reconstruct an `@i64(k)` node from a bound multiplicity |
| `App` | Build `(op args...)` via `eg.add()`, or `eg.add_mset()` under AC |
| `PrimApp` | Evaluate a primitive op on bound literal values or multiplicities, intern result |
| `FetchGlobal` | Fetch a global binding by `GlobalVarId` and canonicalize it at evaluation |

### Evaluation

```rust
fn eval(op: &RhsOp, env: &mut RhsEnv, eg: &mut EGraph, model: &M, globals)
    → Result<G, EvalError> {
    Ok(match op {
        FetchNode(node) => eg.find(env.node(node)),
        Lit(lit_op, value) =>
            eg.add_lit(lit_op, eg.lits_mut().intern(value.clone())),
        LitVar(lit_op, vid) => eg.add_lit(lit_op, env.query.get_lit_val(vid)),
        App { op, args } => {
            let mut children = Children::for_kind(kind(op)); // counted under AC
            for arg in args {               // A operators: eval_seq_args
                eval_arg(arg, env, eg, model, globals, &mut children)?;
            }
            if children.is_empty() && variadic(op) && eg.unit_node(op).is_none() {
                return Err(EvalError::new(NO_VALUE, ..));  // §7.7, occurrences
            }
            match children {
                Counted(cs) => eg.add_mset(op, &cs)?,   // MultOverflow is an error
                Positional(ids) | Distinct(ids) => eg.add(op, &ids),
            }
        }
        PrimApp { op, args } => eval_prim(op, args, env, eg, model)?, // None → EvalError
        // MultVar and FetchGlobal are direct reconstructions/lookups.
    })
}
```

`eval_arg` splices rest bindings, evaluates optional multiplicity
expressions, and handles the three comprehension kinds. `ChildVec` is a
`SmallVec` with inline capacity 16 and can spill to the heap for larger RHS
child lists.

### Occurrences and empty applications

A count is a number of occurrences. Every check on counts follows from that reading, so
that no written term or pattern lacks a meaning:

- **An omitted count is 1, and a written count is at least 1.** `x:0` says the element does
  not occur, so it is refused wherever it is written: in a ground term (sortcheck), in a
  pattern (`FlatMult::Exact(0)`), and as a literal count on a right-hand side
  (`zero_count_message`, `resolve.rs`). The message says to omit the element.
- **A computed count of 0 drops the child.** A right-hand-side multiplicity expression that
  evaluates to 0 omits its element without evaluating it (`eval_arg`, `apply.rs`); the
  occurrence count of the other children is unchanged.
- **An empty application means the identity.** `(And)` denotes the operator's `:identity`,
  so it is accepted only for an AC or ACI operator that declares one. Written without one, it
  is refused: in a ground term by sortcheck, on a right-hand side by resolution
  (`empty_application_message`), and as a pattern by `check_min_children`, since a stored
  node is never empty. When every child of a right-hand-side application is dropped at run
  time and the operator has no identity, the term is not built: the action returns
  `NO_VALUE` and is skipped, and the run warns with the number of skipped actions
  (`count_no_value`, `interpret.rs`).
- **ACI takes no counts.** A set holds each element once, so a count under an ACI operator
  is refused in ground terms and on right-hand sides (`set_count_message`, `sortcheck.rs`);
  the message points to AC.
- **Repeated elements reduce.** Writing an element twice is not a count, and it is
  accepted: `(And a a a)` canonizes to `(And a)` (deduplication, §5.2), which collapses to
  `a`; under AC, `(Add a a)` is `(Add a:2)`.

### Actions

```rust
enum CompiledAction<O, V> {
    Union(RuleId, RhsOp<O, V>, RhsOp<O, V>),
    Insert(RhsOp<O, V>),
    Set { func: O, args: Vec<RhsOp<O, V>>, value: RhsOp<O, V> },
    Subsume(VarId),
}
```

For rewrites, `Union(rule_id, FetchNode(root_vid), compiled_rhs)` evaluates
the RHS, then unions the result with the matched LHS root. `rule_id` labels the
justification when proof logging is enabled.

For datalog rules, `Insert(App { op, args })` builds the term and
insert it into the e-graph.

`Set { func, args, value }` is parsed, but resolution refuses it when the rule is
installed ("the `set` action … is not implemented; write the value as a term and use
`union` instead", `resolve_action`), so the `todo!` in `apply_action` is unreachable from a
program. Lattice-valued function semantics are future work.

For subsumption, `Subsume(root_vid)` marks the matched node as
subsumed so it is excluded from future matches.

### Primitive Op Evaluation

When the RHS contains a `PrimApp` (primitive op like `IBig::+`):

```rust
PrimApp { op, args: [x, y] } => {
    let x_val = eg.lits().get(match.get_lit_val(x));
    let y_val = eg.lits().get(match.get_lit_val(y));
    let prim = &model.ops()[op];
    let result_val = (prim.eval)(&[&x_val, &y_val])   // Option: None is outside the domain
        .ok_or_else(|| EvalError::new(prim.name, ..))?;
    let vid = eg.intern_lit(result_val);  // intern NEW value
    eg.add_lit(lit_op, vid)
}
```

This is when a primitive RHS result is interned for a firing rule. It is not
the only interning site in the program: ground-term construction and an
algebraic identity declaration can also intern literals. LHS matching and LHS
predicate guards do not intern (Chapter 10).

### Filter Guards

Filters inside RHS comprehensions are RHS terms, not LHS `:when` predicates.
Resolution accepts only forms guaranteed to produce a concrete literal node:
literal constants, reconstructed literal or multiplicity values, and primitive
applications. Ordinary e-node variables, globals, and applications are
rejected. In particular, `if (Keep x)` is not an existence query over the
e-graph; that condition belongs in the LHS query.

Accepted filters are evaluated through the same `eval` path as the body and
may intern their literal result before its truth value is tested:

```rust
let id = eval(filter, env, eg, model, globals)?;
fn check_filter_truthy(eg, _model, id) → bool {
    M::is_truthy(eg.get_lit_val(id).expect(
        "RHS invariant violated: comprehension filter did not evaluate to a literal node"))
}
```

Each sequence, set, or multiset comprehension first clones its source slice
with `.to_vec()`. This transient copy permits rebinding local variables and
interning filter/body results while iterating; the implementation is not
allocation-free.
LHS `:when` guards remain read-only and are described in §7.3 to §7.5.

---
[← Ch 6: AC Congruence Closure](06-ac-congruence-closure.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Indexes and Leapfrog →](08-indexes-and-leapfrog.md)
