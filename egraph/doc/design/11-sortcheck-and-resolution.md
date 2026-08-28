# Chapter 11 — Sortchecking and Resolution

[← Ch 10: Surface Language](10-surface-language.md) · [Table of Contents](00-table-of-contents.md) · [Ch 12: Rule Application →](12-rule-application.md)


## The Three-Phase Pipeline

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

## `sortcheck_program`

Processes commands sequentially against a live EGraph. Declaration commands
register sorts and operators; an AC identity declaration also builds its
ground unit term at this point. Pattern commands are flattened and resolved.
Ordinary ground terms are classified and sort-checked without being built.

### Algebraic Signature Invariants

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

## `flatten_surface` — Op-Kind Validation

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

## `resolve` — Name Resolution

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

`MatchShape` records the count of each variable kind, serving as the single
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

### Predicate Guards

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

### Global Name Resolution

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
`RhsOp::FetchGlobal(gid)`: apply reads the stored binding and canonicalizes it
with `eg.find`. The binding array itself is not continuously rewritten to
canonical representatives.

### RHS Collection Sorts

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

## `check_term` — Ground Term Sort-Checking

Walks `Term` bottom-up:
1. Look up op → `OpId`, get arg sorts and return sort.
2. Recursively check children → get child sorts.
3. Verify child sort matches declared arg sort.
4. Return `CTerm::App { op, sort, children }`.

For globals: look up in `GlobalCtx` → `CTerm::Global(name, sort)`.
For literals: classify via `LitModel::parse_as`/`parse_any` →
`CTerm::Lit(value, sort)`.

## `CCommand` / `CTerm`

```rust
pub enum CTerm<O, S, L> {
    Lit(L, S),
    App { op: O, sort: S, children: Vec<CTerm<O, S, L>> },
    Global(String, S),
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
    Rewrite {
        query: ResolvedQuery,
        rhs: RRhsTerm,
        root_vid: VarId,
        subsume: bool,
        ruleset: Option<RulesetId>,
    },
    Rule {
        query: ResolvedQuery,
        actions: Vec<ResolvedAction>,
        ruleset: Option<RulesetId>,
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

## `GlobalCtx`

```rust
pub struct GlobalCtx<S, G = ()> {
    index: HashMap<String, GlobalVarId>,
    sorts: Vec<S>,
    bindings: Vec<G>,
}
```

During sortcheck: `G = ()` (no runtime bindings, only sorts).
During interpretation: `G = ENodeId` (actual e-class bindings).

`GlobalVarId` indices are assigned in command order. Since sortcheck
and the interpreter process commands in the same order, the indices
match between the two phases.

---
[← Ch 10: Surface Language](10-surface-language.md) · [Table of Contents](00-table-of-contents.md) · [Ch 12: Rule Application →](12-rule-application.md)
