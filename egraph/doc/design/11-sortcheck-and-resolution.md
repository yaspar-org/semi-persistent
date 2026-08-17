# Chapter 11 — Sortchecking and Resolution

[← Ch 10: Surface Language](10-surface-language.md) · [Table of Contents](00-table-of-contents.md) · [Ch 12: Rule Application →](12-rule-application.md)


## The Three-Phase Pipeline

The engine processes programs in three phases. This separation is not
incidental; it ensures that the interpreter never does string
lookups or sort inference. By the time a command reaches the
interpreter, every name is a dense id and every sort has been checked.

```
source → parse (parser.rs) → Vec<SurfaceCommand>
       → sortcheck (sortcheck.rs) → Vec<CCommand<OpId, SortId, L>>
       → interpret (interpret.rs) → execute against EGraph
```

## `sortcheck_program`

Processes commands sequentially against a live EGraph. Declaration
commands register sorts/ops. Pattern commands are flattened and
resolved. Ground terms are sort-checked.

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

Invalid combinations produce clear error messages with spans.

One form is recognized before the table, by the operator name. **`(= p q)`, the
root-binding form**: both subpatterns flatten as they would alone, and one
`Atom::Eq` constrains their roots to one e-class. The name `=` is reserved rather
than looked up in the registry, so a declaration cannot shadow the form and
silently change what an existing `(= …)` means. The idiomatic use is `(= v pat)`,
which names `pat`'s root: the left side is a bare variable, so the `Eq` costs one
`CopyBinding` once `pat`'s root is bound. Repeating the name across conjuncts is
the ordinary non-linear case, and it is how a rule states that two patterns share
a root rather than forming a cross product.

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

Non-linear variables (same name in multiple atoms) are unified:
the first occurrence binds, subsequent occurrences emit `CheckEq`.

An `Eq` atom also unifies the two sides' sorts, since they denote one e-class.
That is what gives `(rewrite (= v pat) rhs)` a sort to check `rhs` against: `v`
alone constrains nothing, and takes its sort from `pat`.

### Global Name Resolution

When the resolver encounters a name that exists in `GlobalCtx`, it
emits `PatVar::Global(gid)` instead of a fresh `VarId`. Child
positions in atoms use the `PatVar` enum:

```rust
pub enum PatVar {
    Local(VarId),
    Global(GlobalVarId),
}
```

A `PatVar::Global` child is always considered "bound" for scheduling
purposes. The scheduler can immediately use it for `ByChildPos`
lookups, constraining the join to nodes that have the global's
e-class as a child. When a global appears alone in a pattern (e.g.,
`(Add a x)` where `a` is a global), the resolver emits an
`EqGlobal(local_vid, gid)` atom that compiles to
`Step::CheckEqGlobal`. In the RHS, globals become
`RhsOp::FetchGlobal(gid)`, which reads the canonical representative
from the binding array at apply time.

## `check_term` — Ground Term Sort-Checking

Walks `Term` bottom-up:
1. Look up op → `OpId`, get arg sorts and return sort.
2. Recursively check children → get child sorts.
3. Verify child sort matches declared arg sort.
4. Return `CTerm::App { op, sort, children }`.

For globals: look up in `GlobalCtx` → `CTerm::Global(name, sort)`.
For literals: classify via `LitModel::parse` → `CTerm::Lit(value, sort)`.

## `CCommand` / `CTerm`

```rust
pub enum CTerm<O, S, L> {
    Lit(L, S),
    App { op: O, sort: S, children: Vec<CTerm<O, S, L>> },
    Global(String, S),
}

pub enum CCommand<O, S, L> {
    Decl(SurfaceDecl),
    Let(String, CTerm<O, S, L>),
    Insert(CTerm<O, S, L>),
    Union(CTerm<O, S, L>, CTerm<O, S, L>),
    Check(CTerm<O, S, L>),
    CheckEq(CTerm<O, S, L>, CTerm<O, S, L>),
    CheckNeq(CTerm<O, S, L>, CTerm<O, S, L>),
    Extract(CTerm<O, S, L>),
    Rewrite { query: ResolvedQuery, rhs: ResolvedRhs, root_vid: VarId, subsume: bool },
    Rule { query: ResolvedQuery, actions: Vec<ResolvedAction> },
    Run(u32),
    Push, Pop,
}
```

After sortcheck, every `CCommand` is fully resolved. The interpreter
needs no string lookups or sort inference.

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
