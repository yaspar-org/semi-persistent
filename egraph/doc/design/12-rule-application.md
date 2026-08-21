# Chapter 12 — Rule Application and RHS Evaluation

[← Ch 11: Sortcheck and Resolution](11-sortcheck-and-resolution.md) · [Table of Contents](00-table-of-contents.md) · [Ch 13: Literal Model →](13-literal-model.md)


## From Matches to Mutations

Chapters 8–9 describe how the engine finds matches (read-only).
This chapter describes what happens with each match: the RHS is
evaluated against the binding environment, producing new e-nodes
and merges. Within execution of a prepared rule, mutation is confined to
action/RHS evaluation; command execution and rebuild can also mutate the
e-graph outside that phase.

Sortcheck resolves the RHS to `RRhsTerm`. When the interpreter installs the
checked rewrite or rule, `compile_rhs` converts that resolved tree to
`RhsOp`. Each match then drives a bottom-up evaluation of the compiled tree,
building terms and interning literal values as needed.

## Compiled RHS

```rust
enum RhsOp<O, V> {
    FetchNode(VarId),
    Lit(O, V),
    LitVar(O, LitValVarId),
    MultVar(O, MultVarId),
    App { op: O, args: Vec<RhsArg<O, V>> },
    PrimApp { op: O, args: Vec<RPrimArg> },
    FetchGlobal(GlobalVarId),
}

enum RhsArg<O, V> {
    One(RhsOp<O, V>),
    OneMult { body: RhsOp<O, V>, mult: ResolvedMultExpr },
    SpliceSeq(SeqVarId),
    SpliceSet(SetVarId),
    SpliceMset(MsetVarId),
    SetComp { body, var, source, filter },
    MsetComp { body, var, mult_var, source, filter },
    SeqComp { body, var, source, filter },
}
```

| Variant | Purpose |
|---------|---------|
| `FetchNode` | Read bound e-node id from match environment |
| `Lit` | Intern a known literal value and create its literal node |
| `LitVar` | Reconstruct `@sort(val)` literal node from a bound `LitValVarId` |
| `MultVar` | Reconstruct an `@i64(k)` node from a bound multiplicity |
| `App` | Build `(op args...)` via `eg.add()` |
| `PrimApp` | Evaluate a primitive op on bound literal values or multiplicities, intern result |
| `FetchGlobal` | Fetch a global binding by `GlobalVarId` and canonicalize it at evaluation |

## Evaluation

```rust
fn eval(op: &RhsOp, match: &mut Match, eg: &mut EGraph, model: &M) → G {
    match op {
        FetchNode(vid) => eg.find(match.get(vid)),
        Lit(lit_op, value) =>
            eg.add_lit(lit_op, eg.intern_lit(value.clone())),
        LitVar(lit_op, vid) => eg.add_lit(lit_op, match.get_lit_val(vid)),
        App { op, args } => {
            let mut children = SmallVec::new();
            for arg in args {
                eval_arg(arg, match, eg, model, &mut children);
            }
            eg.add(op, &children)
        }
        PrimApp { op, args } => {
            let result = model.eval(op, resolved_values(args, match, eg));
            let value_id = eg.intern_lit(result);
            eg.add_lit(return_sort_lit_op(op), value_id)
        }
        // MultVar and FetchGlobal are direct reconstructions/lookups.
    }
}
```

`eval_arg` splices rest bindings, evaluates optional multiplicity
expressions, and handles the three comprehension kinds. `ChildVec` is a
`SmallVec` with inline capacity 16 and can spill to the heap for larger RHS
child lists.

## Actions

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

`Set { func, args, value }` is parsed and compiled, but execution currently
reaches `todo!("lattice set not yet implemented")`. Lattice-valued function
semantics are future work; this variant is not a usable runtime feature.

For subsumption, `Subsume(root_vid)` marks the matched node as
subsumed so it is excluded from future matches.

## Primitive Op Evaluation

When the RHS contains a `PrimApp` (primitive op like `IBig::+`):

```rust
PrimApp { op, args: [x, y] } => {
    let x_val = eg.lits().get(match.get_lit_val(x));
    let y_val = eg.lits().get(match.get_lit_val(y));
    let result_val = model.eval(op, &[x_val, y_val]);
    let vid = eg.intern_lit(result_val);  // intern NEW value
    eg.add_lit(lit_op, vid)
}
```

This is when a primitive RHS result is interned for a firing rule. It is not
the only interning site in the program: ground-term construction and an
algebraic identity declaration can also intern literals. LHS matching and LHS
predicate guards do not intern (Chapter 13).

## Filter Guards

Filters inside RHS comprehensions are RHS terms, not LHS `:when` predicates.
They are evaluated through the same mutating `eval` path as the body and can
intern literals or build e-nodes before their truth value is tested:

```rust
fn check_filter_truthy(guard: &RhsOp, match, eg, model) → bool {
    let id = eval(guard, match, eg, model);
    eg.get_lit_val(id).map(|v| model.is_truthy(v)).unwrap_or(false)
}
```

Each sequence, set, or multiset comprehension first clones its source slice
with `.to_vec()`. This transient copy permits rebinding the loop variable and
mutating the e-graph while iterating; the implementation is not allocation-free.
LHS `:when` guards remain read-only and are described in Chapters 8–9.

---
[← Ch 11: Sortcheck and Resolution](11-sortcheck-and-resolution.md) · [Table of Contents](00-table-of-contents.md) · [Ch 13: Literal Model →](13-literal-model.md)
