# Chapter 12 — Rule Application and RHS Evaluation

[← Ch 11: Sortcheck and Resolution](11-sortcheck-and-resolution.md) · [Table of Contents](00-table-of-contents.md) · [Ch 13: Literal Model →](13-literal-model.md)


## From Matches to Mutations

Chapters 8–9 describe how the engine finds matches (read-only).
This chapter describes what happens with each match: the RHS is
evaluated against the binding environment, producing new e-nodes
and merges. Rule application is the only phase that mutates the e-graph.

The RHS is compiled into a tree of `RhsOp` nodes during sortcheck.
At runtime, each match drives a walk over this tree, building terms
bottom-up and interning new literal values as needed.

## Compiled RHS

```rust
enum RhsOp<O, V> {
    FetchNode(VarId),
    Lit(O, V),
    LitVar(O, LitValVarId),
    App { op: O, args: Vec<RhsArg<O, V>> },
    PrimApp { op: O, args: Vec<LitValVarId> },
    FetchGlobal(GlobalVarId),
}

enum RhsArg<O, V> {
    One(RhsOp<O, V>),
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
| `Lit` | Create literal node from a known interned value |
| `LitVar` | Reconstruct `@sort(val)` literal node from a bound `LitValVarId` |
| `App` | Build `(op args...)` via `eg.add()` |
| `PrimApp` | Evaluate a primitive op on bound literal values, intern result |
| `FetchGlobal` | Fetch a global e-class binding by `GlobalVarId` |
```

## Evaluation

```rust
fn eval(op: &RhsOp, match: &Match, eg: &mut EGraph, model: &M) → G {
    match op {
        FetchNode(vid) => match.get(vid),
        Lit(lid) => {
            let val = eg.lits().get(match.get_lit_val(lid));
            let vid = eg.intern_lit(val.clone());
            eg.add_lit(lit_op, vid)
        }
        App { op, args } => {
            let children = args.flat_map(|arg| match arg {
                One(inner) => vec![eval(inner)],
                SpliceSeq(sid) => match.seq_slice(sid).to_vec(),
                SpliceSet(sid) => match.set_slice(sid).to_vec(),
                SpliceMset(mid) => expand_mset(match.mset_slice(mid)),
                SetComp { body, var, source, .. } =>
                    match.set_slice(source).iter()
                        .filter(|v| check_filter(...))
                        .map(|v| { bind var=v; eval(body) })
                        .collect(),
                // similar for MsetComp, SeqComp
            });
            eg.add(op, &children)
        }
    }
}
```

## Actions

```rust
enum CompiledAction<O, V> {
    Union(RhsOp<O, V>, RhsOp<O, V>),
    Insert(RhsOp<O, V>),
    Set { func: O, args: Vec<RhsOp<O, V>>, value: RhsOp<O, V> },
    Subsume(VarId),
}
```

For rewrites, `Union(FetchNode(root_vid), compiled_rhs)` evaluates
the RHS, then union the result with the matched LHS root.

For datalog rules, `Insert(App { op, args })` builds the term and
insert it into the e-graph.

For functional relations, `Set { func, args, value }` updates the
function table entry for `func(args...)` to `value`. This supports
semi-lattice merge semantics where the function's value is joined
with the new value rather than replaced.

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

New literal values are interned only when a rule fires, never during
matching (see Chapter 13).

## Filter Guards

`:when` guards are evaluated as boolean predicates on bound values.
They are read-only, with no interning and no e-graph mutation:

```rust
fn check_filter_truthy(guard: &RhsOp, match, eg, model) → bool {
    let id = eval(guard, match, eg, model);
    eg.get_lit_val(id).map(|v| model.is_truthy(v)).unwrap_or(false)
}
```

---
[← Ch 11: Sortcheck and Resolution](11-sortcheck-and-resolution.md) · [Table of Contents](00-table-of-contents.md) · [Ch 13: Literal Model →](13-literal-model.md)
