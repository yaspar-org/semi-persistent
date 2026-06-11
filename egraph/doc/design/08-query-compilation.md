# Chapter 8 — Query Compilation and Scheduling

[← Ch 7: Leapfrog Triejoin](07-leapfrog.md) · [Table of Contents](00-table-of-contents.md) · [Ch 9: Pattern Matching →](09-pattern-matching.md)


## The Full Pipeline

A rule goes from surface syntax to fired action through a pipeline
that cleanly separates the pattern language from the execution
machinery. This separation is critical: it allows the scheduler to
choose any variable ordering (top-down, bottom-up, middle-out)
based on runtime cardinalities.

```
Parse       → Vec<SurfacePattern>     (recursive, string-named)
Flatten     → Vec<Atom>               (flat constraints, synthetic vars)
Resolve     → ResolvedQuery           (dense typed ids, sorts checked)
Schedule    → QueryPlan               (ordered execution steps)
Execute     → Iterator<Match>         (DFS backtracking, Chapter 9)
Apply       → mutations               (union, insert, set — Chapter 12)
```

Stages 1–3 are compile-time (once per rule). Scheduling runs once per
saturation cycle (cardinalities change as the e-graph grows). Execution
runs per-match, lazily.

## Atom Types (`RAtom`)

Flattening walks the pattern tree, assigns synthetic variable names to
nested nodes, and produces flat atoms. Each atom is one relational
constraint on the e-graph. The variants cover the full spectrum of
operator kinds and matching shapes; the scheduler decides in what
order to apply them.

| Variant | Matches |
|---------|---------|
| `Plain { node, op, children }` | Fixed-arity node with specific op |
| `LitBind { node, op, val }` | Literal node, bind value to variable |
| `Lit { node, op, value }` | Literal node with specific known value |
| `Eq(a, b)` | Two variables in same e-class |
| `EqGlobal(local, global)` | Variable equals a global binding |
| `AExact / APrefix / ASuffix / ABoth` | A-node with optional rest vars |
| `ACExact / ACSub` | AC-node exact or sub-multiset |
| `ACIExact / ACISub` | ACI-node exact or subset |

## The Scheduling Algorithm

The scheduler must be free to bind variables in any order. Consider
`(foo x (bar x y) (baz y))`: if `bar` is rare, start there; if `baz`
is rare, start there. A fixed top-down traversal would be stuck with a
bad plan when the rare operator isn't at the root.

Two alternating phases in a loop:

### Phase A: Eager Pass (fixpoint)

Process atoms that are "free" given current bindings (they add no
fan-out, only constrain):

- `Eq(a, b)` with both bound → `CheckEq`
- `Eq(a, b)` with one bound → `CopyBinding`
- `EqGlobal` with local bound → `CheckEqGlobal`
- `Plain/LitBind` with node already bound: re-join within e-class.

### Phase B: Cost-Based Selection

Pick the cheapest unprocessed atom:

```
cost(Plain { op, children }) = card(op) >> bound_children_count
cost(LitBind { op, .. })     = card(op)
cost(A/AC/ACI variants)      = card(op)
cost(Lit)                     = 1
cost(Eq/EqGlobal)             = 0
```

Emit the selected atom via `emit_atom` (Join + ExtractChild steps),
then return to Phase A.

## E-Class–Aware Re-Join

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

## Execution Steps

| Step | Semantics |
|------|-----------|
| `Join { target, lookups, atom_id }` | Leapfrog intersection, bind target to each result. `atom_id` identifies which query atom this join scans — used by semi-naive evaluation to delta-restrict one atom at a time (Chapter 18); ignored by naive matching |
| `ExtractChild { target, parent, pos }` | Read child at position from parent node |
| `ExtractLitVal { node, val }` | Extract literal value id from node |
| `CheckChildEq { parent, pos, expected }` | Verify child equals expected (by find) |
| `CheckEq { a, b }` | Verify find(a) == find(b) |
| `CheckEqGlobal { local, global }` | Verify find(local) == find(globals[global]) |
| `CopyBinding { target, other }` | target = find(other) |
| `ExpandA { node, children, pre, suf }` | Enumerate subsequence matches |
| `DecomposeAC { node, elems, rest, idempotent }` | Enumerate sub-multiset matches |
| `DecomposeACI { node, elems, rest }` | Enumerate subset matches |

> **Note**: `CheckLitEq` and `EvalLit` do not exist as `Step` variants.
> Literal equality checks are handled by `ExtractLitVal` + `CheckEq`.
> Primitive op evaluation happens during RHS application (Chapter 12),
> not during LHS matching.

## Example Plan

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

---
[← Ch 7: Leapfrog Triejoin](07-leapfrog.md) · [Table of Contents](00-table-of-contents.md) · [Ch 9: Pattern Matching →](09-pattern-matching.md)
