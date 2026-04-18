# Chapter 9 — Pattern Matching Execution

[← Ch 8: Query Compilation](08-query-compilation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 10: Surface Language →](10-surface-language.md)


## DFS Backtracking Engine

The query plan from Chapter 8 is executed by a recursive DFS engine.
Each step either binds a variable (and recurses to the next step) or
checks a constraint (and recurses on success, backtracks on failure).

The matching phase is read-only: it never mutates the e-graph or
interns new literal values. All mutations happen during RHS application
(Chapter 12). Matching sees a frozen snapshot of the e-graph, which is critical
for soundness.

## `Match` — Binding Environment

The binding environment separates variables by kind. Node bindings
(plain `VarId`s) use `Option<Cfg::G>` because variables may be unbound
at intermediate DFS steps. Multiplicity and literal-value bindings
are stored directly. The three "rest" kinds (sequence, set, multiset)
use a pool-plus-span indirection: the pool stores all elements
contiguously, and each variable holds a `(start, len)` span into
the pool. This layout avoids per-variable allocation even when
hundreds of rest bindings are live.

```rust
pub struct Match<Cfg: EGraphConfig> {
    nodes: Vec<Option<Cfg::G>>,       // VarId → e-node id (None if unbound)
    mults: Vec<Cfg::M>,               // MultVarId → multiplicity
    lit_vals: Vec<Cfg::V>,            // LitValVarId → literal value id
    seq_pool: Vec<Cfg::G>,            // all seq slices packed contiguously
    seq_spans: Vec<(u32, u32)>,       // SeqVarId → (start, len) into seq_pool
    set_pool: Vec<Cfg::G>,            // all set slices packed contiguously
    set_spans: Vec<(u32, u32)>,       // SetVarId → (start, len) into set_pool
    mset_pool: Vec<Cfg::C>,           // packed AC children (id + mult)
    mset_spans: Vec<(u32, u32)>,      // MsetVarId → (start, len) into mset_pool
}
```

The `MatchShape` (from resolution, Chapter 11) records the count of
each variable kind and is the single source of truth for the binding
environment layout.

## Subsequence Matching (A operators)

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
pool and the fixed elements as individual bindings, then recurses.

For exact match (`AExact`): children count must equal pattern count.
For prefix-only (`APrefix`): fixed elements at the start, rest at end.
For suffix-only (`ASuffix`): rest at start, fixed elements at end.

## Sub-Multiset Matching (AC operators)

`DecomposeAC` enumerates all ways to match pattern elements against a
subset of an AC-node's `(id, multiplicity)` children.

### Maximum Partition Semantics

Each pattern element must match a distinct child. The matcher
allocates multiplicities from the available pool:

1. For each pattern element, find a child whose remaining multiplicity
   satisfies the constraint.
2. Subtract the matched multiplicity from the child.
3. Remaining children (with remaining multiplicities) form the rest.

### Multiplicity Constraints

Each multiplicity variable has a global interval `[min, max]`
computed at compile time by intersecting all constraints:

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
the query is statically unsatisfiable and returns zero matches without
touching the e-graph.

## Subset Matching (ACI operators)

`DecomposeACI` enumerates all ways to match pattern elements against a
subset of an ACI-node's children (no multiplicities, since all counts
are structurally 1 due to idempotency).

Each pattern element must match a distinct child. The rest variable
captures the unmatched children.

## `MatchIterator` — Lazy Pull-Based Engine

In addition to the recursive `run_query` (which collects all matches
into a `Vec`), there is a `MatchIterator` that yields matches one at
a time via an explicit DFS stack:

```rust
pub struct MatchIterator<'a, Cfg, L, S, const T, const P> {
    stack: Vec<Frame>,
    env: Match<Cfg>,
    plan: &'a QueryPlan,
}

impl Iterator for MatchIterator {
    type Item = Match<Cfg>;
    fn next(&mut self) -> Option<Match<Cfg>> { ... }
}
```

Each `Frame` on the stack represents a choice point (e.g., which
element of a `Join` result to try next). `next()` resumes from the
last choice point, advancing or backtracking as needed.

The lazy iterator avoids materializing all matches when only a few
are needed (e.g., for rules that subsume after the first match).

---
[← Ch 8: Query Compilation](08-query-compilation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 10: Surface Language →](10-surface-language.md)
