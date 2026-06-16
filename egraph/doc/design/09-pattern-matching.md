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

### Cost and Correctness of AC Matching

`DecomposeAC` enumerates bindings of pattern elements against a node's
multiset. It is worth being precise about what is enumerated, because
"enumerate all sub-multisets" overstates it, and about which costs are
intrinsic versus avoided.

What we do and do not enumerate:

1. Bound or concrete pattern elements cost O(1). When a pattern element's
   variable is already bound (its e-class is known), the matcher does a
   direct lookup of that class in the residual multiset, checks
   multiplicity, and subtracts. (In `decompose_ac_elem`, this is the
   `bound_repr.is_some()` fast path.)
2. Only unbound scalar variables cause branches, and they branch
   over the distinct residual elements, not over sub-multisets. The matched
   multiplicity is taken whole, so we do not enumerate "1 of this element,
   or 2, or 3…". This is the overview's *maximal partition matching*: the
   multiplicity sub-count blowup is avoided, and branching is restricted to
   distributing unique residual elements among unbound variables.
3. The `rest` variable absorbs the entire remainder in one binding. A
   pattern `(+ ?x ..rest)` yields `O(distinct elements)` matches — bind `?x`
   to each distinct element, `rest` captures the rest as one multiset-typed
   binding — not `O(2ⁿ)` over sub-multisets of the residual.

So for a pattern with `k` unbound scalar variables against a node with `d`
distinct children, the branching is the `k`-permutations of `d`, i.e.
`O(dᵏ)`: polynomial in the term, exponential only in the pattern arity `k`
(small, and fixed by the rule author). Leapfrog narrowing over the indices
(`by_op ∩ by_contains[e]`, [Ch 6](06-index.md)/[Ch 7](07-leapfrog.md))
selects which nodes are worth decomposing, so `DecomposeAC` rarely runs
against more than a small slice of the graph.

#### The matching relation we implement

A correctness claim only means something against a relation defined
independently of the algorithm. The relevant one is the classical AC
matching problem (Contejean, RTA 2004; also Hullot 1979), defined purely
from the equational theory:

> Given a pattern `p` and a subject `s`, a match is a substitution `σ` with
> `pσ =_AC s`, where `=_AC` is equality modulo associativity and
> commutativity. The set of matches is well-defined — and finite, since the
> AC-equivalence class of `s` is finite — before any matching algorithm is
> written.

Specialized here: `s` is an AC node with child multiset `M` over e-class
ids, `σ` maps each scalar variable to an e-class id and each `rest` variable
to a sub-multiset, and `pσ =_AC s` becomes the multiset equation

```
{{ σ(x₁)^{m₁}, …, σ(xₖ)^{mₖ} }}  ⊎  σ(rest)  =  M.
```

We claim *soundness* against this relation: every `σ` that `DecomposeAC`
emits satisfies the equation — its images, with multiplicities, plus the
`rest` binding sum to `M`, and every multiplicity constraint holds, so no
spurious match is produced. This is the property we rely on, and the one that
makes matching safe to drive rebuild, our matcher never fabricates a binding.

We do *not* claim completeness here, i.e. that `DecomposeAC` emits every solution
of the equation. AC matching is NP-complete (Benanav, Kapur, Narendran
1987), and complete enumeration is exactly where matchers tend to go wrong
(missed distributions, mishandled multiplicities, non-linear variables).
Contejean's inference-rule algorithm for this same relation is
verified complete in Coq; ours is a different algorithm, and its
completeness is left as future verification work.
The [ac-congruence-completeness.md](ac-congruence-completeness.md)
verification plan is where that would be taken up.

One scope note, so the relation itself is not misread. The variables in `σ`
range over what exists: an e-class id for a scalar, an existing sub-multiset
for `rest`. A scalar variable is not quantified over implicit sub-sums —
matching `(+ ?x ?y)` against a node stored only as `+(a, b, c)` does not
admit `?x = a+b`, because `a+b` is not an e-class id. That extension is AC
*unification*, a strictly larger problem whose decision would require
materializing every sub-sum (the `O(3ⁿ)` blowup the multiset representation
exists to avoid); Contejean and Conchon et al. (2012, §8) leave it aside.
The entailed equalities this scope leaves out are recovered not by a larger
matcher but by congruence closure in rebuild materializing the relevant
sub-sum nodes — see
[ac-congruence-completeness.md §5b](ac-congruence-completeness.md).

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
