# Chapter 9 — Pattern Matching Execution

[← Ch 8: Query Compilation](08-query-compilation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 10: Surface Language →](10-surface-language.md)


## Flattened-Atom Continuation Execution

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

## Which Snapshot: the Round's Index Build

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

## `Match` — Binding Environment

The binding environment separates variables by kind. Node bindings
(plain `VarId`s) use `Option<Cfg::G>` because variables may be unbound
between continuation steps. Multiplicity and literal-value bindings
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
    seq_spans: Vec<PoolSpan<Cfg>>,    // SeqVarId → (start, len) into seq_pool
    set_pool: Vec<Cfg::G>,            // all set slices packed contiguously
    set_spans: Vec<PoolSpan<Cfg>>,    // SetVarId → (start, len) into set_pool
    mset_pool: Vec<Cfg::C>,           // packed AC children (id + mult)
    mset_spans: Vec<PoolSpan<Cfg>>,   // MsetVarId → (start, len) into mset_pool
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
For prefix-only (`APrefix`): fixed elements at the start, rest at end.
For suffix-only (`ASuffix`): rest at start, fixed elements at end.

## Sub-Multiset Matching (AC operators)

`DecomposeAC` enumerates all ways to match pattern elements against a
subset of an AC-node's `(id, multiplicity)` children.

### Maximum Partition Semantics

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

### Multiplicity Constraints

Each multiplicity variable has a global interval `[min, max]`, computed at
compile time by intersecting all constraints. The interval constrains the
bound child's total multiplicity:

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

1. Bound or concrete pattern elements scan the residual. When a pattern element's
   variable is already bound (its e-class is known), the matcher does a
   linear `position` search for that class in the residual multiset, checks its total
   multiplicity against the element's interval, and removes the child.
   This is O(d) for `d` distinct residual entries, though it avoids branching.
   (In `decompose_ac_elem`, this is the `bound_repr.is_some()` path.)
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
(`by_op ∩ by_contains[e]`, [Ch 6](06-index.md)/[Ch 7](07-leapfrog.md))
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

#### The matching relation we implement

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
The [ac-congruence-completeness.md](ac-congruence-completeness.md)
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
[ac-congruence-completeness.md §5b](ac-congruence-completeness.md).

## Subset Matching (ACI operators)

`DecomposeACI` enumerates all ways to match pattern elements against a
subset of an ACI-node's children (no multiplicities, since all counts
are structurally 1 due to idempotency).

Each pattern element must match a distinct child. The rest variable
captures the unmatched children. This is the set analogue of the
maximum-partition relation above; its implementation has finite test evidence,
not a soundness or completeness theorem.

## Predicate Guards

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
`RhsOp::PrimApp` interns it (Chapter 12).

The guard's placement is the scheduler's (Chapter 8, Phase A): immediately after
the last `ExtractLitVal` that fills a slot it reads. It cannot run earlier than
that, and running it later would join atoms whose results the guard is about to
discard.

## `MatchIterator` — Separate Pull-Based Engine

In addition to the primary push-continuation path, `MatchIterator` executes a
static plan and yields matches one at a time through an explicit depth-first
stack:

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

Callers that stop consuming it can avoid materializing later matches. The
saturation drivers do not currently use this path: they execute
`run_query_scheduled_into`, collect the round snapshot's matches in a
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

---
[← Ch 8: Query Compilation](08-query-compilation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 10: Surface Language →](10-surface-language.md)
