# Chapter 19 — Anti-Unification

[← Ch 18: Semi-Naive Evaluation](18-semi-naive-evaluation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 20: Index Selectivity →](20-index-selectivity-and-delta-suffixes.md)

Describes the anti-unification solver in `egraph/src/au/`: the search space it
builds over an e-graph, the two solvers that traverse it, the data structures
that hold both, and the argument that every answer it reports and every arm it
discards is justified.

Section 9 gives the implementation's soundness and pruning arguments, then
states the internal meaning of a reported optimum. Those arguments are
supported by finite differential/property tests; they are not a verified
end-to-end solver theorem. Sections 1 to 8 define the objects those arguments
are about. Measurements live in
`doc/benchmarks/records/au/anytime-corpus.md`; this chapter is the canonical
design and proof-boundary reference.

One word needs disambiguating on sight. A **certificate** here is the solver's
internal claim that a result is optimal, discharged by the search itself. It is
different from an externally checkable projection proof artifact, which is
future work.

## 1. The problem

Given two e-classes `l` and `r`, find their least general generalization: a
term `t` with a substitution into each side, minimizing

```text
quality(t) = (size(t), variant_mass(t))     lexicographically, lower is better
```

Size is the primary objective. At equal size the term with less variant mass
wins, because mass sits in the variant nodes (the positions where the two sides
disagree), so less of it means more shared backbone (Appendix C.1). Both
components saturate rather than wrap: terms too large to count tie at the bottom
of the order instead of inverting it.

The objective's shape constrains everything downstream. Every bound the solver
computes bounds the FIRST component only; the second has no useful lower bound.
Section 9.3 draws the consequence, which is that every comparison against a
bound is strict.

## 2. Theory

### 2.1 The search space is an AND/OR graph

An **OR node** is a state `(l, r, ctxL, ctxR)`: a class pair plus two cycle
contexts. Its choice is which action to take. An **AND node** is one action: a
single operator common to both sides, its induced child pairs, and their
multiplicities; solving it requires solving every child. Two states with the
same class pair but different contexts are different subproblems, because a
context only removes candidates (9.2).

Two actions terminate the recursion. If `l == r` the state returns the class's
best ground term. The **generalize action** builds a variant node holding both
projections and is always available at exactly `bs(l) + bs(r)`, where `bs(c)` is
the class's best size (2.4). It is both the incumbent every state starts from
and the fixed comparison target of the first pruning rule (9.4).

Because states are shared rather than duplicated per path, the structure is a
graph, not a tree. Section 2.6 is what that costs and how it is paid.

### 2.2 Cycles, and why we refuse to unroll them

E-graphs contain cycles, so a class can reach itself and a naive descent never
terminates. Unrolling to a fixed depth would bound the search but changes the
problem: it silently removes generalizers that need the cycle, and the bound
would have to be justified per instance. Instead the search keeps the graph
finite by refusing to re-enter a class it is already inside, which preserves
every finite generalizer and needs no depth parameter.

### 2.3 Cycle contexts: pruning without losing sharing

Each state carries, per side, the set of classes blocked on that side. A child's
context is derived by filtering the parent's through reachability, and any
action whose child pair re-enters a blocked class is refused. Filtering by
reachability rather than carrying the whole ancestor path is what preserves
sharing: two paths reaching the same pair with the same *relevant* blocks reach
the same state, so the graph stays merged.

Two modes bound reuse:

- `AncestorOnly` (default) filters against ancestor contexts, so a class occurs
  at most twice per side on a path.
- `CurrentInclusive` also filters against the current `(l, r)`, so a class
  occurs at most once per side.

Both produce finite graphs. One session uses one mode, so both solvers share one
space and their results are comparable.

### 2.4 Reachability: computing and storing reach(e)

Cycle detection, action filtering, and context construction all need `reach(e)`,
the set of classes reachable from `e` through any member e-node. It is computed
once per frozen snapshot:

1. Number live classes densely.
2. Run Tarjan over the class graph (edge: class to the class of each member
   child). All classes of one component share a reach set, and a class on a
   cycle reaches itself.
3. Process components in reverse topological order; a component's set is the
   union of its successors' sets and those successors, plus its own members when
   the component is cyclic.
4. Store **one bitset per component** plus a class-to-component index.

Memory is `#components × C / 8` bytes rather than the naive `C² / 8`, which
matters on rule-saturated graphs where components are large. Membership is one
bit test; building a child context intersects the bitset with the parent's small
context; action filtering binary-searches an interned sorted context.

The same snapshot exposes `bs(c)`, the **best size**: the least fixpoint of the
extraction recurrence, the true minimum size of any ground term in the class. It
is a property of the frozen e-graph and of no search state, which is what makes
the bounds of 9.2 admissible.

### 2.5 Cost, compression ratio, and selection reward

Both solvers minimize size, then variant mass. The reported compression ratio
compares a result against the two smallest root representatives:

```text
compression_ratio(t, l, r) = (size(t) - a) / b
    a = min(bs(l), bs(r))        b = max(bs(l), bs(r))
```

Graph search needs a bounded reward for its selection rule, so it applies a
monotone transformation of expected size, inside selection only:

```text
local_cr(n)  = (E[size](n) - a_n) / b_n
normalize(n) = 0                                if local_cr(n) <= 0
             = 1 - exp(-lambda · local_cr(n))   lambda = -ln(1 - x_target)
reward(n)    = 1 - normalize(n)                 x_target = 0.8 by default
```

`a_n` and `b_n` are the state's own representative sizes. Landmarks: perfect
compression scores 1, the bare no-sharing result (`size = a + b`) scores
`1 - x_target`, unbounded size approaches 0. The scale is `b_n`, not `b_n - a_n`,
so the no-sharing landmark is stable across states.

### 2.5.1 Normalization and convergence requirements

Since `a_n` and `b_n` are constants of the state and the map is strictly
increasing, for any two candidates at one state
`size(t1) < size(t2) <=> reward(t1) > reward(t2)`. The normalizer therefore
satisfies the bounded-reward assumption without changing the objective.

Expectation must come before normalization. Aggregation needs the additive unit,
because AND combination and expectation commute only under linear maps;
selection needs a bounded unit. The only safe place for a nonlinear map is a
comparison after which no further composition occurs, that is, the within-state
argmax. Averaging *normalized* rollout rewards, as vanilla game MCTS does, is a
different and risk-sensitive objective: by Jensen it can prefer worse expected
size with greater variance. It is prohibited here.

Selection converges to the minimum-size action provided:

- **A (objective alignment).** All actions of one state are scored through the
  same strictly increasing transform, with that state's own `(a_n, b_n)`.
  Action-dependent transforms break `Q_A < Q_B => R_A > R_B` and the inversion
  is stable at every visit count, so it misdirects the search permanently.
  State-dependent normalization is safe; action-dependent is not.
- **B (stationary basis).** `(a_n, b_n)` are immutable for the session: never
  empirical running extrema, never action-specific descendants. A drifting scale
  makes historical statistics incomparable.
- **C (denormalized compositionality).** The value equations of 2.6 and 3.3
  operate entirely in raw size units. No normalized reward enters an AND sum.
- **D (consistent estimators).** Edge estimates converge to true values;
  idempotent recomputation from converging child values (2.6) satisfies this.
  The permanent first sample `U(n)` carries weight `1 / (1 + Σ_a N(n,a))`, which
  vanishes asymptotically.
- **E (infinite exploration, vanishing waste).** `C · sqrt(Σ N) / (1 + N(n,a))`
  diverges for any neglected action, so every action is selected infinitely
  often; an action with reward gap `delta` stops being selected at roughly
  `N(n,a) ~ C · sqrt(N(n)) / delta`, giving `O(sqrt(N))` suboptimal visits.
- **F (fair AND refinement).** Every child of a realized AND node that still
  needs refinement is refined infinitely often. Round robin provides this by
  rotation; the value-guided selectors provide it through the same exploration
  term, which diverges for any neglected non-terminal child. Resolved children
  are skipped, which is admissible because fairness exists to converge
  estimates, and a resolved child's estimate is already exact (3.3.5).

### 2.5.2 Verification properties

The properties the test suite pins, each with the gate that pins it: results are
valid generalizers of both roots (`au_adversarial_correctness.rs`
re-materializes both projections and checks they land in their source classes);
a reported optimum is never below the exact optimum, and a reported certificate
lands exactly on it (`au_differential.rs`); repeated runs of one configuration
agree (determinism, 5.7); mark and restore rewind every layer together
(`au_semi_persistence.rs`); and the transport solver's flows are feasible and
minimal (`au_transport_props.rs`).

### 2.6 Adapting MCTS to graphs

The point of searching a graph is that a subproblem reached by several paths is
one node. That breaks the usual bookkeeping, in which a parent's action count
and its child's visit count are the same number. On a graph they are not: a
child accumulates visits from transposing paths its parent never chose. Two
failures follow from ignoring that. If a parent weights an action by the child's
visit count, unrelated traffic distorts the parent's policy, and the parent
explores *away* from a child other paths already validated. If a parent's value
absorbs every update its child receives, unrelated exploration below the child
drags the parent toward subproblems it never selected.

The solver separates the two quantities and recomputes instead of accumulating.

**Edge visits.** `N(n,a)` counts how many times the selector *at state n* chose
action `a`. That distribution is the state's policy. A child's own visit total
plays no part in any parent's decision.

**Idempotent values.** A state's value is recomputed from its children whenever
it is visited:

```text
Q(n)   = ( U(n) + Σ_a N(n,a) · Q(and_a) ) / ( 1 + Σ_a N(n,a) )
Q(and) = 1 + Σ_i count_i · Q(child_i)        (min-cost flow for transport)
```

`Q(n)` is the mean of the children's *current* values under the state's own
policy, regularized by one unit of weight on its own rollout estimate. Being a
pure function of the children's present values, it cannot double-count a node
reached along many paths, and a stale value corrects itself when the node is next
visited. Staleness costs search quality, never correctness, which is what
licenses updating only the path a playout took (3.3.3).

### 2.7 What correctness means here

Three distinct claims, kept separate throughout:

1. **Validity.** The returned term is a generalizer of both roots. This holds of
   every term the solver stores, at every budget (9.1).
2. **Internal optimality assertion.** The returned term is intended to be the
   lexicographic minimum when the run reports a certificate (9.5). The search
   accounting argument and finite oracle tests support this; no machine-checked
   theorem connects that flag to `OPT`.
3. **Comparability.** Two runs over one session share a space, a mode, and a
   term pool, so their results and stored proofs compose.

A budget-exhausted run claims 1 and 3, never 2.

## 3. The two algorithms

### 3.1 Shared building blocks

Both solvers use the same search space (4.2), the same action generators (3.4),
the same term pool (4.4), and the same results table (4.5). They differ only in
how they choose what to expand next and when they stop. Because the results
table is keyed by state, a proof one solver discharges is visible to the other.

### 3.2 Reference algorithm: eager_with_memo

An iterative memoized depth-first search over states, with an explicit frame
stack. Each state is `Empty`, `Visiting`, or `Solved(term)`; a `Visiting`
re-entry contradicts the cycle-mode rank argument of 2.3 and panics rather than
silently returning a nonminimal answer.

At a state it evaluates the generalize action eagerly as an incumbent,
enumerates actions, orders them best-first by the lazy-completion estimate
`1 + Σ count · (bs(child_l) + bs(child_r))`, descends, and combines. For a
transport action, combining is a min-cost flow over the children's solved
qualities. The frame's incumbent improves strictly.

It is anytime in two ways: a wall-clock deadline polled every 1024 state
entries, and a node-entry budget. On either expiry it unwinds and returns the
root frame's incumbent, marked not complete. Reordering actions permutes the
operands of a minimum, so it cannot change the optimal quality; because the
incumbent comparison is strict, it can change which of several tied terms is
returned, never how good that term is.

`run_exact_at` enters the same search at an arbitrary state rather than the root,
which is what lets graph search delegate a subproblem (9.4).

### 3.3 Monte-Carlo graph search

One playout: descend by selection from the root, expand the first unhandled
action met, estimate fresh children by rollout, backpropagate along the path
taken, then propagate any closure through the reverse edges. Repeat until the
budget is spent or the root closes.

#### 3.3.1 Fully expanded, terminal, and expansion

A state is **terminal** when `l == r`, when it has no surviving action, or when
its stored result is already exact. A terminal state is closed at birth and its
value is its stored result's size, permanently. A state is **fully expanded**
when every action slot is handled, meaning realized or excluded; a per-state
cursor tracks the first unhandled slot, so expansion is O(1) rather than a scan.

#### 3.3.2 Rollout

The rollout is deterministic, not random: at each state it takes the action with
the best static lazy-completion estimate (per-pair generalize quality; a
min-cost flow over static cell costs for a transport action), descends, and
composes on the way out. Its size becomes the state's `U`, and its term is
offered as a valid incumbent. With `static_child_seed` the rollout is deferred:
expansion seeds a fresh child with its stored best size, and the rollout runs on
that child's first selection instead, so a k-child expansion stops paying k
greedy descents for children selection may never enter. With `rollout_hybrid` a
rollout frame that passes the admission tests of 9.4 is handed to the exact
solver, so the first answer is a greedy prefix with an exact suffix.

#### 3.3.3 Backpropagation

Along the traversed path, deepest AND first, then rootward. Each AND recomputes
its value (2.6), composes its children's stored best terms into a candidate, and
offers it to its parent state; the parent then recomputes its own value. An
offer is accepted only on strict lexicographic improvement, so the incumbent is
always a real term assembled from real child terms, never an estimate.

Path-only updates leave off-path parents stale. That is sound by 2.6: values are
recomputed, not accumulated.

#### 3.3.4 Selection and expansion rules at OR nodes

```text
score(a) = reward(Q(and_a)) + C · sqrt(Σ_b N(n,b)) / (1 + N(n,a))
```

evaluated in ascending action order with strict improvement, so ties resolve to
the smallest index. All actions are normalized against the state's own basis
(2.5.1 A). Actions whose AND node is closed, and actions excluded by a bound, are
skipped: their value still enters the state's mean, but they leave the argmax,
because nothing below a resolved or refuted arm can change an answer.

#### 3.3.5 Effort allocation at AND nodes

A second selector decides which child of a realized AND receives the next unit
of refinement:

```text
round_robin: i = counter mod arity, counter += 1
uct_and:     argmax_i  reward(child_i) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
lct_and:     argmin_i  reward(child_i) - C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
```

`lct_and` is the default. Each child is normalized against its own state's basis
(2.5.1 A). The value-guided selectors skip terminal and closed children: their
estimates are already exact, so refining them converges nothing, and the bare
formulas do not starve them naturally (on a deep spine the non-terminal child's
reward converges near the terminal sibling's, and the exploration term then
splits effort evenly, which reproduces round robin's decay).

#### 3.3.6 Priors and the visit distribution

There is no learned prior. The rollout estimate `U(n)` plays the role a prior
would, and its weight decays as `1 / (1 + Σ_a N(n,a))` (2.5.1 D). The edge-visit
distribution at a state is the posterior policy in the sense of 2.6; it is not
exported, because the consumer wants a term and a certificate, not a policy.

#### 3.3.7 Complete search

Two equivalent notions of "done", one incremental and one structural. The
**closed bit** is maintained during the run: a state closes when its last open
action slot resolves, and closure propagates through the reverse edges to every
parent. The **structural check** walks the graph and asks whether every reachable
action is handled and every reachable state complete, with a tri-state visited
protocol so a re-entry on a cycle rejects conservatively. The structural check
remains as the debug oracle for the bit; the run reads the bit (9.5).

#### 3.3.8 Main loop and reporting

Seed the root's incumbent with the generalize term, take its rollout estimate,
then run playouts until the budget is spent or the root closes. On completion,
one children-first pass recomputes every value and recomposes every AND, because
path-only backpropagation may have left an off-path parent without a child's
final improvement. The reported completion is `Exact` when the root closed, and
`BudgetExhausted` otherwise.

### 3.4 Action generation per node kind

Generated per class pair and cached; the surviving subsequence is recomputed from
the same deterministic predicates wherever it is needed, so an action's index
means the same thing at counting time and at expansion time.

#### 3.4.1 Ordered operators (fixed arity and ordered variadic)

Positional zip of same-operator, same-arity member pairs. One action per member
pair; children are the positional pairs.

#### 3.4.2 Commutative binary operators (sorted pairs)

Members are stored canonically as `(min, max)`, so two orientations per member
pair are generated and the canonical order is paired.

#### 3.4.3 Associative operators (sequences)

Positional zip when the two sequences have equal length, none otherwise.
Unequal-length factoring is future work (`doc/future/au-associative-operators.md`).

#### 3.4.4 AC operators (multisets), and why canonical storage wins

An AC class member is a sorted multiset of `(class, multiplicity)` pairs. One
action is one *representation pair* of monomials, and its children are the cells
of a min-cost flow between the two multisets, so the matching is solved rather
than enumerated: no matrix of pairings is ever materialized.

A representation pair becomes an action only if a zero-cost feasibility flow
succeeds. A pair with a cycle-blocked cell in a row carrying positive supply is
Hall-infeasible; admitting it would create an action slot that can never be
realized, and the completion certificate of 3.3.7 would never close.

Cell costs enter the solver as integers. For value estimates they are quantized
as `round(q · 2^20)`, which perturbs each arc by at most `2^-21` and keeps the
integer termination argument that floating-point costs lack; the reported value
is recomputed from the unquantized child values, so quantization decides the
argmin flow only. For composition the costs are the children's lexicographic
qualities directly.

Multiplicities are carried at the surface width and narrowed once, in the
feasibility gate, so a pair whose multiplicities the solver cannot represent
never becomes a descriptor and no downstream consumer needs a fallible
conversion (Appendix C.2).

#### 3.4.5 ACI operators (sets)

Members are sorted and deduplicated, so multiplicities are all one and the flow
degenerates to a bijection between the two sets. When cardinalities differ, the
unmatched elements force variants.

#### 3.4.6 Literals

Same-value pairing only; a literal has no e-node children, so the action is
terminal.

### 3.5 Algorithm portfolio and configuration axes

The two solvers are one portfolio, and the configuration surface (section 7)
selects a point in it: exact search alone, graph search alone, or graph search
that delegates admitted subproblems to exact search and inherits their proofs.
The measured guidance is in `doc/benchmarks/records/au/anytime-corpus.md`: graph search
reaches the optimum sooner on graphs whose hard part is a small subproblem, and
exact search wins outright where its pruning closes the instance in tens of
milliseconds.

## 4. Data structures

### 4.1 Read-only e-graph interface needed by the search algorithm

`AuSnapshot` is the frozen view the solver reads: class lookup for a node,
class members by operator, `bs(c)` (2.4), the reachability structure, operator
metadata (arity, commutativity, algebraic kind), and literal values. It borrows
the e-graph immutably for the session's lifetime, so later mutations are not
observed and every derived quantity stays consistent.

### 4.2 The search-space layer

`SearchSpace` holds the states: aligned arrays for each state's left and right
class, its two interned contexts, and the two representative sizes; the context
interner; and the cycle mode. `get_or_insert_or_node` is what makes sharing
real: a state is identified by all four components, so two paths that agree on
them land on the same node.

### 4.3 The statistics layers

Two arenas of aligned columns, one for OR statistics and one for AND.

**Per OR node:** the rollout estimate `U`; the value `Q`; the normalization basis
`(min_size, max_size)`; a terminal flag; per-action edge visits, realized AND
node, static bound, excluded bit, and dynamic floor; the state's floor `L`; the
first-unhandled cursor; a rolled bit (3.3.2); a closed bit; the count of open
action slots; and a reverse-edge list naming every AND node holding this state as
a child.

**Per AND node:** its parent state *and the parent's action slot*; the operator
and its commutativity; the value `Q`; the child state list with per-child counts
(a multiplicity, or a flow value) and per-child visits; the round-robin counter;
the transport rows, columns, and cell map; a closed bit; the count of open
children; and its floor.

The parent slot is what lets closure and exclusion account the same slot exactly
once: an arm excluded by a bound and later closed from below must not decrement
its parent's open count twice.

### 4.4 The result-term pool

`TermPool` interns result terms: e-graph operator applications, literals, and
variant nodes. Interning is hash-consed and append-only, so a term id stays
valid, and it carries each term's `(size, variant_mass)` so quality is a lookup
rather than a walk. Projection extracts one side's substitution instance from a
term, which is what the validity check re-materializes (2.5.2).

### 4.5 The best-result table

`BestResults` maps each *state* to its best known term, that term's quality, and
an exactness flag. `offer` accepts only strict lexicographic improvement;
`mark_exact` is write-once. Keying by state rather than by overlay position is
what lets a proof outlive one run within a session (4.7).

### 4.6 Well-formedness

The invariants the arenas maintain are stated as assertions and debug checks
rather than machine-checked specifications: aligned columns have equal lengths,
realized action slots form a prefix under the cursor, open counts equal the
number of unresolved slots, and every reverse edge names an existing AND node.
Verifying them in the sense of `containers-verus` is future work.

### 4.7 Whole-search marks, restores, and sessions

`SearchSession` owns the space, the term pool, the results table, the action
cache, and the statistics overlay, and exposes one `mark` and one `restore` for
all of them. Restore is two-phase: every component token is validated against its
container and branch genealogy BEFORE any layer is mutated, so a foreign or
abandoned token cannot leave a partial restore. Layers then restore in reverse
dependency order.

## 5. Rust implementation

### 5.1 Module layout

`session.rs` (public API and configuration), `space.rs` (states, contexts, cycle
filtering), `actions.rs` (3.4), `ac_repr.rs` (AC and ACI representations),
`transport.rs` (min-cost flow), `exact.rs` (3.2), `mcgs.rs` (3.3), `terms.rs`
(4.4), `results.rs` (4.5), `estimates.rs` (the bounds of 9.2), `census.rs`
(action counting, independent of any run), `exact_memo.rs` (the session-level
clean-solve memo of 9.4), `reward.rs` (2.5), `egraph_api.rs` (4.1), `pretty.rs`,
`dump.rs`.

### 5.2 Container primitives

Everything persistent is built from the verified container layer: `VecP` for
mutable columns, `AppendOnlyVec` for immutable ones, `SpMap` for the state and
memo indices, and typed spans for the flattened per-action and per-child pools.
Each contributes its own token to the session token, so no layer can be rewound
independently of the others.

### 5.3 Id types

An `AuIds` trait fixes the id family in one place: state ids, statistics-node
ids, per-action and per-child ids, context ids, term ids, and the shared index
word. The default binding matches the 31-bit e-graph configuration; a different
configuration binds different widths without touching the algorithms.

### 5.4 Arena schemas

Node structure is append-only and values are `VecP`, so a restore truncates the
structure and rewinds the values in one step. Per-action and per-child state is
flattened into pools addressed by typed spans, which keeps a node's columns
contiguous and makes the arena's length assertions total.

### 5.5 Restorable hash indices

The state index and the clean-solve memo are hash maps over an append-only log.
The log is the source of truth; the index is derived. A restore validates the
log's token first, then removes the truncated suffix's keys from the index while
the log is still live, then rewinds the log.

### 5.6 Token and restore order

Marks are taken in dependency order (space, terms, results, actions, statistics)
and restores run in reverse. The whole-session validation of 4.7 happens before
any mutation.

### 5.7 Determinism

Both solvers are deterministic. There is no randomized tie-breaking anywhere:
selection ties resolve to the smallest index, action order is the generation
order, and the transport solver is exact-arithmetic. Two runs of one
configuration on one snapshot return identical terms and identical completions,
which `au_differential.rs` asserts directly.

## 6. Script commands

`(antiunify e1 e2)` runs the configured solver over the two expressions' classes
and reports the term, its quality, and whether the result is certified.
`(checkau e1 e2 expected)` additionally asserts the result, which is what makes
the `.egg` fixtures self-checking.

## 7. Configuration

Defaults are the reference search: every flag below is off or unbounded by
default, and each has a differential test asserting that turning it on changes no
answer it should not (section 8).

| flag | effect |
| --- | --- |
| `algorithm` | exact search (3.2) or graph search (3.3) |
| `cycle_mode` | `AncestorOnly` or `CurrentInclusive` (2.3) |
| `playouts`, `exploration_constant`, `x_target`, `and_selector` | graph-search budget and selection (2.5, 3.3.4, 3.3.5) |
| `exact_deadline` | anytime exact search (3.2) |
| `exact_pruning`, `context_subsumption` | the exact solver's branch and bound, and clean-solve reuse (9.4) |
| `dominance_pruning` | generalize dominance at state creation (9.4) |
| `closed_bit` | maintain closure and skip resolved subgraphs (3.3.7) |
| `hybrid_exact`, `hybrid_threshold`, `hybrid_action_threshold`, `hybrid_node_budget` | exact solving of admitted subproblems, its two admission tests, and its in-call budget (9.4) |
| `rollout_hybrid` | fire that trigger from inside a rollout (3.3.2) |
| `session_exact_memo` | share clean solves across exact calls in one session (9.4) |
| `live_incumbent_pruning` | exclude arms against the live incumbent (9.4) |
| `interval_bounds` | make arm bounds dynamic (9.2); requires the previous flag |
| `static_child_seed` | seed fresh children statically and defer their rollout (3.3.2) |

## 8. Testing

`au_differential.rs` holds the soundness gates. Each behavior-changing flag has
one, and they share a shape: run the flag on over the fixture corpus at several
budgets, and assert that the result never beats the exact optimum, that a
reported certificate lands exactly on the exact optimum, and that quality never
falls below the flag-off fixture. A flag that trades per-playout quality for
per-playout cost asserts soundness and determinism instead of fixture equality,
and is measured at matched wall clock in the corpus.

Beyond those: `au_adversarial_correctness.rs` re-materializes both projections
into a fresh e-graph and checks they land in their source classes;
`au_metamorphic.rs`, `au_convergence_props.rs`, and `au_transport_props.rs` carry
the property tests; `au_deceptive.rs` builds the deceptive families and asserts
the constructed misranking is the one the search actually faces;
`au_semi_persistence.rs` checks that mark and restore rewind every layer
together; `au_conformance.rs` runs the `.egg` fixtures.

`au_oracle.rs` checks the exact solver against the definition rather than
against itself. Anti-unification over an e-graph is the minimum, under the
lexicographic key, of Plotkin's first-order anti-unification over every pair of
ground terms the two classes can produce. On acyclic fixtures small enough to
settle by brute force, the file enumerates those terms straight from the
e-graph, without the snapshot's subsumption filter, runs textbook Plotkin on
every pair, and asserts the solver agrees. This is finite evidence that the
solver agrees with the quotient-defined objective: the oracle does not use the
solver's member ordering, so a representative-dependent answer would disagree
on a checked fixture. The objective itself is well defined by its quantification
over represented terms; the test does not prove agreement on unenumerated
instances. A fixture whose term set is unbounded or too large is
skipped rather than truncated, because a truncated enumeration is not an oracle,
and the test asserts a floor on how many fixtures were actually enumerable so it
cannot pass by skipping everything. The same file pins that the reported size is
the size of the returned term, and that enabling bounds pruning and context
subsumption leaves the optimum unchanged, which is where an inadmissible bound
would show up.

Two files carry corpora with a constructed oracle rather than a comparison
against the exact solver. `au_formalization.rs` builds two formalizations of one
statement and separates the classes of difference between them: conjunct order
and repetition, which canonization absorbs; a replaced condition, where the
planted count is asserted to equal the number of generalized positions; and a
negation pushed over a disjunction, which no anti-unifier over terms can share
and which saturating De Morgan recovers.

It also prices three paraphrase operators that each separate the two sides by a
single edit, which is what shows that counting edits does not measure how far
apart two formalizations are. Replacing a leaf costs a constant 1 however wide
the term grows. Leaving a variable undetermined where the other side lets a
default stand costs `2n` over `n` consumers, because the undecidedness reaches
each of them. Adding one conjunct costs `2n + 3` against `n` shared members
when the operator declares no unit: two ACI conjunctions of different arity have
no structural match available, since a generalization must instantiate to both
sides and no fixed-arity pattern does, so the node is generalized whole.
Declaring the operator's `:identity` removes that term entirely: `pad_pair` pads
the shorter monomial with identity copies until the totals agree, and the excess
becomes a constant 3 at every width. The arity ranking is therefore a property of
the declaration rather than of anti-unification, which is the practical reason to
declare the unit on any conjunction two formalizations might disagree about the
length of. Variant count sees none of this and reads 1 for all three operators,
because hash-consing shares the differing subterm. `au_hardness.rs` sweeps burial depth
against branching factor and prints which method reaches the optimum first per
cell, and pins the finding that the deceptive family never leaves the exact
solver's region at any feasible scale.

## 9. Bounds, pruning, and what optimal means

### 9.1 The feasibility invariant

> **Every term the solver stores for a state is a valid generalizer of that
> state.**

Terms enter the results table from three places and each preserves it. The
generalize action builds a variant node over both sides, valid by construction. A
rollout, and an AND composition, assemble terms their children returned, so
validity is inductive over children. An exact subproblem solve returns a term for
the same state. Nothing else writes terms.

The consequence used everywhere below: an incumbent is an *achieved* value. If an
arm provably cannot beat some quantity, and the incumbent already achieves at
least that, discarding the arm loses nothing.

### 9.2 The bound invariant

> **Every bound the solver compares against is a lower bound on what the bounded
> object can achieve.**

The primitive is per class pair:

```text
lb(l, r) = bs(l)                     if l == r
         = max(bs(l), bs(r)) + 1     otherwise
```

*Argument.* If `l == r` the optimum is the class's best ground term, of size
exactly `bs(l)`. If `l != r` the classes are disjoint, so no variant-free term
projects into both; any generalizer contains at least one variant node above a
subterm at least as large as the larger side's minimum. Since `bs` is a least
fixpoint over ground terms rather than an incumbent (2.4), the bound holds at
every state under every context, and does not assume the projections are optimal
representatives.

Three bounds derive from it, each a sum or a flow of admissible parts:

- **static arm bound**: `1 + Σ count · lb(pair)` for a structural action; a
  min-cost flow over `lb` cell costs, plus one, for a transport action. The flow
  bound is valid because every true cell value dominates its `lb` and the true
  optimal flow stays feasible in the bound problem.
- **dynamic arm bound** (`interval_bounds`): `1 + Σ count · L(child)`, where
  `L(state)` is the minimum over that state's live arms. It starts equal to the
  static bound and rises as children's floors rise. Every write keeps the maximum
  of old and new, so a floor never loosens; propagation is path-only, so an
  unrefreshed floor is weaker than it could be, never wrong.
- **partial completion bound** (exact solver): solved children at their true
  size, unsolved children at `lb`. Substituting a solved child's true size for
  its bound only raises the sum, so a mid-action re-check is at least as tight as
  the initial one.

Saturating arithmetic keeps every accumulation a lower bound, and a saturated
total still exceeds every representable incumbent, so it discards the arm.
Discarding is sound: a pair with no finite member admits no valid term at all.

### 9.3 Why every comparison is strict, and on size alone

The bounds of 9.2 bound `size`; the objective is `(size, variant_mass)`. An arm
whose size floor *equals* the incumbent's size can still produce an equal-size
term with smaller variant mass, which is a genuine lexicographic improvement.
Comparing with `>=` would therefore discard the true optimum. Every rule in 9.4
tests `bound > incumbent`, strictly, on the size component only. Section 9.5
shows the same reasoning forbidding `L == U` as a closing condition.

### 9.4 The pruning rules

Each discards an *arm*, never a term.

| rule | test | argument |
| --- | --- | --- |
| generalize dominance | static arm bound > `bs(l) + bs(r)` | the generalize action is always available at exactly that value (2.1), so an arm that cannot come in under it can never be optimal |
| live-incumbent exclusion | arm bound > the state's current incumbent | the same argument against a tighter target, valid because the incumbent is achieved (9.1) |
| interval exclusion | dynamic arm bound > incumbent | the dynamic bound is admissible and monotone (9.2), so it can be tested at any time |
| exact branch and bound | partial completion bound > incumbent | the partial bound is admissible; equality cannot prune because variant mass may still improve (9.3) |
| resolved-subtree skip | the child or action is closed | a resolved subgraph can change no value, no stored term, and no certificate |

Two rules need more than a line.

**Context subsumption.** A solve of a state is *context-clean* when its entry
context removed no candidate anywhere in the winning derivation; the solver
records that derivation's support, the classes it descended through on each side.
A clean solve of the bare pair `(l, r)` may then be reused at any other state
with the same pair whose entry contexts are disjoint from that support.

*Argument.* Contexts only remove candidates, so `V(ctx) >= V(empty)` for every
context. If the stored derivation's support is disjoint from `ctx`, every step of
that derivation remains available under `ctx`, so it re-executes there and
`V(ctx) <= V(empty)`. Hence equality, and the stored term is the new state's
optimum too. If the supports intersect, the stored term is still *valid*
(validity does not depend on contexts), so it may be offered as an incumbent, but
it must not be marked exact. With `session_exact_memo` the same entries persist
across exact calls in a session, which changes what is reused and not why it is
sound.

**Exact subproblem solving.** When a state passes two admission tests, a
rectangle of reachable class pairs and the state's own action count, the exact
solver runs on that state's own four-tuple: same class pair, same contexts, same
cycle mode, same generators. The implementation treats a completed call as the
optimum *of that state*, which is exactly what the exactness flag asserts and
what finite oracle tests check. A call that exhausts
its node budget returns a feasible incumbent with no proof attached. Both tests
are needed: the rectangle bounds how many subproblems lie below the state, the
action count bounds the work per subproblem, and each misjudges the family the
other catches.

### 9.5 The two bits, and why closure is not `L == U`

**The closed bit** lives in the statistics overlay and is structural: every
action slot of this state is resolved, meaning realized and closed, or excluded
by a bound. It is run-scoped and rewinds with the overlay. The root's closed bit
is the run's internal certificate: when set, its accounting says every reachable
action was realized or excluded by a bound. The reported term is then marked
optimal by the implementation. This is not an externally checkable or
machine-checked optimality proof.

**The exactness flag** lives in the results table and is about a stored term:
this term is the optimum for this state. It is set when the state is trivial,
when an exact subproblem solve completes on it, when a context-clean result is
reused under a disjoint context, and when closure reaches it. It is
session-scoped, so a later run finds such a state terminal at creation.

**Closure is not `L == U`, and cannot be.** With floors on both states and arms
it is tempting to close a state when its floor meets its incumbent. That is
unsound here for the reason of 9.3: `L` bounds size, `U` is lexicographic.
`L == U.size` establishes only that no live arm can produce a *smaller* term; an
arm whose floor equals that size may still produce an equal-size term with
smaller variant mass, and closing would report a term that is not the
lexicographic optimum as proven. The closing condition therefore stays "no open
action slots", and floors serve to reach it sooner by excluding arms. Once a
state closes, its floor is set to its incumbent, so `L == U` holds as a
*consequence* of closure, never as its cause.

## Appendix B. Worked AC example

Two AC sums, `l = x + x + y` and `r = x + z + z`, over an operator whose members
are stored as sorted `(class, multiplicity)` multisets: `l = [(x,2), (y,1)]`,
`r = [(x,1), (z,2)]`.

One representation pair yields one transport problem with row supplies `(2, 1)`
and column demands `(1, 2)`. Cell costs are the children's qualities: `(x,x)` is
a trivial pair costing `bs(x)`, while `(x,z)`, `(y,x)`, and `(y,z)` are distinct
pairs costing at least `max(bs, bs) + 1` each. The min-cost flow sends one unit
through `(x,x)`, one unit through `(x,z)`, and one through `(y,z)`, and the
resulting term is `x + V1 + V2` with two variant positions. No pairing matrix is
enumerated: the assignment is the flow's argmin, and the flow's cost is the AND
node's value.

## Appendix C. Worked examples

### 9.6 Target optimum theorem and current proof boundary

The intended high-level theorem is stated here because everything above is
about how the search prunes and nothing above, by itself, proves what it
converges to. The equality below currently has a prose argument and finite
implementation evidence. It is not a theorem established by `au-verus`.

**The objective.** For a class `C`, write `terms(C)` for the set of ground terms
`C` represents, and `bs(C)` for the size of its smallest term. For ground terms
`s` and `t`, `lgg(s, t)` is Plotkin's least general generalization and
`q(s, t) = (size, variant_mass)` is its quality key, where `size` counts concrete
nodes and `variant_mass` counts those under a generalized position. Define

```text
  OPT(A, B) = lex-min over s in terms(A), t in terms(B) of q(s, t)
```

**Well-definedness is immediate from that definition**, and this is worth saying
plainly because it is easy to mistake for an open question: `terms(C)` is a set
determined by the class, and no representative, member ordering or union-find
survivor appears anywhere in `OPT`. What needs proof is not that `OPT` is well
defined but that the solver computes it, since the solver *does* work with
members and representatives.

**The recurrence.** The solver computes

```text
  D(A, B) = lex-min of
      bs(A) + bs(B)                                    -- generalize
      1 + sum over i of D(A_i, B_i)                    -- one structural action
```

where the structural line ranges over pairs of members `n in A`, `m in B` with
the same operator and arity, and `A_i`, `B_i` are the classes of their i-th
children. `bs(A) + bs(B)` is the generalize cost because a generalized position
hides both sides, and minimizing over the terms it could hide gives the two
smallest.

**Lemma (a lexicographic minimum decomposes over independent sums).** Let each
child `i` offer an achievable set `S_i` of pairs, and let the parent's achievable
set be the elementwise sum. Then the lexicographic minimum of the sum is the sum
of the lexicographic minima.

*Proof.* Write `(a_i, b_i) = lex-min(S_i)` and take any choice `(x_i, y_i) in
S_i`. Each `x_i >= a_i`, so `sum x_i >= sum a_i`. If the sums are equal then
`x_i = a_i` for every `i`, since a single strict increase cannot be offset by a
decrease elsewhere; the per-child choice is then among the size-minimal elements
of `S_i`, where `y_i >= b_i` by lexicographic minimality, so `sum y_i >= sum
b_i`. Hence `(sum a_i, sum b_i)` is the lexicographic minimum of the sum. ∎

The lemma is what makes a dynamic program valid here at all. Summing per-child
optima is obviously right for a scalar objective and is not obviously right for a
lexicographic one, because a child could in principle trade size for variant
mass. It cannot, and the reason is that both components are additive and the
children are chosen independently.

**Target theorem.** `D(A, B) = OPT(A, B)` wherever both term sets are
non-empty.

The paper argument has two inequalities.

`OPT <= D`: every value `D` returns is achieved by a pair of terms. Induct on the
recursion. The generalize line is achieved by the two smallest terms, whose lgg
is a single generalized position of quality `(bs(A) + bs(B), bs(A) + bs(B))`. A
structural line at members `n, m` is achieved by `f(s_i)` and `f(t_i)` where the
`s_i, t_i` achieve `D(A_i, B_i)` by the induction hypothesis; those terms lie in
`A` and `B` because `n` and `m` are members, and their lgg is `f(lgg(s_i, t_i))`
with quality `1 + sum`, by the lemma.

`D <= OPT`: every term pair costs at least `D`. Induct on `|s| + |t|`, which is
finite for each pair even when `terms(C)` is infinite, so cyclic classes need no
special treatment here. If the root operators or arities differ, `lgg(s, t)` is a
single generalized position of cost `|s| + |t| >= bs(A) + bs(B) >= D(A, B)`. If
they agree, then `s = f(s_i)` with `s_i in terms(A_i)` for the member `n` that
`s` uses at its root, and likewise for `t`; so
`q(s, t) = 1 + sum q(s_i, t_i) >= 1 + sum D(A_i, B_i) >= D(A, B)` by the
induction hypothesis, the lemma, and the fact that `(n, m)` is one of the pairs
the structural line ranges over. ∎

**Conditional corollary (edge counts are the recurrence, not an optimization).** If
the target theorem and recurrence construction are established, `D` is a
function of the class pair, so a child pair reachable by several paths has one
value. Pricing an AND node at `1 + sum over children of count * D(child)` is
therefore the same quantity as the tree unfolding, and counting edges rather than
nodes needs no separate justification. §4 describes the memo that realizes this;
the corollary is why it is sound.

**Conditional corollary (representation independence).** If `D = OPT`, and `OPT` mentions
no representative, the answer is invariant under any change of union-find
survivor or member ordering.

**What is machine-checked.** `au-verus` proves:

- totality and monotonicity properties of the lexicographic objective,
  including decomposition of independent sums;
- that an action already assumed to belong to the action set and to be no worse
  than every action satisfies the set-minimum predicate
  (`lemma_preselected_action_is_min`);
- that any function satisfying the two current lower-bound inequalities is
  below every represented positional term pair
  (`lemma_recurrence_below_every_pair`);
- representation decomposition/assembly, and that minimum-size terms give a
  Plotkin result no worse than hiding both terms.

**Why this does not prove `D = OPT`.**

1. `satisfies_recurrence_lower_bounds` states only `d <= action_cost`
   inequalities. The constant-zero quality function satisfies them but
   generally is not attainable.
2. `lemma_preselected_action_is_min` assumes in its precondition that the
   selected action is already no worse than every action. It does not prove
   that a recurrence or solver selects it.
3. `lemma_generalize_has_no_worse_witness` relates a represented witness to
   the generalize action, not to an arbitrary `d`.
4. `lemma_structural_terms_are_represented` has no quality postcondition and
   no recursive child-quality premise.
5. No exported theorem defines the intended least recurrence solution or
   states that its value equals `OPT`.

**Proof roadmap.**

1. Define the recurrence by equality with the minimum action cost, or construct
   its least solution explicitly.
2. Prove action-set non-emptiness and existence/selection of a minimum.
3. Strengthen the structural witness lemma with recursive quality premises and
   an assembled Plotkin-quality postcondition.
4. Prove that the selected recurrence value is attained by represented terms,
   including the cyclic-class case.
5. Combine that `OPT <= D` result with the existing `D <= OPT` lower-bound
   induction in one theorem whose postcondition states equality.
6. Separately refine the positional term model to production AC/ACI transport,
   identity padding, multiplicities, cycle contexts, bounds/pruning, MCGS, and
   exact/MCGS delegation.

Until those steps are complete, `au_oracle.rs` is finite evidence for the Rust
exact solver: it enumerates `OPT` on small acyclic fixtures, checks `lb_pair`
against that optimum, and tests representation independence. It is not a
universal proof. The maintained theorem and production-refinement acceptance
criteria are in
[`../future/au-correctness-and-validation.md`](../future/au-correctness-and-validation.md).

---

### C.1 Cyclic tie-break and the variant-mass objective

On a cyclic graph two candidate terms often tie on size, and the tie is not
cosmetic: one keeps the shared backbone and pushes disagreement into a single
variant, the other spreads disagreement across several. Variant mass separates
them, preferring the first, which is the term a reader would call the better
generalization. This is why the objective is a pair and why every bound
comparison is strict (9.3): a size-only rule would treat the two as
interchangeable and could discard the better one.

### C.2 AC multiplicities

Multiplicities are carried at the surface width and narrowed once, inside the
feasibility gate that produces a transport descriptor. A pair whose
multiplicities the transport solver cannot represent is reported infeasible,
which is the same signal an unsolvable pair gives: it consumes no action slot.
Consequently every later consumer of a descriptor works with already-narrowed
supplies and needs no fallible conversion, and the gate and the solver cannot
disagree about what was solved.

---
[← Ch 18: Semi-Naive Evaluation](18-semi-naive-evaluation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 20: Index Selectivity →](20-index-selectivity-and-delta-suffixes.md)
