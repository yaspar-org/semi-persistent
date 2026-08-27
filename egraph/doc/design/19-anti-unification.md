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
are about. Historical measurements for the predecessor contextual root solver
remain in `doc/benchmarks/records/au/anytime-corpus.md`. They are not current
comparisons for pair-mode `exact_fixed.rs`; the rerun protocol is tracked in
[`../future/performance-validation.md`](../future/performance-validation.md).
This chapter is the canonical design and proof-boundary reference.

One word needs disambiguating on sight. A **certificate** here is the solver's
internal claim that a result is optimal, discharged by the search itself. It is
a different object from the externally checkable proof artifact specified in
[`../future/au-proof-certificates.md`](../future/au-proof-certificates.md),
which is not production functionality. `tests/au_proof_certificates.rs`
prototypes projection materialization and proof-path extraction and exposed the
need for two-phase replay; it is evidence for the proposed pipeline, not an
exported certificate format or verified checker.

## 1. The problem

Given two e-classes `l` and `r`, find a minimum-quality anti-unifier in the
supported search domain: a term `t` with a substitution into each side,
minimizing

```text
quality(t) = (size(t), variant_mass(t))     lexicographically, lower is better
```

Size is the primary objective. At equal size the term with less variant mass
wins, because mass sits in the variant nodes (the positions where the two sides
disagree), so less of it means more shared backbone (Appendix C.1). Both
components saturate rather than wrap: terms too large to count tie at the
worst representable end of the order instead of inverting it.

The objective's shape constrains everything downstream. Every bound the solver
computes bounds the FIRST component only; the second has no useful lower bound.
Section 9.3 draws the consequence, which is that every comparison against a
bound is strict.

## 2. Theory

### 2.1 The search spaces are AND/OR graphs

In `Pair` mode, root Exact has one **OR node** per reachable ordered class pair
`(l, r)`. An **AND node** is one action: a common operator, its induced child
pairs, and their multiplicities. Solving an action requires every selected
child; AC/ACI chooses those children by min-cost transport.

The two side modes, UCT in every mode, and the contextual Exact calls UCT
delegates use a class pair plus a cycle-filter context. A side context stores
left and right classes independently; a pair context stores ordered class
pairs. Two states with the same `(l, r)` but different contexts are distinct
because a context removes candidates. Their optimization domain is the action
graph surviving the selected policy (2.3).

Two actions terminate the recursion. If `l == r` the state returns the class's
best admissible ground term. The **generalize action** builds a variant node
holding both projections and is always available. For distinct classes its
stored quality is `(bs(l) + bs(r), bs(l) + bs(r))`, subject to the `u32`
capacity boundary in 2.6.1; `bs(c)` is the snapshot's best admissible size
(2.4). It is both the incumbent every state starts from and the fixed comparison
target of the first pruning rule (9.4).

Because states are shared rather than duplicated per path, the structure is a
graph, not a tree. Section 2.6 is what that costs and how it is paid.

### 2.2 Cycles as finite derivations

E-classes are a finite regular tree grammar even when they represent infinitely
many finite terms. Recursive descent over that grammar can loop, but rejecting
a repeated class is not complete: one side may revisit a class while the
ordered pair continues to make progress and later reaches a terminal pair.
The test `cycle_modes_apply_to_exact_uct_and_both_hybrid_paths` in
`tests/au_adversarial_correctness.rs` pins such a case: side-filtering returns
size 9 while the finite derivation has quality `(8, 3)`.

Pair-mode root Exact therefore closes the finite graph of reachable ordered
pairs without recursing, then computes:

```text
best[0, q]     = terminal_generalize(q)
best[d + 1, q] = min(best[d, q],
                     every action composed from best[d, child])
```

The intended interpretation is that the value after round `d` is the minimum
over achieved finite derivations of structural depth at most `d`, and every
stored value carries an attaining witness term. The code constructs witnesses
and finite oracle tests exercise this interpretation, but its universal round
invariant is still a proof target (9.6). The proposed instance-derived bound is:

> A minimum-size derivation never repeats an ordered pair on one path.

If pair `q` occurred below itself, the descendant subtree would already be a
valid result for `q`. The surrounding structural path contains that subtree
with positive multiplicity and adds at least one ordinary operator, so replacing
the ancestor by the descendant is strictly smaller. With `N` reachable pairs,
the argument gives an optimum of depth below `N`; the implementation asserts
that relaxation stabilizes within that bound. Pair-cycle erasure and the
`N`-round bound are prose arguments with regressions, not machine-checked
theorems. Infinite recursive derivations never acquire a witness and are not
candidates.

### 2.3 One cycle policy for every algorithm

`cycle_mode` is an input to root Exact, UCT, expansion-time hybrid Exact, and
rollout-time hybrid Exact. A hybrid call copies the UCT node's context and mode;
it never substitutes its own policy. Three values are implemented:

- `AncestorOnly` (`:cycles sides`, the default) tracks left and right classes
  independently and filters against side-ancestor contexts. A class can occur
  at most twice per side on a path.
- `CurrentInclusive` (`:cycles sides-current`) also filters against the current
  left and right classes, so a class occurs at most once per side.
- `Pair` (`:cycles pair`) tracks ordered `(left, right)` pairs. Either side may
  recur alone; only an already active ordered pair is blocked.

#### Why both policy families are intentional

The policies answer two different questions about a cyclic e-graph.

The **side policies** are provenance-conservative. Source terms are finite
DAGs, while saturation can introduce cycles through rewrites. Refusing to
revisit either side prevents a rewrite-created cycle from being used to shift
one projection through extra structure and then absorb that structure into the
shared backbone. This was the original operational intent of cycle filtering,
and it also removes candidate derivations early. `AncestorOnly` preserves the
established default behavior; `CurrentInclusive` is the stricter boundary
convention used to expose sensitivity to whether the current class is already
blocked.

That rationale is a policy choice, not an optimality theorem. The cyclic
reproducer above disproves the earlier zero-sum intuition that such a shift can
never improve the result: a one-sided revisit can exit through a different
partner and produce a strictly smaller finite AU. Side-mode completion must
therefore be reported as optimal only within the side-filtered graph.

The **pair policy** instead gives the snapshot's admissible grammar its
regular-tree-grammar meaning: every finite derivation in the supported action
domain is eligible, including one whose derivation revisits one class while the
other side changes. It blocks only a repeated ordered subproblem, which the
pair-cycle-erasure argument identifies as redundant for the minimum-size
objective. Pair mode is consequently the mode used for global finite-term
`OPT` evidence and exact-oracle comparisons, subject to the domain boundaries
in 2.4, 2.6.1, and 9.6. It can admit substantially more work than side
filtering, so it is explicit rather than silently replacing the compatibility
default.

Choose a side policy when rewrite-created cyclic structure is intentionally
outside the AU search semantics, and choose `Pair` when the search should range
over all supported finite derivations of the admissible snapshot grammar.
Results from the two policy families are comparable as terms and qualities, but
their certificates quantify over different domains.

A child context retains only ancestors independently reachable from that child,
which preserves sharing while retaining the relevant cycle guards. All three
policies produce finite contextual graphs. The side policies can exclude valid
finite generalizers and therefore certify only the optimum of their filtered
graphs.

At a `Pair` root, Exact uses the bounded bare-pair relaxation of 2.2 instead of
recursive context expansion. UCT and both hybrid paths use pair contexts and
therefore search the same pair-simple derivation domain. The pair-cycle-erasure
argument says this domain contains a minimum-size finite derivation, but that
argument is not yet machine-checked (9.6). Terms returned under different
policies remain directly comparable under the same quality key; completion
claims must name their policy and domain.

### 2.4 Reachability: computing and storing reach(e)

Context filtering and construction need `reach(e)`, the set of classes
reachable from `e` through any member e-node. It is computed once per frozen
snapshot:

1. Number live classes densely.
2. Run Tarjan over the class graph (edge: class to the class of each member
   child). All classes of one component share a reach set, and a class on a
   cycle reaches itself.
3. Process components in reverse topological order; a component's set is the
   union of its successors' sets and those successors, plus its own members when
   the component is cyclic.
4. Store **one bitset per component** plus a class-to-component index.

The dense bit storage is
`#components × ceil(C / 64) × 8` bytes rather than the naive
`C × ceil(C / 64) × 8`. Total reachability-table memory also includes one
class-to-component id per class, one typed span and one `u32` popcount per
component, and the `Vec` headers/capacity. The condensation matters on
rule-saturated graphs where components are large. Membership is one bit test;
building a child context intersects the bitset with the parent's small context;
action filtering binary-searches an interned sorted context.

The same snapshot exposes `bs(c)`, the **best size**: the least fixpoint of the
extraction recurrence over non-subsumed members. It is the true minimum only in
that admissible snapshot grammar and only when the expanded size is strictly
below `u32::MAX`, which is reserved as the no-finite-representative sentinel.
Search startup rejects a root whose reachable admissible grammar contains a
class with no such representative. `bs` is a property of the frozen snapshot
and of no search state, which is what makes the bounds of 9.2 admissible within
that domain.

### 2.5 Cost, compression ratio, and selection reward

Both solvers minimize size, then variant mass. The reported compression ratio
compares a result against the two smallest root representatives:

```text
compression_ratio(t, l, r) = (size(t) - a) / b
    a = min(bs(l), bs(r))        b = max(bs(l), bs(r))
```

For one fixed pair of ground terms, this linear ratio lies in `[0,1]`: the bare
variant of the two terms is the no-sharing endpoint. For e-classes, the
denominator uses independently smallest representatives while a searched
derivation may use larger represented terms, so the same linear ratio can
exceed 1. It is not clamped.

Graph search needs a bounded reward for its selection rule, so it applies a
monotone transformation of expected size, inside selection only:

```text
local_cr(n)  = (E[size](n) - a_n) / b_n
normalize(n) = 0                                if local_cr(n) <= 0
             = 1 - exp(-lambda · local_cr(n))   lambda = -ln(1 - x_target)
reward(n)    = 1 - normalize(n)                 x_target = 0.8 by default
```

For the required configuration `0 < x_target < 1`, the exponential `normalize`
is the bounded NCR used by selection: mathematically it is in `[0,1)` for
finite nonnegative linear ratios even when the e-graph ratio exceeds 1 (the
`f64` result can round to 1 at the extreme). The code checks that range only
with `debug_assert!`; callers of the Rust API must uphold it in release builds.
Final result ranking never uses this floating-point value; it remains the
integer lexicographic key `(size, variant_mass)`.

`a_n` and `b_n` are the state's own representative sizes. Landmarks: perfect
compression scores 1, the bare no-sharing result (`size = a + b`) scores
`1 - x_target`, unbounded size approaches 0. The scale is `b_n`, not `b_n - a_n`,
so the no-sharing landmark is stable across states.

### 2.5.1 Normalization and convergence requirements

Since `a_n` and `b_n` are constants of the state, the real-valued formula is
strictly increasing before reward inversion. Thus, mathematically, for any two
candidates at one state
`size(t1) < size(t2) <=> reward(t1) > reward(t2)`. Finite-precision `f64`
evaluation can collapse extreme values to a tie, as noted above; it does not
reverse the final integer objective. Subject to that boundary, the normalizer
satisfies the bounded-reward assumption without changing the size ordering.

Expectation must come before normalization. Aggregation needs the additive unit,
because AND combination and expectation commute only under linear maps;
selection needs a bounded unit. The only safe place for a nonlinear map is a
comparison after which no further composition occurs, that is, the within-state
argmax. Averaging *normalized* rollout rewards, as vanilla game MCTS does, is a
different and risk-sensitive objective: by Jensen it can prefer worse expected
size with greater variance. It is prohibited here.

The real-valued selection model converges to a minimum-size action provided:

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

This is a mathematical convergence argument under A-F, not a theorem checked
by `au-verus`. In particular, consistency on the shared cyclic graph and the
limit argument for the selectors remain unverified; finite differential tests
do not establish asymptotic convergence.

### 2.5.2 Verification properties

The test suite pins these finite properties: returned terms are valid
generalizers (`au_adversarial_correctness.rs` re-materializes both projections);
pair-mode root Exact agrees with the independent enumerable oracle
(`au_oracle.rs`); UCT never beats pair-mode root Exact on the differential
corpus, and a UCT certificate agrees with it on those corpus instances
(`au_differential.rs`); repeated runs
of one configuration agree (determinism, 5.7); mark and restore rewind every
layer together (`au_semi_persistence.rs`); and transport flows are feasible and
minimal (`au_transport_props.rs`).

The UCT/Exact equality check is a property of that finite corpus, not the UCT
certificate contract. The cyclic regressions in
`au_adversarial_correctness.rs` and `au_deep_term_stress.rs` deliberately show
side-mode UCT and Exact closing at a worse policy-relative optimum than
pair-mode root Exact.

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

`U(n)` is the state's immutable first rollout estimate, or the static estimate
used until a deferred rollout replaces that initialization. `N(n,a)` is a
parent-local `u64` action-edge count; traffic reaching the child through another
parent does not change it. The separate `u64` child-visit counters on an AND
node record refinement effort for its selector and are not multiplicities in
the value equation. `(min_size,max_size)` is copied once from the state's two
`bs` values and remains immutable for the life of that statistics node.
Transport AND nodes replace the displayed fixed sum with the current
quantized-cost flow's argmin and then recompute its value from unquantized child
`Q`s.

`Q(n)` is the mean of the children's *current* values under the state's own
policy, regularized by one unit of weight on its own rollout estimate. Being a
pure function of the children's present values, it cannot double-count a node
reached along many paths, and a stale value corrects itself when the node is next
visited. Staleness can change finite-budget selection and therefore result
quality, but it cannot manufacture an unachieved term: incumbents are assembled
separately from real child terms. An `Exact` completion assertion additionally
depends on the closure/action-accounting logic in 9.5; idempotent value
recomputation alone does not establish certificate correctness. This is the
scope in which path-only value updates are used (3.3.3).

### 2.6.1 Numeric boundaries

`Q` and `U` are `f64` search statistics. Integer-valued sums cease to be exact
above `2^53`; this can affect selection order but cannot alter the final
integer quality or make an unachieved term an incumbent. Transport selection
quantizes each finite `Q` as `round(q * 2^20)`. While the scaled magnitude stays
below the implementation's `2^96` headroom, one arc is perturbed by at most
`2^-21` per transported unit. For total transported mass `M`, a flow's summed
quantized objective can therefore differ from its real-valued objective by an
amount proportional to `M`; near-tied flows can change order within that
cumulative error. The selected flow's displayed `Q` is then recomputed from the
original floating-point child values. That headroom is only `debug_assert!`ed.
The Rust float-to-`i128` cast saturates in release for larger statistics, so
neither bound is claimed beyond it.

Final result-term `size` and `variant_mass` use saturating `u32` arithmetic, so
totals at or above `u32::MAX` tie at the worst representable quality instead of
wrapping. Snapshot `bs` uses a different convention: `u32::MAX` is a sentinel,
so a candidate reaching it is not admitted as a finite representative.
Transport supplies and demands are narrowed to `u32`; a representation pair
with any unrepresentable supply or demand entry is omitted from the supported
action domain. Monomial totals are checked `u64` sums; overflowing that surface
width currently panics rather than returning `AuError`.

### 2.7 What correctness means here

Four distinct claims, kept separate throughout:

1. **Validity.** The returned term is a generalizer of both roots. This holds of
   every term the solver stores, at every budget (9.1).
2. **Exact optimality assertion.** In `Pair` mode,
   `Completion::Exact` means relaxation stabilized over every reachable bare
   pair and action within the implementation's asserted round bound. The code
   marks the separate global-exact slot at that point. This is intended to equal
   the global finite-term `OPT` within the supported action domain; finite
   oracles support it, but no machine-checked theorem yet connects stabilization
   or the round bound to `OPT`. In either
   side mode, completion instead certifies the selected contextual action
   graph. Transport pairs whose margins exceed the flow solver's `u32`
   capacity are not in any mode's domain (3.4.4).
3. **UCT optimality assertion.** A UCT closure certificate covers every action
   surviving its configured cycle filter. It is not a global `OPT` claim.
4. **Comparability.** All returned terms use the same quality key and projection
   semantics even when two configurations optimize different policy domains.

A budget-exhausted run claims validity, never either optimality assertion.

All four claims are relative to the equality relation the e-graph holds when the
snapshot is taken. §2.8 states what that excludes.

### 2.8 Optimality is relative to the e-graph, not to the AC theory

Every question the solver asks is a question about the graph as it stands. It
reads members and child classes through `AuSnapshot` (4.1) and compares child
positions with `find`. It never asks whether two terms are equal in the AC
theory. So a reported optimum is optimal for the relation the graph holds, and
that relation is sound but not complete for `≈_AC`: it is exactly the relation
`ac-congruence-completeness.md` Part I shows plain recanonicalization plus
congruence closure computes.

What plain mode does give the solver is every AC fact that is a property of one
node, because those are representation facts settled at build time: argument
order, flattening, multiplicity, the count clamp, and the dropped unit
(`ac-algebraic-properties.md`). AC action generation is then AC-aware in the
sense of 3.4.4, choosing child pairings by min-cost transport over canonical
monomials. The gap is narrower than "plain mode is not AC-aware". It is exactly
the erased class reference of `ac-congruence-completeness.md` §3: an equality
between two AC nodes that follows from grouping a *known sub-sum* out of one of
them, where flattening removed the sub-sum's class reference and congruence has
nothing left to follow.

**The failure is one-sided, and it is the bad direction for the use case.** A
missing AC consequence puts two AC-equal subterms in different classes, so the
solver finds no common action at that position and emits `Variants(s, t)` priced
at the full hidden mass. The reported anti-unifier is therefore LARGER than the
AC optimum, never smaller: the solver over-reports disagreement and never invents
an equality, since canonization and congruence only assert real AC consequences.
For the formalization-diagnosis use (8, `au_formalization.rs`) that is the
expensive direction. A reported difference that the theory does not have points a
reader at a part of a formalization that is in fact stable.

**Measured.** The §4a containment case wrapped in one common operator, so the
anti-unifier has a backbone and the only candidate disagreement is the AC-equal
pair:

```text
(union (add a b) c)          ; add is :assoc :comm
(union (add a b d) n)        ; AC entails n = add(c, d)
(antiunify (g n) (g (add c d)) :algorithm exact)
```

| mode | flag | reported |
| --- | --- | --- |
| plain | none | `:size 5 :cr 0.7500` — `(g (Variants n (add c d)))` |
| eager | `--derive-ac-eqs` | `:size 2 :cr 0.0000` — `(g n)` |
| lazy | `--lazy-ac-eqs` | `:size 5 :cr 0.7500` — identical to plain |

Nothing about the solver differs across the three rows. What differs is the
equality relation it was handed. `tests/au_ac_completion_modes.rs` pins all three
sizes exactly, by bracketing each with a `checkau :max_size` that must pass and
one that must fail, since `checkau` bounds from above only.

**Lazy completion contributes nothing here, and this is structural.** The lazy
transaction is opened only by `CheckEq` and `CheckNeq`; every other command calls
`lazy_txn_close()` first (`interpret.rs`, the command loop in `run_checked`),
which restores the graph and discards the derived nodes. `AntiUnify` and
`CheckAu` are not equality checks, so the close runs, and only then does
`AuSnapshot::new` read the graph. The snapshot is the plain graph.

Routing the solver through the lazy path instead is not a small change, and the
reason is the shape of the search rather than the plumbing. Lazy mode is
goal-directed: it installs one pair via `set_cc_goal` and stops completion the
moment that pair joins (`ac-congruence-completeness.md` §13). Root Exact has one
OR node per reachable ordered class pair (2.1) and no single pair to install,
because not knowing in advance which pairs matter is the search. A lazy variant
would be one goal-directed completion search per visited pair, each inside its
own mark and restore, discarding between pairs exactly the accumulated
completion state that makes consecutive equality checks cheap. Eager completion
pays the closure once for the whole graph and hands the solver a snapshot it
reads with `find`.

**Consequence for reporting.** The three modes are not three points on one
speed axis. Plain and lazy hand the solver the same relation; eager changes what
the answer means. Any size, `cr`, or benchmark number for an AC workload must
therefore name its completion mode, and any claim that a reported difference is
real needs eager.

## 3. The two algorithms

### 3.1 Shared building blocks

Both solvers use the same action semantics (3.4), term representation (4.4),
quality key, and requested cycle policy. Pair-mode root Exact uses bare-pair
states. Side-mode root Exact and every hybrid call use contextual states; UCT
uses those states plus the session result table. Pair-mode session root Exact
records the stronger global certificate scope. Side-mode Exact and delegated
Exact record contextual exactness.

### 3.2 Exact under the selected cycle policy

For `Pair`, `exact_fixed.rs` first discovers the root-reachable bare pair graph
with an iterative queue. It records non-AC actions directly and AC/ACI
representation pairs as transport problems whose cells name child pair states.
Unlike MCGS, this discovery path does not run a zero-cost feasibility flow
before recording a transport descriptor; after count narrowing, infeasible
problems are ignored when a relaxation round invokes the solver. Discovery
interns each ordered pair once, so graph construction terminates independently
of grammar cycles.

Every state starts with an achieved terminal witness: the best admissible ground
term when the classes agree, otherwise `Variants(best(l), best(r))`.
Synchronous rounds evaluate every unpruned structural action and exact min-cost
transport against the previous round's child qualities. Strict improvements
carry a newly composed finite term. The pair-repeat lemma of 2.2 is the
unverified argument used to bound the rounds by the number of reachable pairs;
equality of consecutive vectors is the implementation's completion condition.

A wall-clock deadline is checked during graph discovery, baseline construction,
and relaxation. Expiry returns the last fully achieved root incumbent with no
completion claim. Projection pruning can skip an action only when its static
size bound strictly exceeds that incumbent.

For `AncestorOnly` and `CurrentInclusive`, root Exact uses `run_exact` in
`exact.rs` from an empty side context. `run_exact_at` is the same contextual
depth-first engine entered at an existing UCT state for bounded delegation; it
accepts either a side context or a pair context. Its completion is relative to
the supplied context and mode.

### 3.3 Monte-Carlo graph search

One playout: descend by selection from the root, expand the first unhandled
action met, estimate fresh children by rollout, backpropagate along the path
taken, then propagate any closure through the reverse edges. Repeat until the
budget is spent or the root closes.

#### 3.3.1 Fully expanded, terminal, and expansion

A state is **terminal** when `l == r`, when it has no surviving action, or when
its stored contextual result is already exact. The separate global result does
not make a UCT state terminal because its witness may use a filtered action. A
terminal state is closed at birth and its value is its stored result's size,
permanently. A state is **fully expanded** when every action slot is handled,
meaning realized or excluded. A per-state cursor avoids rescanning the realized
prefix and advances across each excluded slot once. Locating the next slot is
amortized constant work per handled slot, but realizing a structural slot
currently scans the cached action list to map the surviving action index and
then pays the action's child-construction cost; expansion as a whole is not
O(1).

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
solver. A call that completes contributes a contextually certified exact suffix;
if `hybrid_node_budget` is exhausted, it contributes only the call's feasible,
uncertified incumbent. The first answer is therefore a greedy prefix with a
delegated suffix, whose certificate status is recorded separately.

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

Positional zip of same-operator, same-arity member pairs. Each member-pair zip
contributes a candidate whose children are the positional pairs; the final
deterministic dedup removes equivalent candidates.

#### 3.4.2 Commutative binary operators (sorted pairs)

Members are stored canonically as `(min, max)`, so each member pair contributes
up to two orientations. The crossed orientation is suppressed when repeated
children make it identical to the positional orientation, and final
deterministic dedup can remove equivalences across member pairs.

#### 3.4.3 Associative operators (sequences)

Positional zip when the two sequences have equal length, none otherwise.
Unequal-length factoring is future work (`doc/future/au-associative-operators.md`).

#### 3.4.4 AC operators (multisets), and why canonical storage wins

An AC class member is a sorted multiset of `(class, multiplicity)` pairs. One
candidate is one *representation pair* of monomials, and its children are the
cells of a min-cost flow between the two multisets, so assignments are solved
rather than enumerated. The implementation materializes the
`rows * columns` cell table; it does not materialize the factorial family of
complete pairings.

MCGS turns a representation pair into an action slot only if a zero-cost
feasibility flow succeeds with cycle-blocked cells forbidden. A pair can have
legal cells and still be Hall-infeasible; excluding it prevents an unrealizable
slot from blocking closure. Contextual Exact instead builds and solves the cell
problem while visiting the pair, and pair-mode fixed-point Exact records the
narrowed descriptor during graph discovery and tests feasibility during
relaxation. These paths share representation and flow semantics, not one common
admission step.

Cell costs enter the solver as integers. For value estimates they are quantized
as `round(q · 2^20)`, which perturbs each arc by at most `2^-21` and keeps the
integer termination argument that floating-point costs lack; the reported value
is recomputed from the unquantized child values, so quantization decides the
argmin flow only. For composition the costs are the children's lexicographic
qualities directly.

Multiplicities are carried at the surface width and narrowed at each solver
path's transport boundary. In MCGS that boundary is the feasibility gate and
the resulting descriptor stores the narrowed vectors. Pair-mode Exact narrows
during graph discovery; contextual Exact narrows when it constructs the final
transport problem. An unrepresentable pair contributes no candidate
(Appendix C.2).

#### 3.4.5 ACI operators (sets)

Members are sorted and deduplicated, so multiplicities are all one and an
equal-cardinality flow degenerates to a bijection between the two sets. With a
usable declared identity, unequal cardinalities are equalized by padding the
shorter side and the excess elements pair with that identity, producing
variants. Without an identity, the unequal-total representation pair is
omitted; the always-available whole-pair generalize action remains.

#### 3.4.6 Literals

Same-value pairing only; a literal has no e-node children, so the action is
terminal.

### 3.5 Algorithm portfolio and configuration axes

The two solvers are one portfolio, and the configuration surface (section 7)
selects a point in it: exact search alone, graph search alone, or graph search
that delegates admitted subproblems to exact search and inherits their proofs.
No current timing crossover is claimed. The retained corpus predates
pair-mode fixed-point Exact; every algorithm and cycle-policy combination being
compared must be rerun from one revision under the Criterion/corpus protocol
before performance guidance is restored.

## 4. Data structures

### 4.1 Read-only e-graph interface needed by the search algorithm

`AuSnapshot` is the frozen view the solver reads: class lookup for a node,
class members by operator, `bs(c)` (2.4), the reachability structure, operator
metadata (arity, commutativity, algebraic kind), and literal values. It borrows
the e-graph immutably for the session's lifetime, so later mutations are not
observed and every derived quantity stays consistent.

### 4.2 The search-space layer

`SearchSpace` holds the states: aligned arrays for each state's left and right
class, two opaque context-id slots, and the two representative sizes; separate
interners for side-class contexts and ordered-pair contexts; and the cycle
mode. Side modes use both context-id slots. Pair mode stores its pair context in
the first and leaves the second empty. `get_or_insert_or_node` is what makes
sharing real: a state is identified by the pair and both context ids, so two
paths that agree on the full policy state land on the same node.

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

`BestResults` maps each *state* to two term/quality slots. The contextual slot
is consumed by UCT, side-mode root Exact, and delegated Exact; its exactness bit
closes the configured contextual graph. The global slot is consumed only by
pair-mode root Exact and has its own completion bit. Pair-mode root Exact
warm-starts from the better achieved slot, but a global result is not injected
into a closed contextual parent. This keeps the contextual finality assertion
meaningful even when the global slot is strictly better. Keying by state lets
both slots outlive one run in a session (4.7).

### 4.6 Well-formedness

The invariants the arenas maintain are stated as assertions and debug checks
rather than machine-checked specifications: aligned columns have equal lengths,
realized action slots form a prefix under the cursor, open counts equal the
number of unresolved slots, and every reverse edge names an existing AND node.
Verifying them in the sense of `containers-verus` is future work.

### 4.7 Whole-search marks, restores, and sessions

`SearchSession` owns the space, the term pool, the results table, the action
cache, and the statistics overlay, and exposes one `mark` and one `restore` for
their search-relevant state. Restore is two-phase: every component token is
validated against its container and branch genealogy BEFORE any layer is
mutated, so a foreign or abandoned token cannot leave a partial restore. Layers
then restore in reverse dependency order. `HybridStats` is cumulative
diagnostic telemetry outside those arenas; restore intentionally does not
rewind its call, proof, or duration counters.

## 5. Rust implementation

### 5.1 Module layout

`session.rs` (public API and configuration), `space.rs` (states, contexts, cycle
filtering), `actions.rs` (3.4), `ac_repr.rs` (AC and ACI representations),
`transport.rs` (min-cost flow), `exact_fixed.rs` (pair-mode root Exact),
`exact.rs` (side-mode root Exact and contextual delegation), `mcgs.rs` (3.3), `terms.rs` (4.4),
`results.rs` (4.5), `estimates.rs` (the bounds of 9.2), `census.rs` (action
counting, independent of any run), `exact_memo.rs` (the contextual clean-solve
memo of 9.4), `reward.rs` (2.5), `egraph_api.rs` (4.1), `pretty.rs`, `dump.rs`.

### 5.2 Container primitives

Persistent arena columns use the container crate: `VecP` for mutable columns,
`AppendOnlyVec` for immutable ones, `SpMap` for most indices, and typed spans
for flattened pools. Some derived storage remains ordinary Rust allocation:
`ActionCache` keeps action lists in a `Vec`, and `ExactMemo` rebuilds a standard
`HashMap` index from an append-only log on restore. The session token covers the
container logs and the corresponding ordinary-storage lengths; this chapter
does not claim that the whole AU layer is Verus-verified merely because its
primitive containers are.

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

Without a wall-clock deadline, both solvers are deterministic. There is no
randomized tie-breaking: selection ties resolve to the smallest index, action
order is the generation order, and transport optimization uses integer costs
(UCT quantizes estimates as described in 2.6.1). The deterministic corpus gates
compare runs without a deadline. `exact_deadline` deliberately observes
`Instant::now()`, so the amount of completed work, incumbent, and completion
status can vary with host scheduling.

## 6. Script commands

`(antiunify e1 e2)` runs the configured solver over the two expressions'
classes and prints the term, `:size`, the linear `:cr`, and `:completion`. It
does not print `variant_mass`, so the complete lexicographic quality is
available through the Rust result pool rather than this command's output.
`(checkau e1 e2 :max_size n)` additionally asserts a size bound, which is what
makes the `.egg` fixtures self-checking. Both accept `:algorithm exact|uct` and
`:cycles sides|sides-current|pair`; the cycle option defaults to `sides`.

## 7. Configuration

`AuConfig::default()` selects UCT with the `LctAnd` child selector and without
the optional pruning, closure, hybrid, memo, or deferred-seeding paths.
Dedicated finite differential tests exercise each of those paths and selected
flag combinations. They do not exhaust the configuration product or prove the
flags' arguments universally. Cycle policies and finite playout budgets are
intentionally allowed to change the answer or its certificate.

| field | default | effect |
| --- | --- | --- |
| `algorithm` | `Uct` | Exact under the selected cycle policy (3.2) or UCT graph search (3.3) |
| `cycle_mode` | `AncestorOnly` (`:cycles sides`) | shared by root Exact, UCT, and both hybrid paths; alternatives are `CurrentInclusive` and `Pair` (2.3) |
| `playouts` | `1000` | UCT playout budget |
| `exploration_constant` | `sqrt(2)` | OR/AND exploration term |
| `x_target` | `0.8` | NCR no-sharing landmark; Rust callers must keep it in `(0,1)` |
| `and_selector` | `LctAnd` | AND-child effort allocation (3.3.5) |
| `exact_deadline` | `None` | optional wall-clock anytime bound for root Exact (3.2) |
| `exact_pruning` | `false` | static projection pruning in root Exact (9.4) |
| `context_subsumption` | `false` | support-checked reuse for side-context Exact; pair contexts disable it |
| `dominance_pruning` | `false` | generalize dominance at state creation (9.4) |
| `closed_bit` | `false` | maintain closure and skip resolved subgraphs (3.3.7) |
| `hybrid_exact` | `false` | exact solving of admitted UCT subproblems |
| `hybrid_threshold` | `4096` | reachable-pair admission estimate; inert while hybrid Exact is off |
| `hybrid_action_threshold` | `u64::MAX` | entry-state action-count admission estimate |
| `hybrid_node_budget` | `None` | optional deterministic hard bound for one hybrid call |
| `rollout_hybrid` | `false` | fire the hybrid trigger from inside a rollout (3.3.2) |
| `session_exact_memo` | `false` | share clean side-context solves across exact calls (9.4) |
| `live_incumbent_pruning` | `false` | exclude arms against the live incumbent; requires `closed_bit` |
| `interval_bounds` | `false` | make arm bounds dynamic; requires live-incumbent pruning |
| `static_child_seed` | `false` | seed fresh children statically and defer their rollout (3.3.2) |

## 8. Testing

`au_differential.rs` holds the finite soundness gates. Each behavior-changing
UCT flag runs over the fixture corpus at several budgets and checks against
explicitly pair-mode root Exact. On that corpus, a reported UCT certificate also
lands on the root-Exact quality. This is intentionally not generalized into the
public UCT contract: cycle filtering can exclude a better finite derivation.
A flag that trades per-playout quality for per-playout cost asserts validity,
the corpus comparison, and determinism instead of fixture equality. These are
correctness checks; host-sensitive performance comparisons require the
Criterion protocol and are not inferred from test-process elapsed times.

Beyond those: `au_adversarial_correctness.rs` re-materializes both projections
into a fresh e-graph and checks they land in their source classes;
`au_metamorphic.rs`, `au_convergence_props.rs`, and `au_transport_props.rs` carry
the property tests; `au_deceptive.rs` builds the deceptive families and asserts
the constructed misranking is the one the search actually faces;
`au_semi_persistence.rs` checks that mark and restore rewind every
search-relevant layer together (not cumulative diagnostics);
`au_conformance.rs` runs the `.egg` fixtures.

`au_oracle.rs` checks the exact solver against an independent traversal rather
than against itself. On small acyclic, free-constructor fixtures with no
subsumed members, it minimizes a certificate-carrying extension of Plotkin's
first-order anti-unification over every pair of enumerated ground terms. A
mismatch is represented as `Variants(s, t)` and priced by the complete hidden
mass `size(s) + size(t)`, not as a size-one syntactic variable. The file
enumerates terms straight from the e-graph without using the snapshot's member
list, runs that recurrence on every pair, and asserts pair-mode Exact agrees.
This is finite evidence for the production quality objective on that fixture
domain, not evidence about the standard variable-count size of an lgg. The
oracle does not use the solver's member ordering, so a
representative-dependent answer would disagree on a checked fixture. It does
not test the production distinction between admissible non-subsumed members and
all retained e-nodes, AC/ACI quotient semantics, or unenumerated instances. A
fixture whose term set is unbounded or too large is
skipped rather than truncated, because a truncated enumeration is not an oracle,
and the test asserts a floor on how many fixtures were actually enumerable so it
cannot pass by skipping everything. The same file pins that the reported size
is the size of the returned term and that enabling root projection pruning
leaves the optimum unchanged, which is where an inadmissible bound would show
up. `context_subsumption` has no execution effect for pair-mode root Exact,
whose states are already bare pairs; side-context Exact and delegated Exact do
execute the support-checked reuse path.

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

*Argument.* If `l == r` the supported optimum is the class's best admissible
ground term, of size exactly `bs(l)`. If `l != r` the classes are disjoint, so
no variant-free term projects into both; any generalizer contains at least one
variant node above a subterm at least as large as the larger side's minimum.
Since `bs` is a least fixpoint over admissible, counter-representable ground
terms rather than an incumbent (2.4), the bound holds at every supported state
under every context, and does not assume the projections are optimal
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
- **partial completion bound** (contextual Exact delegation): solved children
  at their true size, unsolved children at `lb`. Substituting a solved child's
  true size for its bound only raises the sum, so a mid-action re-check is at
  least as tight as the initial one. Root Exact uses the static arm/transport
  bound because its rounds evaluate all children synchronously.

Saturating arithmetic keeps every accumulation a lower bound. A saturated
`u32` bound exceeds every incumbent below `u32::MAX`; against a saturated
incumbent the strict comparison does not prune. A pair with no admissible
finite member contributes no supported term.

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
| generalize dominance | static arm bound > stored generalize size | the generalize action is always available at that achieved value (2.1), so an arm that cannot come in under it can never be optimal |
| live-incumbent exclusion | arm bound > the state's current incumbent | the same argument against a tighter target, valid because the incumbent is achieved (9.1) |
| interval exclusion | dynamic arm bound > incumbent | the dynamic bound is admissible and monotone (9.2), so it can be tested at any time |
| root-Exact projection pruning | static arm or transport bound > pair incumbent | the bound is admissible; equality cannot prune because variant mass may still improve (9.3) |
| contextual-Exact branch and bound | partial completion bound > incumbent | the partial bound is admissible by 9.2 and obeys the same strict comparison |
| resolved-subtree skip | the child or action is closed | a resolved subgraph can change no value, no stored term, and no certificate |

Two rules need more than a line.

**Context subsumption in side-context Exact.** A solve of a contextual state is
*context-clean* when its entry context removed no candidate anywhere in the
winning derivation; the delegated solver records that derivation's support, the
classes it descended through on each side. A clean solve of the bare pair
`(l, r)` may then be reused at any other contextual state with the same pair
whose entry contexts are disjoint from that support. Pair-mode root Exact needs
no such optimization because its state key is already the bare pair.

*Argument.* Contexts only remove candidates, so `V(ctx) >= V(empty)` for every
context. If the stored derivation's support is disjoint from `ctx`, every step of
that derivation remains available under `ctx`, so it re-executes there and
`V(ctx) <= V(empty)`. Hence equality, and the stored term is the new state's
optimum too. If the supports intersect, the stored term is still *valid*
(validity does not depend on contexts), so it may be offered as an incumbent, but
it must not be marked exact. With `session_exact_memo` the same entries persist
across exact calls in a session, which changes what is reused and not why it is
sound. This support record has independent left/right sets, so pair-context
subsumption and session-memo reuse are disabled until the record preserves
ordered-pair correlations.

**Exact subproblem solving.** When a state passes two admission tests, a
rectangle of reachable class pairs and the state's own action count, the exact
solver runs on that state's own full policy state: same class pair, same side or
pair context, same cycle mode, same generators. The implementation treats a
completed call as the optimum *of that contextual state*, which is exactly what
the contextual exactness flag asserts. Finite differential tests exercise
completed delegated calls against fixture references, but there is no
independent exhaustive oracle for arbitrary contextual states. A call that
exhausts its node budget returns a feasible incumbent with no proof attached.

The two admission tests are workload estimates, not hard complexity bounds.
`reachable_pairs` bounds the rectangle of bare class pairs but can undercount
contextual states, and the action threshold counts only the entry state's
actions, not descendant fan-out. They screen complementary observed families;
only a configured `hybrid_node_budget` hard-bounds node entries in one call.
That budget defaults to `None`, so hybrid admission by itself does not prove
that a playout cannot enter a long exact solve.

### 9.5 Certificate bits, and why closure is not `L == U`

**The closed bit** lives in the statistics overlay and is structural: every
action slot of this state is resolved, meaning realized and closed, or excluded
by a bound. It is run-scoped and rewinds with the overlay. The root's closed bit
is the run's internal certificate: when set, its accounting says every reachable
action was realized or excluded by a bound. The reported term is then marked
optimal by the implementation. This is not an externally checkable or
machine-checked optimality proof.

**Contextual exactness** lives in the results table. It says the stored
incumbent is no worse than every result in that state's configured contextual
action graph. It is set when the state is trivial, when a contextual Exact call
completes, when a context-clean result is reused under a disjoint context, and
when UCT closure reaches it. It is session-scoped, so a later UCT run finds
such a state terminal at creation.

**Global exactness** is the stronger results-table bit set only when pair-mode
root Exact stabilizes. Its separate term slot may be strictly
better than a contextually exact result without contradicting or mutating that
filtered result; the filtered certificate never quantified over the newly
admitted derivation. A globally exact slot cannot improve.
`global_offer_can_improve_a_contextually_exact_result` pins the two result
slots and certificate bits independently. `warm_exact_honors_the_session_cycle_mode`
checks that UCT and warm Exact share one cycle policy and that only pair mode
sets the global certificate. These are finite implementation tests, not a proof
that every solver sequence preserves certificate scope.

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
resulting term is `x + V1 + V2` with two variant positions. The cell-cost matrix
is materialized, but complete assignments are not enumerated: the assignment
is the flow's argmin, and the flow's cost is the AND node's value.

## Appendix C. Worked examples

### 9.6 Target optimum theorem and current proof boundary

The intended high-level theorem is stated here because everything above is
about how the search prunes and nothing above, by itself, proves what it
converges to. The equality below currently has a prose argument and finite
implementation evidence. It is not a theorem established by `au-verus`.

**The ideal objective.** For a class `C`, write `terms(C)` for the mathematical
set of finite ground terms `C` represents, and `bs(C)` for the size of its
smallest term. For free-constructor ground terms `s` and `t`, define
`cplgg(s, t)` as Plotkin's structural recurrence with an annotated mismatch:
matching roots recurse positionally, while a mismatch produces
`Variants(s, t)` carrying both complete projections. Its generalized backbone
is Plotkin's lgg, but its quality is not the standard syntactic lgg node count.
An ordinary node contributes 1; a `Variants` node contributes no node of its
own but contributes `size(s) + size(t)` through its hidden projections, and the
same hidden mass contributes to `variant_mass`. Let
`q_cert(s, t) = quality(cplgg(s, t))` under that production key. Define

```text
  OPT(A, B) = lex-min over s in terms(A), t in terms(B) of q_cert(s, t)
```

**Well-definedness is immediate from that definition**, and this is worth saying
plainly because it is easy to mistake for an open question: `terms(C)` is a set
determined by the class, and no representative, member ordering or union-find
survivor appears anywhere in `OPT`. What needs proof is not that `OPT` is well
defined but that the solver computes it, since the solver *does* work with
members and representatives.

Production has a narrower executable domain that the refinement theorem must
state explicitly: the snapshot grammar drops subsumed members, `bs` admits only
expanded sizes below its `u32::MAX` sentinel, transport entries must fit `u32`,
and AC/ACI terms are interpreted through canonical monomials plus optional
identity padding. Thus the unqualified ideal equality below is a target theorem,
not the exact contract already established for every Rust input. A production
theorem must either define `terms_adm(C)` with these restrictions and prove
optimality there, or prove that each restriction preserves the ideal `OPT` under
explicit preconditions.

**The bounded recurrence.** For a root-reachable pair `p = (A, B)`, let `G(p)`
be the achieved generalize quality (or the best represented term when
`A == B`). Define:

```text
  D_0(p)     = G(p)
  D_{d+1}(p) = lex-min of
      D_d(p)                                             -- stop at depth d
      (1, 0) + sum over i of D_d(A_i, B_i)              -- structural action
```

The structural line ranges over pairs of members `n in A`, `m in B` with the
same operator and arity; `A_i`, `B_i` are their child classes. AC/ACI replaces
the positional sum with the minimum feasible transport sum. `G(A, B)` is
`(bs(A) + bs(B), bs(A) + bs(B))` when the classes differ, because a generalized
position hides both sides and the smallest hidden pair minimizes both
components.

Unlike an unconstrained recursive equation on a cyclic graph, every `D_d` is
constructive and unambiguous. It is the minimum achieved quality among
derivations of depth at most `d`, with an attaining term carried alongside it.
If the reachable pair graph contains `N` states, pair-cycle erasure (2.2) says
that a minimum-size derivation needs fewer than `N` structural edges on every
path. Cold pair-mode root Exact computes these vectors synchronously until they
stabilize and defines `D*(p) = D_N(p)`. A session solve can warm-start the root
from an already achieved term, so its implementation invariant must generalize
the depth-indexed cold recurrence while preserving attainability and the final
fixed point. The two side modes intentionally solve their smaller contextual
recurrences instead.

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

**Target theorem.** `D*(A, B) = OPT(A, B)` wherever both term sets are
non-empty.

The paper argument has two inequalities.

`OPT <= D*`: every finite round stores an achieved value. Induct on `d`. The
base is achieved by the two smallest terms (or the best common term). A
structural update at members `n, m` combines child witnesses from round `d`;
the assembled terms lie in `A` and `B`, and their certificate-carrying Plotkin
quality is `(1, 0) + sum`, by the lemma. The implementation-level theorem must
also cover transport assembly.

`D* <= OPT`: every finite represented term pair induces a finite derivation in
the pair graph. Induct on `|s| + |t|`: a root mismatch uses `G`; a root match
uses the corresponding member-pair action and the child inductions. Thus some
`D_d(A, B)` is no worse than that pair's `q_cert` quality. The pair-cycle-erasure
lemma supplies an equally good pair-simple derivation for a minimum witness, so
`d < N` suffices and `D_N <= OPT`.

**Conditional corollary (edge counts are the recurrence, not an optimization).** If
the target theorem and recurrence construction are established, `D*` is a
function of the class pair, so a child pair reachable by several paths has one
value. Pricing an AND node at `1 + sum over children of count * D*(child)` is
therefore the same quantity as the tree unfolding, and counting edges rather than
nodes needs no separate justification. §4 describes the memo that realizes this;
the corollary is why it is sound.

**Conditional corollary (representation independence).** If `D* = OPT`, and `OPT` mentions
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
  certificate-carrying Plotkin result no worse than hiding both terms.

**Why this does not prove `D* = OPT`.**

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

1. Model the finite root-reachable ordered-pair graph and prove that the
   generalize action makes every state's finite action set nonempty.
2. Define `D_d` constructively and prove the round invariant: its value is the
   minimum over depth-`d` finite derivations and its stored term attains it.
3. Prove pair-cycle erasure: replacing an ancestor occurrence of a repeated
   pair by its descendant preserves projection validity and strictly reduces
   size. Derive the `N`-state depth bound and stabilization.
4. Prove action completeness by mapping every represented positional term pair
   to a finite pair-graph derivation, and strengthen structural assembly with
   the required `q_cert` postcondition.
5. Combine attainability (`OPT <= D*`) with the existing lower-bound direction
   (`D* <= OPT`) in one exported equality theorem, then refine the Rust
   synchronous loop to `D_d`.
6. Separately refine the positional model to production AC/ACI transport,
   identity padding, multiplicities, bounds/pruning, and certificate scopes.
   UCT cycle filtering must be specified as an intentionally smaller domain,
   not justified as preserving all finite derivations.

Until those steps are complete, `au_oracle.rs` is finite evidence for the Rust
exact solver: it enumerates `OPT` on small acyclic, non-subsumed
free-constructor fixtures, checks `lb_pair` against that optimum, and tests
representation independence there. It is not a universal proof. The maintained
theorem and production-refinement acceptance criteria are in
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

Multiplicities are carried at the surface width and narrowed at the transport
boundary. MCGS narrows in the feasibility gate that produces its descriptor;
pair-mode Exact narrows while building its graph; contextual Exact narrows when
it forms the solve request. A pair whose entries the transport solver cannot
represent contributes no candidate. Only the MCGS descriptor guarantees that
all later consumers reuse the exact vectors accepted by an earlier feasibility
gate.

---
[← Ch 18: Semi-Naive Evaluation](18-semi-naive-evaluation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 20: Index Selectivity →](20-index-selectivity-and-delta-suffixes.md)
