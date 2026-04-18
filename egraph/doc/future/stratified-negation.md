#  Stratified Negation

## 1. Stratification as Generation Boundaries

The key insight is that a stratum boundary is a generation boundary.
The engine's generational structure provides exactly the right
semantics for stratified negation at no additional cost.

Stratum k runs the fixpoint loop until convergence, producing generation G_k. Stratum k+1 treats G_k as its negative database: the state captured at G_k's `mark()` is a fully rebuilt, congruence-closed snapshot. Stratum k+1 writes new facts into G_{k+1}. Negative lookups in stratum k+1 query G_k's state, which is immutable — backtracking to G_k would undo all of stratum k+1's work, so the absence of a fact in G_k is stable for the entire duration of stratum k+1.

This is sound: a negative literal `¬R(a, b)` in stratum k+1 means "R(a, b) was not derived by stratum k." Since stratum k is fully saturated and its state is frozen, this is a stable truth for all of stratum k+1's reasoning.

## 2. Static Stratification Check

Before execution, the engine builds a dependency graph over relations:

- A positive edge `A ->+ B` if some rule with B in its head has A in its body positively
- A negative edge `A ->- B` if some rule with B in its head has A in its body negatively

A valid stratification exists iff the dependency graph has no cycle passing through a negative edge. This is checked by topological sort: assign each relation a stratum number such that for every positive edge `A ->+ B`, stratum(B) ≥ stratum(A), and for every negative edge `A ->- B`, stratum(B) > stratum(A). If no such assignment exists, the program is not stratifiable and The engine rejects it with an error identifying the offending cycle.

## 3. Negative Literals in the Join Engine

Negative literals are post-filters applied after the positive
leapfrog join completes. They do not contribute iterators.

### Variable safety

Every variable appearing in a negative literal must already be bound
by some positive literal in the same rule body. This is checked
statically. It ensures that negative literals never need to enumerate
candidates: they only verify absence for already-bound values.

### Implementation

After the positive leapfrog produces a candidate binding
`{?X = e1, ?Y = e2, ...}`, each negative literal `¬R(t1, ..., tk)`
is checked by canonicalizing `(t1[σ], ..., tk[σ])` under the current
substitution `σ` and performing a point lookup in G_k's frozen
hashcons for R. If the lookup succeeds, the candidate is discarded.
O(log n) per negative literal per candidate.

## 4. Interaction with E-Class Merging

A subtle case: stratum k+1 may fire union actions that merge e-classes. If a merged e-class appeared as an argument to a negated relation in G_k, the negation check was against a specific canonical id that may now be non-canonical. This would make the negative lookup stale.

The safety condition enforced by the stratification check: a
relation R used negatively in stratum k+1 must not appear as an
action target in stratum k+1 or later, and no stratum k+1 rule may
union e-classes that appear as arguments to negated R-literals. In
practice, this means:

- Pure Datalog relations (over base types) are safe: base-type equality is stable and does not interact with the union-find.
- Relations over sort-typed arguments require the more careful condition above.
- The common case — negating over a fully ground Datalog relation whose arguments are base types — always satisfies the condition trivially.

