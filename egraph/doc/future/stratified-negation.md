# Stratified Negation

**Status**: design for future work; nothing in this document is
implemented. It depends on Datalog relations (`datalog-integration.md`),
which the engine does not have.

## 1. Stratification as Generation Boundaries

A stratum boundary can coincide with a generation boundary, but the existing
semi-persistent `mark()` is only a rollback token. It records how to restore
the mutable state; it does not expose the marked state for concurrent queries
after later writes. Therefore stratum `k+1` cannot query a token as if it were
an immutable `G_k`.

The implementation needs a frozen or versioned lower-stratum view containing:

- relation indexes at the completed stratum;
- the equality/canonicalization mapping under which those indexes were keyed;
- ownership and lifetime rules that keep the view queryable while the live
  graph advances; and
- a policy for memory reclamation after dependent strata finish.

Stratum `k` runs to a genuine fixpoint and publishes that view. Stratum `k+1`
uses it for every negative lookup. The intended soundness statement is that
`not R(a, b)` means the canonical tuple was absent from the completed,
immutable lower-stratum relation. That statement becomes valid only after the
fixpoint and snapshot-refinement obligations are proved.

## 2. Static Stratification Check

Before execution, build a dependency graph over relations:

- a positive edge `A ->+ B` if a rule with `B` in its head has `A` in its body
  positively;
- a negative edge `A ->- B` if a rule with `B` in its head has `A` in its body
  negatively.

A valid stratification exists iff no strongly connected component contains a
negative dependency. Compute SCCs of the graph while retaining edge polarity,
reject a negative edge whose endpoints lie in one SCC, then topologically
order the condensation DAG. Assign strata so positive edges are nondecreasing
and negative edges are strictly increasing. A plain topological sort of the
original graph is insufficient because positive recursion within one stratum
is valid.

## 3. Negative Literals in the Join Engine

Negative literals are post-filters applied after the positive leapfrog join
completes. They do not contribute iterators.

Every variable appearing in a negative literal must already be bound by a
positive literal in the same rule body. Check this statically so a negative
literal only verifies absence for an already-bound tuple.

After the positive join produces a candidate binding, canonicalize each
negative tuple under the frozen lower-stratum equality view and perform a point
lookup in that view's relation index. A hit discards the candidate. Lookup
complexity is backend-dependent: expected O(1) for a hash index, O(log n) for
an ordered tree, or another documented bound for a dense/sorted
representation.

## 4. Interaction with E-Class Merging

Stratum `k+1` may merge live e-classes that appeared as arguments in `G_k`.
Looking up with the live representative against an index keyed by the old
representative is stale; re-keying the old index would also destroy the frozen
semantics.

The robust rule is that negative canonicalization and lookup both use the same
frozen equality view. Base-value arguments satisfy this naturally when their
equality is immutable. For sort-typed arguments, either retain the lower
stratum's representative mapping or restrict the language so later strata
cannot change equality relevant to a negated relation. A syntactic check that
only forbids writing relation `R` is not enough: union actions can change its
argument equivalence indirectly.

## 5. Validation Obligations

- Generated finite programs agree with a simple stratified Datalog reference
  evaluator for relation facts.
- Positive recursive SCCs are accepted; every negative cycle is rejected with
  an actionable dependency path.
- Later e-class merges cannot change a lookup in a frozen lower-stratum view.
- Mark/restore and stratum-view reclamation do not expose a partially rebuilt
  or differently canonicalized relation.
- Complexity claims name the selected index backend and include the cost of
  retaining/versioning the frozen view.
