# Datalog Integration

**Status**: design for future work; nothing in this document is
implemented. The engine has no relation declaration form (this is why
`doc/benchmarks/`'s `array` benchmark is a BLOCKED carrier).

## 1. Relations as Unit-Typed Functions

A possible logical encoding is a function
`R: (S1, ..., Sk) -> Unit`, where all successful tuples map to one unit value.
That observation does not make relations free in this engine. The current node
stores, hash-cons tables, and `IndexStore` are organized around e-nodes and
e-classes; there is no relation descriptor, unit-result protocol, relation
tuple index, or relation-specific rollback state.

An implementation must define:

- declaration metadata for arity, argument sorts, and any symmetry;
- a canonical tuple representation whose sort-typed arguments are
  canonicalized against a specified equality snapshot;
- tuple insertion and point lookup, including collision-safe equality rather
  than treating a hash as identity;
- relation indexes for joins and negative point lookups;
- mark/restore behavior for tuple storage and reconstruction of transient
  indexes; and
- change events for new or recanonicalized tuples.

Existing plain, commutative, and variadic node-storage machinery may be reused,
but that is an implementation option to measure and validate, not an already
wired relation API. In particular, a symmetric binary relation and an ACI
e-node have different logical meanings and must not be conflated merely because
both can use canonical child order.

## 2. Semi-Naive Evaluation

For each eligible rule with scanning body atoms `A1, ..., Am`, use the same
disjoint first-delta decomposition as the implemented e-matcher:

```text
DeltaRule_j:
  A1(full \ delta), ..., Aj-1(full \ delta),
  Aj(delta),
  Aj+1(full), ..., Am(full) -> head
```

The current e-matcher's delta is not a backing-vector length difference. It is
built from an explicit touched-node log, then indexed separately from the full
round snapshot. The log includes fresh nodes, recanonicalized nodes, and members
exposed by class growth; `full \ delta` is a cursor view. Datalog relations need
the analogous tuple-level bookkeeping. A relation tuple can become newly
visible because it was inserted or because equality changed one of its
canonical arguments, even when no relation-storage vector grew.

The target correctness statement is:

1. `delta` is a subset of the same frozen `full` snapshot under every index key;
2. every newly enabled eligible match contains at least one delta tuple;
3. the first-delta variants form a disjoint partition of those matches; and
4. rule shapes whose enabling event is not represented in a scanning atom's
   delta use the full matcher.

The textbook/egglog semi-naive theorem motivates this construction, but it does
not carry over merely by naming the touched log `DeltaDB`. A proof must relate
relation insertion, e-class merging, recanonicalization, fallback rules, and
the engine's frozen round indexes to those four premises. Until then, finite
naive-versus-semi differential tests are evidence, not a universal theorem.

## 3. The Fixpoint Loop

The future relation driver should preserve the implemented round-snapshot
contract:

1. Rebuild the live e-graph to plain congruence closure.
2. Build immutable full indexes for the round and, after round zero, delta
   indexes from the touched node and relation-tuple logs.
3. Clear those logs, match rules against the frozen indexes, and apply actions
   to the live e-graph. New nodes, merges, and tuples populate the next logs.
4. Discard/recycle the round indexes.
5. Stop when no action changed the live state, or at the iteration budget;
   otherwise repeat so the next rebuild makes those changes visible.

There is no implemented arena-compaction phase or incrementally maintained
relation index to reuse here. If either is introduced, it needs a separate
refinement argument showing that every lookup observes the same round snapshot.

## 4. Validation and Proof Obligations

- Differentially compare naive and semi-naive final relation facts and e-class
  partitions over generated finite programs.
- Include tuple insertion, tuple recanonicalization, class merges that preserve
  the stored representative, mark/restore, and fallback-only rule shapes.
- Assert per-key `delta subset full` and disjoint first-delta emissions.
- Specify whether duplicate derivations are observable; if actions are not
  idempotent, deduplicate at the semantic boundary rather than relying on
  storage hash-consing.
- Only claim fixpoint equivalence after proving that every enabling event is
  either represented by a delta scanning atom or routed through the full
  fallback.
