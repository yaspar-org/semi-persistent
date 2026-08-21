# Lattice-Valued Functions

## Current state

E-graph operators are term constructors. A functional-dependency collision is
resolved by e-class union, and semi-naive deltas are driven by node creation,
recanonization, and class growth.

The workspace also contains verified abstract domains and a verified
semi-persistent class layer. Neither is currently connected to a
lattice-valued function surface.

## Gap

Programs that require egglog-style relations with a merge operator cannot be
translated faithfully. A lattice update can change a rule result without
creating an e-node or merging an e-class, so treating it as an ordinary
constructor write would also make semi-naive evaluation incomplete.

## Semantics

Add declarations of the form:

```text
(function f (Args...) Ret :merge Domain)
```

`Domain` names a declared lattice. A collision at one argument tuple stores the
join of the old and incoming values. Arbitrary user expressions are not merge
operators; restricting the operation to a verified domain join makes
associativity, commutativity, idempotence, and monotonicity available to the
engine.

A lattice function is a table, not an e-class constructor:

- keys are canonical argument tuples;
- values belong to one declared domain;
- writes are inflationary joins;
- restore recovers the value at the selected frame; and
- a strict value increase is a semi-naive delta event.

## Verified storage

Extend `EClasses` or add a sibling verified table with a well-formedness clause
analogous to W7:

```text
stored[key] == join(history[key])
```

The clause must hold for the current frame and every archived frame. The proof
must cover insertion, collision join, mark, restore, and branch cutting. One
domain wired end to end is sufficient to establish the integration shape;
additional domains reuse the same table contract.

## Engine integration

1. Resolve each `:merge` declaration to a verified domain descriptor.
2. Compile reads to indexed table lookups and writes to join operations.
3. Record a touched key when a join strictly increases its value, even when no
   node or class changes.
4. Include those keys in the next semi-naive delta.
5. Give proof logging an explicit lattice-join step; a join is not a union.
6. Desugar `run-schedule` forms such as `seq`, `saturate`, and `repeat` onto the
   existing run loop without weakening stratum or restore boundaries.

## Acceptance criteria

- One verified domain runs through declaration, write, join, query, mark, and
  restore with no new `admit`, `assume`, or trusted contract.
- A regression proves that a join-only update reaches the next semi-naive
  round.
- Naive and semi-naive evaluation reach the same lattice table on generated
  finite traces.
- Proof-enabled execution distinguishes lattice joins from e-class unions.
- The translated lattice benchmark set passes, including the shared Luminal
  header programs and the stripped interval-analysis workload.
- Criterion measurements report table-write, delta, and end-to-end costs with
  confidence intervals.
