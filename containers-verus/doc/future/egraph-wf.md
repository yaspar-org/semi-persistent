# E-graph well-formedness: remaining work

The class-layer aggregate (`src/eclasses.rs`) is verified: invariants W1
through W7 form its machine-checked `wf()`, every public mutator preserves
them, and the archive clauses extend them to every outstanding mark. The
authoritative invariant table, one line per clause, is the `eclasses.rs`
module header; the production-parity statement is
[`../design/12-egraph-class-layer-parity.md`](../design/12-egraph-class-layer-parity.md).
This document holds only what is not yet proved.

## D1: the dirty-set discipline

`EGraph::merge` breaks W5-freshness on purpose (use-list entries go stale at
a merge) and rebuild repairs it. The honest specification is
`wf_except(dirty)`: W1 through W4, W6 and W7 hold unconditionally; the nodes
whose freshness is suspended are exactly the dirty set. Proving it makes the
deferred-repair convention a checked object and gives rebuild its loop
invariant: each iteration shrinks the dirty set, and the unconditional `wf`
holds when the set is empty.

## R1: congruence at the rebuild fixpoint

When the dirty set is empty, the hash-cons maps each live node's canonical
form to its id, and no two live nodes share a canonical form. R1 is the
correctness theorem of `rebuild`, not a step invariant, and its statement
needs D1's dirty set. Postponed, not planned: congruence closure has
mechanizations in other provers but no Verus mechanization exists to
calibrate an effort estimate against. Revisit when D1 is in place.

The node-store side of R1 (hash-cons and canonical-form specification) is
scoped in [`node-store-plan.md`](node-store-plan.md).

## Order

D1 precedes R1, because R1 quantifies over the empty dirty set. Both build on
the shipped aggregate unchanged.
