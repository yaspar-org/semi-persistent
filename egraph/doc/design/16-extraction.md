# Chapter 16 — Term Extraction

[← Ch 15: Proof Logging](15-proof-logging.md) · [Table of Contents](00-table-of-contents.md) · [Ch 17: Interpreter →](17-interpreter.md)


## Problem

An e-class represents a potentially infinite set of equivalent terms.
Extraction answers the question: "give me the simplest concrete term
from this class." This is how the user gets results out of the
e-graph after saturation.

Given an e-class (a set of equivalent terms), find the smallest
(lowest-cost) concrete term that belongs to the class.

## Cost Model

Each operator has a per-node cost, declared as `:cost n` on its
declaration and defaulting to 1. The cost of a term is the sum of its
nodes' costs, so an undeclared program pays one per node. For AC
nodes, child multiplicities
are accounted for: a child with multiplicity k contributes k ×
child_cost.

Literal values have cost 1. Variables are not extractable (they
represent unknowns in patterns, not concrete terms).

An operator declared `:unextractable` is excluded from the candidate
set: the extractor never selects one of its nodes, though the node
stays in the e-graph and stays matchable. This is a filter, not a large
cost: a cost cannot express "never", and the two behave differently
when the alternative is expensive.

The costs and the exclusion are read from `OpInfo` (`cost`,
`unextractable`), hoisted into a per-op table before the fixpoint so the
inner loop indexes by op id rather than querying the registry per node.
`OpInfo::is_constructor` is registration metadata and stamps
`FLAG_CONSTRUCTOR` on the op's nodes; the extractor does not currently
prefer constructors over other operators.

### Subsumption is not unextractability

`(subsume …)` hides a node from *matching* only: the matcher's indices
skip `FLAG_SUBSUMED`, but the extractor does not, so a subsumed node is
still extractable and can still be the extracted winner. That is why
`:unextractable` is a separate mechanism rather than sugar for
subsumption. Pinned by `subsumed_node_is_still_extractable` in
`tests/extract_best.rs`. Whether extraction should skip subsumed nodes
is an open question, deliberately left as-is here.

## Algorithm: `extract_best`

Bottom-up BFS over e-classes:

```rust
pub fn extract_best(eg: &EGraph, root: G) -> Result<ExtractedTerm, ExtractError> {
    // Two dense arrays indexed by class id, not a map: ids are dense, so
    // `Vec` indexing replaces a hash per lookup. `UNSET` in `best_cost`
    // marks "this class has no best node yet".
    let mut best_cost: Vec<usize> = vec![UNSET; n];
    let mut best_node: Vec<G>     = vec![G::default(); n];

    loop {
        let mut changed = false;
        for each e-node id:
            let slot = find(id).to_usize();
            if op_meta[op_of(id)].unextractable: continue;
            let child_cost = sum of best_cost[find(child)] for each child;
            let total = op_meta[op_of(id)].cost + child_cost;
            if total < best_cost[slot]:
                best_cost[slot] = total;
                best_node[slot] = id;
                changed = true;
        if !changed: break;
    }

    reconstruct(eg, &best_node, find(root))
}
```

Iterates until fixpoint. Each iteration may improve costs as
cheaper representations are discovered through equivalences. In practice the
fixpoint converges in two passes on every workload measured, which is why the
worklist variant was not adopted (`doc/perf-results/E12-worklist-fixpoint.md`).

The dense-array representation is a measured choice over a map form: 22-29%
faster where the fixpoint dominates
(`doc/perf-results/E4-extract-dense-tables.md`).

`reconstruct` then builds a printable term tree from `best_node`:

```rust
fn reconstruct(eg, best_node, repr) -> ExtractedTerm {
    let node_id = best_node[repr.to_usize()];
    let op_name = eg.node_op_name(node_id);
    // A child of multiplicity k costs k copies, but only k-1 of them need to
    // be clones — the last one moves the original in. At the common k == 1
    // that is one deep copy saved per child, and it matters more than it
    // looks: cloning-then-dropping made extraction of a depth-d chain
    // O(d^2) node copies for a d-node result.
    let children = eg.children(node_id)
        .flat_map(|(child, k)| {
            let t = reconstruct(eg, best_node, find(child));
            repeat(t.clone()).take(k - 1).chain(once(t))
        });
    ExtractedTerm { op: op_name, children }
}
```

Removing that redundant clone is 91-98% on every extraction row
(`doc/perf-results/E11a-reconstruct-redundant-clone.md`).

For literal nodes, the extracted term includes the literal value.
For AC/ACI nodes, children are expanded from the pool.

## Failure

Extraction returns `ExtractError` rather than an empty option, so the
caller can say why:

- `AllUnextractable { class, ops }`: the class has nodes, but every one
  of them is an `:unextractable` op. Reachable, and named: the error
  carries the class and the offending op names.
- `NoGroundTerm { class }`: no node in the class has a fully costed
  child set. Defensive: `add` builds children before parents, so every
  class is grounded through the leaves it was built from.

## Limitations

The current extractor uses a simple iterative cost model. It does
not handle:
- Constructor preference (`is_constructor` is stamped but unread here)
- DAG extraction (each subtree is extracted independently)
- Extraction with constraints (e.g., "extract a term of sort X")

These are all potential future extensions.

---
[← Ch 15: Proof Logging](15-proof-logging.md) · [Table of Contents](00-table-of-contents.md) · [Ch 17: Interpreter →](17-interpreter.md)
