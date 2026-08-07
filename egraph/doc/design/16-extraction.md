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

Each operator has cost 1. The cost of a term is the sum of all
operator costs (i.e., the number of nodes in the term tree).
For AC nodes, child multiplicities are accounted for: a child with
multiplicity k contributes k × child_cost.

Literal values have cost 1. Variables are not extractable (they
represent unknowns in patterns, not concrete terms).

All nodes are treated uniformly; there is no constructor preference
or cost weighting. (`OpInfo::is_constructor` exists in the registry
but is not currently used by the extractor.)

## Algorithm: `extract_best`

Bottom-up BFS over e-classes:

```rust
pub fn extract_best(eg: &EGraph, root: G) -> Option<ExtractedTerm> {
    // Two dense arrays indexed by class id, not a map: ids are dense, so
    // `Vec` indexing replaces a hash per lookup. `UNSET` in `best_cost`
    // marks "this class has no best node yet".
    let mut best_cost: Vec<usize> = vec![UNSET; n];
    let mut best_node: Vec<G>     = vec![G::default(); n];

    loop {
        let mut changed = false;
        for each e-node id:
            let slot = find(id).to_usize();
            let child_cost = sum of best_cost[find(child)] for each child;
            let total = 1 + child_cost;
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

The dense-array representation is a measured choice over the map form this
document previously showed: 22-29% faster where the fixpoint dominates
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

## Limitations

The current extractor uses a simple iterative cost model. It does
not handle:
- Weighted costs (all ops cost 1)
- Constructor preference (planned but not yet implemented)
- DAG extraction (each subtree is extracted independently)
- Extraction with constraints (e.g., "extract a term of sort X")

These are all potential future extensions.

---
[← Ch 15: Proof Logging](15-proof-logging.md) · [Table of Contents](00-table-of-contents.md) · [Ch 17: Interpreter →](17-interpreter.md)
