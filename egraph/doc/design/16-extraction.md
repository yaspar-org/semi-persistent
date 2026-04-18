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
    let mut best: HashMap<G, (usize, G)> = HashMap::new();
    // best[class_repr] = (cost, best_node_id)

    loop {
        let mut changed = false;
        for each e-node id:
            let repr = find(id);
            let child_cost = sum of best[find(child)].cost for each child;
            let total = 1 + child_cost;
            if total < best[repr].cost:
                best[repr] = (total, id);
                changed = true;
        if !changed: break;
    }

    reconstruct(eg, best, root)
}
```

Iterates until fixpoint. Each iteration may improve costs as
cheaper representations are discovered through equivalences. The
`reconstruct` function then builds a printable term tree from the
`best` map:

```rust
fn reconstruct(eg, best, id) -> ExtractedTerm {
    let (_, node_id) = best[find(id)];
    let op_name = eg.node_op_name(node_id);
    let children = eg.children(node_id)
        .map(|child| reconstruct(eg, best, child));
    ExtractedTerm { op: op_name, children }
}
```

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
