# Optimal Term Extraction

## Problem

Given an e-class (identified by its representative), reconstruct the
lowest-cost concrete term from the equivalence class. Each e-class
may contain many e-nodes, each representing a different way to build
a term of that sort. We want the cheapest one.

## Cost Model

Each operator has a base cost of 1. The cost of an e-node is:

    cost(node) = 1 + Σ best_cost(class(child))

where `best_cost(class)` is the minimum cost over all nodes in the
class. Literal nodes (constants) have cost 1 with no children.

This is the standard AST-size metric. A pluggable cost function can
be added later, but AST size is the right default.

## Algorithm

Bottom-up fixpoint iteration over all e-classes:

```
best_cost: HashMap<repr, usize>     // best cost per e-class
best_node: HashMap<repr, G>         // which node achieves it

loop:
    changed = false
    for each node id in 0..eg.len():
        repr = find(id)
        op_cost = 1
        child_cost = 0
        extractable = true
        for each child c of node:
            child_repr = find(c)
            if child_repr not in best_cost:
                extractable = false
                break
            child_cost += best_cost[child_repr]
        if not extractable: continue
        total = op_cost + child_cost
        if total < best_cost.get(repr, ∞):
            best_cost[repr] = total
            best_node[repr] = id
            changed = true
    if not changed: break
```

Convergence: each iteration can only decrease costs. Since costs are
bounded below by 1, the fixpoint is reached in at most `max_depth`
iterations where `max_depth` is the depth of the shallowest term in
the e-graph. In practice, 2-3 passes suffice.

## Term Reconstruction

After extraction, reconstruct the `Term` AST by following
`best_node` pointers:

```
fn reconstruct(repr) -> Term:
    node = best_node[repr]
    op_name = eg.node_op_name(node)
    if node is literal:
        return Term::Lit(display(lit_val))
    children = []
    for each child c of node:
        children.push(reconstruct(find(c)))
    return Term::App(op_name, children)
```

## Surface Syntax

```
(extract expr)
```

Builds `expr` in the e-graph (like `check`), finds its e-class
representative, runs extraction, prints the result.

## Implementation Plan

1. Add `extract` module with `extract_best` function
2. Add `Command::Extract(Term)` variant
3. Parse `(extract ...)` in parser
4. Handle in interpreter: build term, extract, print

## What We Don't Need

- ILP extraction (overkill for now)
- Per-operator cost weights (just use AST size)
- Extraction with sharing (DAG extraction) — tree is fine
