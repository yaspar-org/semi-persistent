# Partial Weighted Max-SAT Extraction

## Current state

`extract_best` computes the minimum owned-tree cost for the current additive
cost model by fixpoint iteration. It is the default extractor and is adequate
for uniform or per-operator tree costs. It cannot directly express shared-DAG
cost, edge-dependent cost, hard exclusions combined with richer objectives, or
lexicographic multi-objective selection.

## Gap

The e-graph is an AND/OR graph, but there is no general optimization encoding or
solver boundary for selecting an acyclic subgraph under those objectives.

## Encoding

Treat each e-class as an OR node and each e-node as an AND node.

- A selected e-class chooses one selected member for tree extraction, or the
  objective's specified member set for DAG extraction.
- Selecting an e-node requires selections for all child classes.
- Root classes are hard-selected.
- `:unextractable` nodes are hard-disabled.
- Soft clauses or pseudo-Boolean terms carry node and edge costs.

Shared-DAG extraction uses one decision variable per selected e-node, so a
shared subterm is charged once. This is a distinct output contract from
returning an owned `Term`; decoding must expose sharing rather than silently
deep-copy it.

## Acyclicity

Local AND/OR constraints alone admit selected cycles. Add one sound acyclicity
encoding:

- topological-order variables with every selected edge decreasing the order;
- a solver-supported acyclicity constraint; or
- iterative cycle cuts with a checked final DAG.

The decoder must reject a model that violates acyclicity even if the solver
backend claims validity.

## Solver Boundary

Define a trait over:

- weighted hard and soft constraint insertion;
- deterministic solve status;
- optimum cost retrieval;
- model lookup; and
- optional proof or optimum certificate retrieval.

Keep the current fixpoint extractor as the default. Solver-specific ids and
iteration order must not determine ties: decoding applies an explicit stable
tie-break over operator, node, and child ids.

## Validation

Use an independent brute-force enumerator on small e-graphs. Where the objective
is additive owned-tree cost, compare both selected cost and reconstructed
validity with `extract_best`. Add objectives the current extractor cannot
express:

- shared-DAG cost;
- edge-dependent cost;
- per-operator preferences;
- hard `:unextractable` exclusions; and
- lexicographic objectives.

## Acceptance criteria

- The encoder and decoder reject cyclic or incomplete models.
- Small-instance brute force agrees with the solver optimum for every supported
  objective.
- Additive tree-cost fixtures agree with `extract_best`, including ties and
  cyclic e-classes with grounded exits.
- At least one shared-subterm fixture demonstrates a different DAG optimum and
  returns an explicitly shared representation.
- Different solver backends decode the same result under ties.
- Encode, solve, and decode time are measured separately against graph size with
  Criterion confidence intervals.
