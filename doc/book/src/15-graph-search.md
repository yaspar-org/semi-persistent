# Graph search, and the hybrid

UCT searches the same action graph defined in Chapter 14, but it can return an
achieved result before the graph has been exhausted. A playout budget controls
how much of the graph it explores.

## When to use it

The surface default is `:algorithm uct` with 1,000 playouts and
`:cycles sides`. Select `exact` when an exhaustive result is required and its
search completes within the available resources. Select UCT when a fixed
playout budget is required. Neither algorithm is generally faster; their costs
depend on the action graph.

UCT always performs a deterministic initial rollout. A budget of
`:playouts 0` therefore returns that initial achieved result rather than no
result. Further playouts can improve it or exhaust the graph. The output reports
`:completion budget` in the first case and `:completion exact` in the second.

The following query reuses Chapter 14's cyclic construction. With 10,000
playouts and pair-cycle filtering, UCT exhausts this small graph and returns the
same size-eight term:

```lisp
{{#include ../examples/15-uct.egg:uct-query}}
```

```text
(anti-unify :size 8 :cr 0.8571 :completion exact
  (h a (h (Variants (f a) a) (f a))))
```

## One playout

A playout performs four operations:

1. Select from the root, using UCT at OR nodes and an effort selector at AND
   nodes.
2. Expand the first unhandled action reached.
3. Run a deterministic rollout to initialize newly reached states.
4. Walk back along that path, recomputing values and composing stored child
   terms into achieved candidates for their parents.

Composition during the final step is how later playouts improve on the initial
rollout. The full procedure is specified in
[`19-anti-unification.md`, section 3.3](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## The same subproblem, reached many ways

Several paths may reach the same contextual class-pair state. They share that
state's current value and achieved term. Selection counts remain local to the
parent-action edge, however, so traffic arriving through another parent does
not pretend that this parent selected the shared child.

Chapter 14 defines the cycle contexts that distinguish states. The shared-state
and local-edge bookkeeping is detailed in
[`19-anti-unification.md`, section 2.6](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## Values are recomputed, not accumulated

Ordinary tree-MCTS bookkeeping would mix unrelated traffic at a shared child.
A child visit count includes visits from parents that the current parent never
selected, and propagating every child update into every parent would count work
outside each parent's selected distribution.

Semper keeps `N(n,a)` on the edge from state `n` to action `a`, and recomputes
values from current child values:

```text
Q(n)   = (U(n) + sum N(n,a) * Q(a)) / (1 + sum N(n,a))
Q(a)   = 1 + sum count(i) * Q(child(i))
```

`U(n)` is the initial rollout estimate. AC and ACI actions replace the second
sum with the current minimum-cost transport. An off-path parent can temporarily
hold a stale value, changing what a finite budget explores, but a published
candidate is still composed from achieved child terms rather than estimates.

## Closure

A structural completion check asks whether every reachable action has been
handled and every realized child has completed. If so, a children-first pass
recomposes all shared parents before the root is reported exact.

The Rust API can additionally maintain closure incrementally. A completed
shared state notifies every parent through reverse edges, selection skips its
closed subgraph, and a closed root stops the run early. Closure means that no
unresolved action remains. It cannot be inferred merely because a size lower
bound equals the incumbent size: an equal-size action could still improve
variant mass. Chapter 14 gives the pruning rule; the closure argument is in
[`19-anti-unification.md`, section 9.5](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## The hybrid

Hybrid search hands an admitted UCT state to Exact. A completed call marks that
state exact and terminal, so subsequent selection need not enter its subgraph.
The call receives the same class pair, cycle context, and cycle mode as the UCT
state and therefore solves the same contextual problem.

Admission uses estimates of the reachable class-pair rectangle and entry-state
action count. These estimates are not complexity bounds on descendant
contextual states. A separate Rust configuration can impose a node-entry
budget on one delegated call. Hybrid correctness has finite differential
evidence and an implementation argument, not a machine-checked solver proof.

Hybrid selection is available only through the Rust API. The implementation and
argument are in
[`mcgs.rs`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/src/au/mcgs.rs).

## Configuration

The surface language exposes `:algorithm`, `:playouts`, and `:cycles`.
Chapter 14 defines the cycle options. Incremental closure, hybrid calls, their
admission settings, and the other search-policy controls are Rust-API
configuration. The complete configuration table is in
[`19-anti-unification.md`, section 7](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).
