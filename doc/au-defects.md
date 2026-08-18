# AU defects: minimal triggers and proposed fixes

Companion to `au-review.md`: the detailed account of the three defects
the 2026-08-14 review found in `egraph/src/au/`, all three fixed in the
tree (the resolution banner in `au-review.md` names the fix and the
regression test per defect; line references below are to the reviewed
snapshot). Each account gives the smallest
input known to trigger it, the mechanism traced through the code, the
candidate fixes with their trade-offs, and the regression test to land
with the fix. The review's differential fuzzer (2400 randomized cases,
exact vs MCGS plus projection re-evaluation) found no case where either
solver returned a wrong answer; all three defects are availability or
search-coverage defects, not wrong-result defects.

## D1. MCGS hangs: `solve_transport_f64` never terminates

**Severity.** P0. A library call (`anti_unify` with `AuAlgorithm::Uct`)
does not return; the process spins at 100% CPU. Hit rate 2 of 2400
random cases; deterministic once the graph shape occurs.

**Minimal input.** An ordinary acyclic e-graph; no merges, no cycle
mode. Leaves `k0..k3`; ops `u/1`, `f/2`; mset op `plus` with unit
`k0`; set op `and` with unit `k1`. Nodes:

```text
n4 = u(k2)
n5 = f(n4, k0)
n6 = and{n5, k3}
n7 = plus{n6, n6}
n8 = plus{n7, k3}
```

Query: `anti_unify(n4, n8)` under UCT with 3000 playouts. Expected:
returns in milliseconds (the exact solver answers the same pair in
under a millisecond). Actual: never returns. Two independent `sample`
captures place every sample inside the SPFA relaxation loop at
`egraph/src/au/transport.rs:217-268`, reached from
`recompute_transport_and_value` (`mcgs.rs:1588`), which runs one f64
transport solve per transport-AND node per backpropagation step.

**Mechanism.** The solver is successive shortest paths with SPFA as
the shortest-path routine. Its termination argument needs the residual
graph to stay free of negative cycles, which holds under exact
arithmetic because every augmentation follows a true shortest path.
The arc costs here are f64 Q values produced by `recompute_or_value`'s
divisions, and two mathematically-equal path sums can differ by one
ulp. Once an augmentation follows a path that is shorter only by such
noise, the residual graph acquires a cycle whose true cost is zero but
whose computed cost is approximately -1 ulp. SPFA's strict-less
relaxation then decreases `dist` around that cycle forever. The outer
loop's `total_supply` bound never engages because the inner SPFA call
never returns. The integer transport solver (`transport.rs:340`,
exact `i128` arithmetic) has the invariant unconditionally and cannot
loop.

**Candidate fixes.**

1. **Fixed-point costs, reuse the exact solver.** Scale the Q values
   to integers (a fixed denominator, e.g. 2^20) and route the
   transport-AND solve through the existing exact `i128` solver. The
   f64 network code is deleted; the termination argument becomes the
   integer solver's, which already holds. Cost: Q values quantize,
   which perturbs playout scoring below the noise floor of the search
   itself (Q is a selection heuristic, and nothing downstream consumes
   its low bits). This removes the defect class rather than patching
   the instance.
2. **Node potentials with reduced costs.** Maintain per-node
   potentials so arc costs stay non-negative and replace SPFA with
   Dijkstra. Negative residual arcs disappear structurally; ulp noise
   surfaces as tiny negative reduced costs that a clamp to zero
   absorbs. This is the textbook repair and keeps f64, but it is the
   larger diff (potential maintenance on every augmentation) and the
   clamp needs its own argument that clamping cannot starve a
   deficient node.
3. **Relaxation budget only.** Bound total relaxations per solve at
   the Bellman-Ford count and return the best flow found on breach.
   Smallest diff, converts the hang into a bounded-error result, but
   it keeps the broken invariant and turns a correctness property into
   a tuning constant.

**Recommendation.** Fix 1. The exact machinery exists, the heuristic
consumer tolerates quantization, and one of two solver code paths is
deleted instead of patched. Land fix 3's budget as a debug assert in
the same commit so any future negative-cycle regression fails loudly
in tests instead of hanging.

**DECIDED 2026-08-14: fix 1.** Ecosystem precedent supports it: the
major exact min-cost-flow implementations refuse float costs at the
API (OR-Tools SimpleMinCostFlow is int64-only; LEMON's cost-scaling
needs integrality for its epsilon-termination argument; NetworkX
documents that float weights void its guarantees). The alternatives
stay recorded with their revisit conditions:

- *Potentials with Dijkstra (fix 2).* Scipy's assignment solver runs
  this architecture on f64 safely because assignment structure
  precludes cycling; general transport cells lack that shield and the
  clamp needs a starvation argument. Revisit if the quantization is
  MEASURED to distort MCGS selection (a playout-decision differential
  against an exact-rational oracle would show it), or if Q values
  ever leave their bounded range so a fixed grid loses relative
  precision.
- *Interval costs with outward rounding.* Sound enclosures require
  propagating intervals through the whole Q pipeline (wrapping point
  values at the solver door is unsound), and on contested comparisons
  the algorithm still chooses arbitrarily, so decisions do not
  improve. Revisit only if a consumer wants certified per-decision
  optimality gaps.
- *Entropic regularization (Sinkhorn).* Unconditionally FP-robust
  fixed-point iteration; changes semantics (approximate, temperature
  parameter). Revisit if the transport solve remains the dominant
  profile cost after the buffer-reuse and dirty-flag work
  (au-review.md performance items 2-3) and the consumer is confirmed
  heuristic-only.
- *Relaxation budget alone (fix 3).* No optimality guarantee on
  breach; lands as the debug assert only, never as the fix.

**Regression test.** The five-node graph above as an in-tree test
running `anti_unify(n4, n8)` under UCT with a wall-clock bound (the
release-codegen timing-canary pattern from
`containers-conformance/tests/bplus_search_parity.rs` applies), plus a
property run asserting solve termination over the fuzzer's graph
distribution at reduced case count.

## D2. Exact solver panics: AC identity class containing an AC member

**Severity.** P0. `unreachable!("cycle-mode rank invariant violated")`
at `egraph/src/au/exact.rs:185`; process abort. Hit rate 13 of 2400
random cases; deterministic from the minimal input.

**Minimal input.**

```text
declare mset op plus with unit e
a, b, c leaves
merge(e, plus{a, b})      // the theory derives a + b = 0
rebuild()
exact AU(c, e)            // AU(a, e) also triggers
```

Expected: a generalization or an error value. Actual: panic.

**Mechanism.** Identity padding (`ac_repr.rs:126-157`, `pad_pair` and
`add_identity`) equalizes multiset widths by injecting the identity
CLASS as a transport-cell child. That class is not a structural child
of any member node, so `derive_child_context`
(`space.rs:398-418`) never sees it pass the
`is_reachable_from_child` filter, and the ancestor classes are not
accumulated into the cycle context. The OR-node memo key is
`(l, r, ctxL, ctxR)`; with contexts unchanged, `AU(c, e)` pads
`{c}` to `{c, e}` against `e`'s member `{a, b}` and spawns an
`AU(_, e)`-shaped cell with the SAME key beneath itself while the
parent is still `Visiting`. The rank argument (design section 3.2)
assumes every recursion step either shrinks the pair or grows the
context; padded identities do neither, and the `Visiting` re-entry
check correctly reports the broken invariant by panicking. MCGS
tolerates the same graphs because its playout loop has no memo-key
rank requirement (verified: all 64 pairs of a triggering graph
complete under MCGS).

**Candidate fixes.**

1. **Make padded identities context-relevant.** When `pad_pair`
   injects identity class `e` into a cell, add `e` (equivalently, the
   padding ancestor pair) to the derived child contexts for every
   recursive cell the padding creates. The memo key then differs
   between the parent and the padded child, the rank argument's
   "context grows" disjunct holds again, and recursion terminates
   because contexts are bounded by the class count. Cost: more
   distinct contexts, hence a larger memo table, only on
   identity-degenerate inputs (the class of graphs that panic today).
   Preserves exact-solver completeness.
2. **Cycle-block identity pairing.** In cycle mode, refuse the padding
   action when the identity class itself has members of the padded
   operator (the degenerate `unit = op{...}` shape). Small diff, but
   it excludes candidates: on inputs where the minimal generalization
   routes through the identity's members, the exact solver returns a
   larger answer than the true optimum, silently.
3. **Downgrade the `Visiting` re-entry to "no candidate".** Smallest
   diff, but the in-code comment is right that it needs a minimality
   argument: an OR node marked exact from a frontier missing the
   re-entrant candidate may be nonminimal, and callers treat exact as
   optimal. Without that argument this trades a loud panic for a
   silent quality regression.

**Recommendation.** Fix 1. It repairs the invariant the termination
proof actually uses instead of carving the degenerate inputs out of
the search space, and its cost lands only on inputs that cannot
complete at all today. Fix 2 is acceptable as an interim guard if fix
1's context plumbing takes longer than a day, with the exclusion
documented.

**Regression test.** The four-line minimal input asserting a
non-panic result; the same shape with `AU(a, e)`; and a rerun of the
review's 13 panic cases distilled to their unit-plus-merge skeletons.

## D3. Cross-operator action loss in `dedup_and_insert`

**Severity.** P1. No panic and no wrong score, but the action space is
silently truncated: generalizations using the dropped operator are
unreachable for both solvers.

**Minimal input.**

```text
a, b leaves; f/1, g/1
merge(f(a), g(a))
merge(f(b), g(b))
rebuild()
generate_actions(class(f(a)), class(f(b)))
```

Expected: two actions, one for `f` and one for `g` (both operators
witness the same child pairing). Actual: one action; whichever
operator is enumerated second is dropped.

**Mechanism.** `dedup_and_insert` (`actions.rs:455-464`) keys the
duplicate check on the `(left, right, count)` child-pair signature
alone; `action.op` is not part of the key. The doc comment scopes the
dedup to duplicates of the SAME action arising from different
`(l_node, r_node)` witnesses; dropping a different operator with the
same pairing is outside that intent. Quality happens to be unaffected
(two actions with identical signatures produce identically-scored
results), which is why the fuzzer's score comparison never flagged
it; the loss is the edge itself and the operator on the reported
generalization.

**Fix.** Include `action.op` in the dedup signature. One line plus
the test; no trade-off identified: same-op duplicates still collapse,
cross-op actions survive.

**Regression test.** The two-merge input asserting
`generate_actions` returns two actions with distinct operators, and
that both solvers can return a generalization headed by either
operator when the seed forces each.

## Order of work (executed)

All three shipped in the order proposed here: D3 first, D1 with the
budget assert in the same commit, D2 behind its context-plumbing
design, each with its regression tests.
