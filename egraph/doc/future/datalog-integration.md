# Datalog Integration

## 1. Relations as Unit-Typed Functions

The formal encoding: a relation `R(t1, ..., tk)` is a function `R: (S1, ..., Sk) -> Unit`. The unit sort has a single e-class `UNIT_CLASS`, a sentinel outside the union-find that never participates in any merge. Asserting `R(a, b)` inserts the e-node `R(canon(a), canon(b))` into the appropriate mode-specific hashcons pointing to `UNIT_CLASS`. Querying `R(a, b)` is a hashcons lookup after canonicalizing the arguments.

This encoding is zero-overhead: no additional machinery is needed. Relations over sort-typed arguments automatically benefit from the union-find's canonical representation — a query for `R(a, b)` where `a` and `c` have been unified will find entries for both under `R(canon(a), b)`.

Plain relations use `hashcons_plain`. Commutative relations use `hashcons_c`. Set-valued relations use `hashcons_aci`. The mode-specific hashcons choice is part of the relation declaration.

## 2. Semi-Naïve Evaluation

Semi-naïve evaluation avoids re-deriving facts already computed in previous iterations. For each rule with body atoms `A1, ..., Am`, The engine generates `m` delta rules, each using the current generation's diff for exactly one atom:

```
ΔRule_j: A1(full), ..., Aj-1(full), ΔAj(new only), Aj+1(full), ..., Am(full) → head
```

The diff for atom `Aj` is the set of e-nodes added to `Aj`'s backing hashcons since the previous generation boundary — read directly from the `semi_persistent::containers::Vec` length difference, no bookkeeping required.

Correctness: the union of all delta rule results equals the set of new facts derivable in this iteration that were not derivable in the previous iteration. This is Theorem 4.1 of the egglog paper, and the proof carries over directly since the engine's generational diff is exactly the ΔDB in the semi-naïve algorithm.

## 3. The Fixpoint Loop

One saturation iteration proceeds through six phases. The match and
action phases produce pending mutations. The rebuild phase drains
them, which is where congruence closure happens and where index
updates are piggy-backed. The delta and termination phases determine
whether the loop continues.

1. Match phase: apply all rules (rewrite and Datalog) using
   semi-naïve evaluation against the current generation's diff and
   full database.
2. Action phase: execute all pending actions (unions, inserts,
   lattice updates).
3. Rebuild phase: process the pending-merges queue to fixpoint. For
   each merge, drain `by_child(absorbed)` into `by_child(survivor)`,
   canonicalize dirty parents in children vecs, decrement Len for
   ACI/AC deduplication, re-key hashmap entries, and detect
   collisions and enqueue further merges.
4. Index phase: if the arena compaction threshold is reached, rewrite
   the arena in in-order layout. Otherwise indexes are already up to
   date from step 3.
5. Delta phase: compute the new generation diff.
6. Termination check: if the diff is empty (no new facts, no new
   unions), the fixpoint is reached.

The phases cannot be reordered. Rebuild must see all pending merges
before indexes stabilize, and the delta can only be computed after
rebuild produces a congruence-closed state. Repeat until fixpoint or
the iteration budget is exhausted.

