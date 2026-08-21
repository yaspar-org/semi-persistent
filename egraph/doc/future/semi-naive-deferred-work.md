# Deferred Work — Semi-Naive Evaluation & Index Backend

[Ch 18: Semi-Naive Evaluation](../design/18-semi-naive-evaluation.md) · [Table of Contents](../design/00-table-of-contents.md)

Semi-naive evaluation is implemented and shipped (Chapter 18). This
document tracks the work that was **intentionally deferred**: each item
is optional relative to the intended implementation. The current
naive/semi-naive equivalence argument is scoped to eligible rule shapes plus
the explicit full-match fallbacks, and finite differential tests support it;
there is no universal machine-checked fixpoint-equivalence theorem. The items
below are performance and ergonomics follow-ups rather than known fixes for a
current counterexample.

---

## 1. Configurable index backend (B+tree-backed `IndexStore`)

**Status**: not started. The full index is always `SortedVec`,
bulk-rebuilt from scratch each round.

The `BPlusTreeSet` container and the `SortedCursor` trait already exist
(the latter is what semi-naive's `Difference` combinator and the
leapfrog join are generic over). What remains is to make `IndexStore`
generic over the sorted-set backend so the full index can be a
*semi-persistent* `BPlusTreeSet` that is maintained incrementally
across rounds, instead of rebuilt:

- Introduce a `SortedSetBackend` trait (`cursor()`, `len()`), implemented
  by both `SortedVec` and a `BPlusTreeSet` wrapper.
- Make `IndexStore<Cfg, B: SortedSetBackend>` generic, defaulting to
  `SortedVec` so nothing changes by default.
- Add incremental maintenance hooks (`on_node_added`,
  `on_node_recanonicalized`) for the B+tree backend, so the full index
  rolls forward with the e-graph rather than being rebuilt.

The motivating hypothesis is that late, small-delta rounds can favor a
maintained index over a full rebuild. A one-off ascending-arrival diagnostic
favored bulk rebuilding for both the verified B+tree and `std::BTreeSet`, but it
was not a maintained Criterion benchmark and supports no current ratio or
backend decision. Revive this item for a restore-heavy or
query/update-interleaved workload, and decide with a Criterion comparison that
retains bootstrap confidence intervals, host, and revision. The B+tree is
**currently unused by the engine**: shipped as a ready container, not wired
into `IndexStore`.

## 2. Layered incremental `DenseSpanMap` backend

**Status**: container implemented and verified; engine integration not started.

`containers-verus::LayeredSpanMap` keeps a dense base plus one replacement
delta and per-key invalidations. The e-graph does not currently instantiate it.
The current `IndexStore` bulk-builds a full `DenseSpanMap` and a separate delta
index for each semi-naive round.

Wiring the layered container is not mechanical. Recanonicalized old nodes can
move between buckets, so every source and destination bucket affected by a
merge must be invalidated and replaced in full to preserve sorted cursor
segments. The current layer installation is `O(d + i + k)`, where `d` is delta
values, `i` invalidated keys, and `k` the dense key-space size. Before enabling
it, either:

- adapt the delta to the occupied-key `SpanArena` build so installation is
  `O(d + i)`; or
- show with Criterion that the `k` term is immaterial on the target workload.

Add the backend behind an experimental configuration. Differentially compare
every bucket, full/delta/full-minus-delta query result, and final equality
partition with the bulk-rebuilt index across additions, recanonicalization,
class merges, marks, and restores. Measure installation, flattening, lookup,
retained memory, and end-to-end saturation. Keep bulk rebuild as the default
unless a restore-heavy or query/update-interleaved workload shows a supported
benefit.

Acceptance:

- no stale source or destination bucket survives recanonicalization or restore;
- each two-slice lookup is globally sorted under its documented separation
  condition;
- flattening is bucket-for-bucket equal to a fresh bulk rebuild;
- counters show whether installation scales with `d + i` or still with `k`;
  and
- a default change is backed by Criterion confidence intervals on a maintained
  consumer workload.

## 3. Delta-size fallback

**Status**: not started; deliberately omitted. There is currently **no
automatic fallback**: the selected strategy runs as-is.

If one round's merge cascade recanonicalizes a large fraction of the
e-graph, `|delta|` approaches `|full|` and the semi-naive savings
vanish (the k-variant fan-out becomes pure overhead). A guard would run
that round naively when `|delta| > α · |full|` for some `α ∈ (0, 1)`.
The threshold `α` and whether the decision is per-round or per-rule are
to be determined empirically (item 5).

## 4. Trigger pre-filter

**Status**: not started.

A `root_ops: HashSet<O>` per `PreparedRule` (the set of ops its join
atoms can scan) would let a round skip a rule's entire variant loop
when the delta contains no node with any of those ops. This is a cheap
membership check that avoids scheduling and running k empty variants
for rules that cannot possibly fire on this round's delta. Most
valuable when the delta is sparse and the ruleset is large.

## 5. End-to-end performance harness

**Status**: delivered; kept here only because items 1 and 2 cite it.
Wall-clock measurement exists at two levels: Criterion measurements over
`egraph/benches/saturate_bench.rs` and the campaign harness timing naive
against semi-naive end to end across the
`.egg` corpus (`scripts/egglog-compare/compare.py`, records in `doc/benchmarks/records/campaigns/`).
The backend-selection sweep for item 1 ran and closed as E5
(`BPlusTreeSet` is not instantiated outside benches; the sweep splits on
node size). Match-work instrumentation (`SatResult.match_steps` /
`--count-match-steps`) records fewer partial-match extensions on the retained
workloads where that result was observed. It is not a universal inequality:
variant scheduling and fallback rules can add work on other programs.

---

## Out of scope (decided against)

- **Strict structural-isomorphism differential oracle.** Rejected: node
  count and per-class node multiset are order-dependent, so the valid
  invariant is the equivalence *partition*, not structural identity.
  See Chapter 18, "Testing Strategy".

---
[Ch 18: Semi-Naive Evaluation](../design/18-semi-naive-evaluation.md) · [Table of Contents](../design/00-table-of-contents.md)
