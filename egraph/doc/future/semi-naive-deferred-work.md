# Deferred Work — Semi-Naive Evaluation & Index Backend

[Ch 18: Semi-Naive Evaluation](../design/18-semi-naive-evaluation.md) · [Table of Contents](../design/00-table-of-contents.md)

Semi-naive evaluation is implemented and shipped (Chapter 18). This
document tracks the work that was **intentionally deferred**: each item
is optional and orthogonal to the correctness of what landed. None is
required for semi-naive to be sound or to reach the same fixpoint as
naive; they are performance and ergonomics follow-ups.

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

The motivating hypothesis (late in saturation, deltas are small, so a
maintained index beats a full rebuild) is measured and answered no on
the current workloads: `containers-conformance/benches/incremental_vs_rebuild.rs`
(20M ids, 10 rounds; recorded in `doc/migration/README.md`) has rebuild
winning 6-11x on the e-graph's ascending-arrival pattern, identically for
`std::BTreeSet`, so the gap is strategy-level, not implementation
quality. The item stays postponed with that record's revive condition: a
workload measured to be restore-heavy. The B+tree is **currently unused
by the engine**: shipped as a ready container, not wired into
`IndexStore`.

## 2. Delta-size fallback

**Status**: not started; deliberately omitted. There is currently **no
automatic fallback**: the selected strategy runs as-is.

If one round's merge cascade recanonicalizes a large fraction of the
e-graph, `|delta|` approaches `|full|` and the semi-naive savings
vanish (the k-variant fan-out becomes pure overhead). A guard would run
that round naively when `|delta| > α · |full|` for some `α ∈ (0, 1)`.
The threshold `α` and whether the decision is per-round or per-rule are
to be determined empirically (item 4).

## 3. Trigger pre-filter

**Status**: not started.

A `root_ops: HashSet<O>` per `PreparedRule` (the set of ops its join
atoms can scan) would let a round skip a rule's entire variant loop
when the delta contains no node with any of those ops. This is a cheap
membership check that avoids scheduling and running k empty variants
for rules that cannot possibly fire on this round's delta. Most
valuable when the delta is sparse and the ruleset is large.

## 4. End-to-end performance harness

**Status**: delivered; kept here only because items 1 and 2 cite it.
Wall-clock measurement exists at two levels: the E-series experiments
over `egraph/benches/saturate_bench.rs` (`doc/perf-results/`) and the
campaign harness timing naive against semi-naive end to end across the
`.egg` corpus (`comparison/run-full.py`, records in `comparison/final/`).
The backend-selection sweep for item 1 ran and closed as E5
(`BPlusTreeSet` is not instantiated outside benches; the sweep splits on
node size). Match-work instrumentation (`SatResult.match_steps` /
`--count-match-steps`) confirms semi-naive explores strictly fewer
partial-match extensions than naive.

---

## Out of scope (decided against)

- **Strict structural-isomorphism differential oracle.** Rejected: node
  count and per-class node multiset are order-dependent, so the valid
  invariant is the equivalence *partition*, not structural identity.
  See Chapter 18, "Testing Strategy".

---
[Ch 18: Semi-Naive Evaluation](../design/18-semi-naive-evaluation.md) · [Table of Contents](../design/00-table-of-contents.md)
