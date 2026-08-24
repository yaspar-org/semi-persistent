# Container conformance and performance baseline

The e-graph consumes `containers-verus` directly. These benchmarks compare it
with the independent reference implementation; they do not represent a second
production path.

## Semantic conformance

`tests/egraph_reference_differential.rs` compares the former production
`containers::{union_find,eclasses}` algorithms with the verified class kernel
over finite randomized traces using 31-bit IDs. The shared contract covers
allocation, ordinary and directed merges, representatives, proof paths and
labels, class rings, use lists, atomic flags, completion-minimum contents, and
nested restore. Separate layout tests instantiate the retained ring cell at
both 31- and 63-bit ID widths.

The comparison has these explicit boundaries:

- the retained proof payload is generic instead of carrying the engine's rule
  enum, and directed rank increments saturate like the current verified kernel;
- the retained minimum pool stores flat cell offsets as `usize`, while the
  verified pool stores row IDs in the node index word, so tests compare row
  presence and contents rather than numeric row handles;
- cached class size and invariant W7 were added to the verified aggregate after
  the retained production revision, so no legacy-parity claim is made for that
  field; and
- capacity refusal and token validation are stronger in the verified total
  APIs. Differential traces remain within both implementations' valid domain.

These tests are regression evidence over sampled executions, not a proof that
the implementations are universally equivalent.

`src/prod_class_ring.rs` is a separate, deliberately minimal ring model used
only by the ring-cell layout test, exact retained-history accounting trace, and
the `class_ring/*` microbenchmarks. It isolates the two-cell splice protocol
from union-find, sparse-set, and use-list costs. It is not a second aggregate
oracle: aggregate semantic comparisons use the retained
`containers::eclasses::EClasses` above, and aggregate performance comparisons
use `benches/eclasses_bench.rs`.

## Performance methodology

Run the reference suite with Criterion:

```bash
cargo bench -p containers-conformance --bench retained_containers_bench
cargo bench -p containers-conformance --bench eclasses_bench
```

Criterion supplies warm-up, adaptive iteration counts, outlier analysis, and
bootstrap confidence intervals. Results are bound to the measured source
snapshot and host. They are not used as fixed-ratio CI gates because the ratio
between two in-process implementations can shift with code layout, allocator
state, and machine load.

The retained suite includes:

- `vec/try_extend`, `vec/mark_set_restore`, `vec/restore_replay`, and
  `vec/push_pop_untracked`;
- untracked `list/append_iter` and `list/splice`;
- `class_ring/splice_untracked`, `class_ring/walk`, and
  `class_ring/merge_restore`;
- map/intern, sparse-set churn, and append-only-log workloads; and
- separate B+, nested-mark, and tracked-vector benches.

`eclasses_bench` compares the complete retained and verified `EClasses`
aggregates for merge cascades, canonical find sweeps, and tracked
mark/merge/restore cycles. It is the class-layer performance evidence; the
`class_ring/*` rows above remain intentionally narrower microbenchmarks.

Read every retained-vs-verified row as implementation-vs-implementation, not as
a measurement of verification overhead. The two sides differ in ways unrelated
to proof: the verified `DiffStore` has a `raw_len() -> usize` accessor, so its
`Vec::set` bounds check does not round-trip through a checked narrowing to the
index type, while the retained `set` calls `len()` and pays that conversion on
every write; and the retained `Map` uses `hashbrown` with a randomly seeded
builder where the verified `SpMap` uses a fixed-seed `IndexHasher` over a
different table. Those are optimizations the reference never received. The
claim these benches support is that adopting the verified aggregate costs
nothing measurable — not that verification is free, and not that it is a win.

`restore_replay` excludes capture setup from the timed body.
`class_ring/splice_untracked` excludes ring construction,
`class_ring/walk` excludes construction and merging, and
`class_ring/merge_restore` measures the complete tracked mutation/rollback
phase. These rows preserve phase separation from the retired custom gate
without retaining its fixed ceilings.

Use `iter_batched`/`iter_batched_ref` and `BatchSize::LargeInput` for expensive
fixtures. Run registration orders separately when allocator history may affect
an arm, and retain the Criterion report, host, toolchain, and revision. A
complete cycle must not replace an isolated phase when the complete cycle can
hide a local regression.
