# Container performance methodology

The e-graph consumes `containers-verus` directly. These benchmarks compare it
with the independent reference implementation; they do not represent a second
production path.

Run the reference suite with Criterion:

```bash
cargo bench -p containers-conformance --bench retained_containers_bench
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
- separate B+, nested-mark, tracked-vector, and aggregate `EClasses` benches.

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
