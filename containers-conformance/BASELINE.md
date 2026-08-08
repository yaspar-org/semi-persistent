# Performance baseline: verus vs production containers

The migration gate (plan validation matrix) is: **retained containers within
±10% of production, or a reviewed exception.** This file records the measured
ratios and how to reproduce them.

## How to run

```
cargo bench --bench perf_gate -p containers-conformance
```

Prints a table and exits non-zero if any row rises above **its own recorded
ceiling** (below). It is a plain `main` (`harness = false`), not a criterion
bench, and it runs on every PR as the `perf-gate` job in
`.github/workflows/ci.yml`.

## The baselines here are enforced, not documentary

Each gated row is pinned in code via `Row::gated(.., recorded)`, where `recorded`
is the least favourable delta in the table below; the ceiling is
`recorded + perf::NOISE_MARGIN` (6pp), capped by `perf::MIGRATION_GATE` (the
plan's absolute 10%).

## Enforced on the machine they were measured on

The recorded ceilings are a contract for the baseline machine below. The
prod/verus ratio is itself machine-dependent, not merely noisy: one GitHub
shared-runner run read `mark_set_restore` at +1.9% against a −12…−17% recorded
range and, in the same run, `class_merge_restore` at −28.6% against −7.9…−8.2%
recorded (0.3pp local spread) — ~14–20pp shifts in opposite directions. A
`NOISE_MARGIN` wide enough to cover that collapses every ceiling to the blanket
10% the per-row design exists to avoid.

So the gate has two modes:

- **default** — per-row recorded ceilings, for the baseline machine. This is
  the mode any re-record must be measured in.
- **absolute** (`PERF_GATE_ABSOLUTE=1`, set by the `perf-gate` CI job) — every
  gated row is held to the one-sided `MIGRATION_GATE` (+10%) only. This is the
  migration plan's own criterion, the strongest claim that transfers across
  machines. The recorded ceilings are still printed for comparison.

A failure in absolute mode is a real regression on any hardware; a failure in
default mode on a machine other than the one below is measuring the CPU, not
the code.

Per-row pinning is the point. Under the blanket `pct <= 10` gate this file
previously described, `mark_set_restore` — recorded at −12…−17% — could have
degraded all the way to +9% and still printed `ok`: a 26pp regression behind a
green gate. A row that is currently verus-*faster* now has to stay verus-faster.

**Changing a number here is changing a contract.** If a row legitimately moves,
re-record it in both this file and the `Row::gated` call, citing the measured
spread that justifies it. Widening `NOISE_MARGIN` to quiet a row that is drifting
one way across commits discards exactly the signal the gate exists to catch.

## Why not criterion for the ratio

Criterion's per-group `prod`-then-`verus` layout measures **position, not
implementation**. Whichever `bench_function` runs second inherits a
grown/fragmented glibc `brk` heap and reads ~+18%; swapping the two arms moves
the penalty to the other. Two rows were chased as regressions and were entirely
this artifact:

- `micro/push_only_untracked` read +40%. The push loop, `RawVec::grow_one`,
  `drop_in_place`, and the allocation counts are **byte-identical** between the
  two crates. Confound-free: **+0.2%**.
- `vec/mark_set_restore` read anywhere from −1.8% to +19.9% across runs (three
  hand-timed harnesses called it parity). Confound-free: **within ±3%**, both
  signs across runs.

Full bisection and the byte-level disassembly evidence:
`doc/design/11-layout-parity.md`. Confound-free single-call-site probes:
`examples/onesite.rs`, `examples/onesite_mark.rs`.

`perf_gate` removes the confound with `containers_conformance::perf::compare`
/ `compare_batched`: the two arms are interleaved per sample (neither is
systematically second) and reduced by min (the least-perturbed estimate).

## Baseline readings (AMD EPYC 9R14, release, N=100k)

Ratios are stable across runs; absolute µs drift with machine load and with how
often the fixture is rebuilt, the delta does not.

Observed range and spread are over **seven consecutive runs** on one otherwise
idle machine. `recorded` is the least favourable end of that range — the value
pinned in `perf_gate.rs` — and `ceiling` is what the build actually fails above.

| bench                 | observed range  | spread | recorded | ceiling | notes |
|-----------------------|-----------------|--------|----------|---------|-------|
| `mark_set_restore`    | −12.1% … −17.0% | 4.9pp  | −12.0%   | −6.0%   | tracked mark / 50k set / restore; verus faster. Noisiest row: the timed unit includes the 50k-set phase |
| `restore_replay`      | −1.1% … +1.4%   | 2.5pp  | +1.5%    | +7.5%   | restore phase ALONE; see "gate on phases" below |
| `class_splice`        | +3.9% … +4.7%   | 0.8pp  | +4.7%    | +10.0%  | ceiling is `MIGRATION_GATE`-capped (4.7+6 > 10). Residual is the extra payload write clearing the absorbed key's presence bit |
| `class_walk`          | −0.6% … +0.3%   | 0.9pp  | +0.5%    | +6.5%   | parity, as the disassembly argues |
| `class_merge_restore` | −7.9% … −8.2%   | 0.3pp  | −7.8%    | −1.8%   | tightest row; the e-graph's real rebuild/backtrack shape |
| `nested_mark/depth2`  | +2.6% … +8.1%   | 5.5pp  | ungated  | n/a     | 0.38 µs — below the layout-noise floor |
| `nested_mark/depth32` | +0.0% … +5.1%   | 5.1pp  | ungated  | n/a     | 2.6 µs — layout floor |

The three `class_*` rows gate the consumer swap in `egraph/src/classes.rs`;
their production arm is the hand-rolled ring the swap deleted, preserved verbatim
in `src/prod_class_ring.rs`. That is the only honest baseline — the implementation
the swap replaced, not some other container.

Note the two ungated `nested_mark` rows have a *wider* spread (5.1–5.5pp) than
several gated rows do, at 0.4–2.6 µs of timed work. That is the layout-noise
floor being visible in the data, and is why they are measured but not gated.

End-to-end in the consumer, `egraph/benches/vec_bench.rs mark/bitset` is
**9.8%–22.0% faster** than production across n = 1k … 1M.

### The gate is one-sided

Only verus being *slower* fails. A symmetric `abs()` gate failed the build at
−25% — for beating production — which is not a regression.

### Gate on phases, not cycles

`restore_replay` exists because a whole mark/set/restore cycle is **set-phase
dominated**, so a real restore regression hides inside a net-faster cycle: at one
point the cycle read −25% while `restore` alone was **+30%**. Cycle-level rows
cannot gate what they average out. `examples/phasesplit.rs` splits
mark / sets / restore; `examples/restoresplit.rs` scales restore by diff count
(a flat delta across a 50× range means per-diff cost, not per-word bitmap cost).

### Retracted: the `nested_mark` "layout artifact"

An earlier revision of this file explained `nested_mark`'s +7–11% as code-layout
alignment, on the strength of a dead-code experiment. That experiment was sound
but the conclusion was **wrong**: a real regression — `CaptureBits::set_true`
missing production's `#[inline(always)]` — was present at the same time. The
missed tell: the egraph's `mark/bitset` row was +12.8% **uniformly from n = 1k to
1M**, and layout deltas do not track n over three decades. Fixing the inline
returned `nested_mark` to +2.3% with no layout change, which disproves the
artifact reading. Full account and the two process lessons:
`containers-verus/doc/design/11-layout-parity.md`.

## Why `push_only_untracked` is not a gated row

A tight allocate-and-push loop is the one workload no in-process A/B harness can
time fairly: its per-iteration work is a few instructions, so the result is
dominated by whether the compiler inlines `Vec::push` into the timing closure
and where the loop lands modulo the cache line — and LLVM makes those choices
independently for the prod and verus closures (in the gate binary prod's `push`
out-lines while verus's inlines, a ~+22% artifact even with per-sample
interleave). The push loop, `RawVec::grow_one`, `drop_in_place`, and allocation
counts are **byte-identical** between the crates (`doc/design/11-layout-parity.md`),
so parity is established by that disassembly. The closest a timing gets is
`examples/onesite.rs` — both arms through one `run(which)` call site, identical
inlining — which reads **+0.1%**.

## Rows still to add

The remaining retained-container rows (`list/append_iter`, `list/splice`,
`vec/push_pop_untracked`, `tracked_vec` mark-churn) still live only in the
criterion benches. Port any whose criterion number is disputed into `perf_gate`
before treating it as real; the harness (`containers_conformance::perf`) is
built to make that a few lines each. Tracked as follow-up.
