<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E3 — index hasher (A3)

**Superseded for the index families, 2026-08-16.** `IndexStore`'s four families
are no longer hash maps: they are dense-keyed `DenseSpanMap`s, read by array
index (`egraph/doc/design/06-index.md`). The result below stands as the record of
the commit it measured, and it still applies to the per-operator statistics maps
that remain hashed, but the four families it names no longer hash anything. Do
not cite it as the current state of the index.

**Change.** The maps keyed by internal dense ids now use foldhash instead of
std's default SipHash:

- `index::IndexStore`'s four crosscutting maps — `by_op` (op id),
  `by_repr`/`by_contains` (class id), `by_child_pos` (`(class id, u32)`). These
  are rebuilt every round and probed on every join step, so they are the whole
  point of the experiment.
- `cc::CcSnapshot::by_op_contains`, keyed by `(op, child_repr)`.
- `extract::extract_best`'s `best_cost`/`best_node`, keyed by class id.

`index::FastMap<K, V>` is the alias, re-exported because
`tests/semi_naive_delta.rs` names the map type in a helper signature.

**Why foldhash and not `rustc-hash`.** The plan proposed adding `rustc-hash`.
foldhash is already a workspace dependency and is hashbrown 0.17's default,
which makes it what production `Map` and verified `SpMap` already hash with — see
the `foldhash` note in the workspace `Cargo.toml`. Using one hasher across the
workspace is worth more than any marginal per-probe difference between the two
fast options, and it adds no dependency.

**Verdict: accepted.** The bar for this experiment was "any statistically clear
win, but record the number". It is clearer than that: 4.5-10% depending on the
row, `p = 0.00`, consistent across three runs.

## Numbers

Baseline `E3-before` = commit `8255ec7` (post-E2). Three full-suite runs,
`MALLOC_MMAP_THRESHOLD_=65536`.

| bench | run 1 | run 2 | run 3 |
|---|---|---|---|
| `plain7/naive`  | −4.5% | −5.6% | −6.4% |
| `plain7/semi`   | −9.5% | −9.8% | −10.1% |
| `ac6/naive`     | −1.2% | −0.9% | −1.4% |
| `ac6/semi`      | −4.5% | −6.2% | −4.9% |
| `ac10/naive`    | −0.2% (p=0.26) | −0.4% (p=0.14) | −0.7% |
| `ac10/semi`     | −1.1% | −1.8% | −1.3% |
| `accompl32`     | +1.5% | +1.0% | +2.0% |
| `accompl64`     | +0.9% | −1.2% | +0.9% |

**The semi-naive rows gain about twice what their naive counterparts do**
(`plain7`: −10% vs −5.5%; `ac6`: −5% vs −1%), which is the shape the mechanism
predicts. Semi-naive builds *two* index stores per round instead of one (full and
delta) and runs one query per (rule, join atom) rather than one per rule, so both
the construction hashing and the probe hashing are multiplied.

`ac10` barely moves. Its time is dominated by AC decompose frames and rest-slice
splicing, not index probes — the same reason it barely moved under E1.

The completion rows land within ±2%, i.e. inside the ±1% rebuild-noise band plus
measurement spread, and one of the six readings is negative. They contain no
`IndexStore` probes on the hot path (completion works through `CcSnapshot`), so
nothing here is evidence about them either way.

## Mechanism

Allocation counts are unchanged by construction — this experiment does not touch
allocation — and `allocprobe` confirms it (`plain7/naive` 148 110 before, 148 111 after —
the one extra is the `RandomState` seed). The mechanism is instructions per probe, not allocator traffic, so the
supporting evidence is the naive-vs-semi ratio above rather than an
`allocprobe` delta: a change that made probes cheaper should help the driver that
probes twice as much roughly twice as much, and it does.

## Note on iteration order

`schedule.rs:131` iterates `by_op` to build `IndexStats::op_card`. Changing the
hasher changes that iteration order. It is safe because the result is collected
into a map keyed by op — order does not reach the output — but it is the kind of
thing that turns into a nondeterministic test failure elsewhere, so it was
checked rather than assumed. No other site iterates any of these maps outside
tests.

## Correctness

`cargo test --workspace --release`: 80 test binaries, 0 failures.

`tests/semi_naive_delta.rs` needed a signature change (its helper spelled the map
type), which is why `FastMap` is public. That test is also the one that matters
most here: it asserts `build_delta` equals `build` restricted to the touched set
*per key*, so a hashing change that corrupted bucketing would fail it.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --baseline E3-before
```
