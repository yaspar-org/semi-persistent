<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E5 — `Branchless` as the B+tree search default (B1) — **closed, premise does not hold**

**The default is not on any hot path, because `BPlusTreeSet` is not instantiated
outside benchmarks and tests.** Flipping `S = BinarySearch` to `S = Branchless`
would change no shipped code path in this workspace. The sweep numbers are below
anyway, since they were the point of the experiment and they answer the question
for whoever does instantiate it.

## The premise, checked

B1 proposed flipping `bplus.rs:405`'s `S = BinarySearch` default, on the reading
that `Branchless` is implemented, swept by the bench, and never used. The second
half is right; the conclusion is not. Every instantiation of `BPlusTreeSet` in
the workspace:

| site | kind |
|---|---|
| `egraph/benches/seek_microbench.rs:28` | bench |
| `egraph/benches/leapfrog_bench.rs:25` | bench |
| `egraph/benches/split_bench.rs` (4 sites) | bench |
| `containers/benches/bplus_bench.rs` | bench |
| `containers/src/bplus.rs:952` | test macro |
| `containers-verus/canary/src/lib.rs:386,402` | verified-vs-production canary |

Nothing in `egraph/src`, `abstract-domains/src` or `traversals/src` constructs
one. What the e-graph's join path actually reads is `index::SortedVec` — a plain
sorted `Vec` with `partition_point`, which is B2's target, not B1's. The
`leapfrog_bench` comparison against `BPlusTreeSet` is a *comparison*: it exists to
show what the tree would cost if the index used one.

So B1 is not a change with a measurable effect to retain; it is a change to a
default that only benchmarks observe. Recording the sweep and closing.

## Sweep numbers

`containers/benches/bplus_bench.rs`, run as-is. The suite registers `Branchless`
for two of the eight layout/width combinations (`bplus64_u32`, `bplus512_u64`).

| workload | layout | `bin` | `br` | br vs bin |
|---|---|---|---|---|
| `build_from_sorted_1m` | 64 / u32  |  8.505 ms |  8.508 ms | +0.0% |
| `insert_random_1m`     | 64 / u32  | 177.7 ms  | 172.1 ms  | **−3.2%** |
| `seek_monotonic_10k`   | 64 / u32  | 951.9 µs  | 887.0 µs  | **−6.8%** |
| `build_from_sorted_1m` | 512 / u64 | 16.33 ms  | 16.26 ms  | −0.4% |
| `insert_random_1m`     | 512 / u64 | 182.7 ms  | 157.7 ms  | **−13.7%** |
| `seek_monotonic_10k`   | 512 / u64 | 694.1 µs  | 724.4 µs  | **+4.4%** |

**Read these as indicative, not as a decision.** They are A/B arms inside one
criterion process, which protocol item 2 forbids relying on: the second arm reads
systematically slow for being second, and E4b showed AC-row artifacts of ±4% from
nothing but a rebuild. Confirming them would need `--save-baseline` across two
runs with the default flipped, which is only worth doing for a real instantiation.

Taken at face value they do reproduce B1's caveat exactly, and in the direction
the caveat predicted: `Branchless` wins on random probes (`insert_random`, −3% to
−14%) and **splits on seeks** — −6.8% at 64-byte nodes, +4.4% at 512-byte nodes.
The crossover is node size, which is the mechanism: a 64-byte node holds ≤ 14
`u32` keys, few enough that a counting loop beats a branch chain, while a
512-byte node holds ≤ 62 `u64` keys, enough that binary search's ~6 branches beat
62 unconditional adds even when every branch mispredicts.

That is a per-instantiation answer, not a default. `BinarySearch` remains the
right default for the widest layouts, which is what a default should suit.

## If this comes back

A consumer instantiating `BPlusTreeSet` on a seek-heavy path with small nodes
should measure `Branchless` for its own layout. The sweep is already in place —
add the combination to `bench_all` in `containers/benches/bplus_bench.rs` and run
the two variants across separate criterion runs, not as two arms.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd containers
cargo bench --bench bplus_bench
```
