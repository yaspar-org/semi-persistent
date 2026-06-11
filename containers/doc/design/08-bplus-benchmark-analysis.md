# Chapter 8 — B+ Tree Parameterization: Benchmark Analysis

[← Ch 7: BPlusTreeSet](07-bplus-tree.md) · [Table of Contents](00-table-of-contents.md)

Microbenchmark sweep across the two compile-time parameters added to
`BPlusTreeSet`:

- **`NodeLayout`** — `Layout64`, `Layout128`, `Layout256` (node size in bytes).
- **`SearchKind`** — `BinarySearch` (`slice::partition_point`) vs
  `Branchless` (linear sum of `(k < target) as usize`, auto-vectorizable).

Source: [`containers/benches/bplus_bench.rs`](../../benches/bplus_bench.rs).

## Derived Geometry

| `NODE_SIZE` | `LEAF_CAP` | `INTERNAL_KEY_CAP` | `INTERNAL_CHILD_CAP` | `MAX_DEPTH` |
|---:|---:|---:|---:|---:|
| 64  | 14 |  7 |  8 | 8 |
| 128 | 30 | 14 | 15 | 6 |
| 256 | 62 | 30 | 31 | 5 |

`LEAF_CAP = (NODE_SIZE − 8) / 4` (8-byte header + `link`, 4 bytes per `u32`).
`INTERNAL_KEY_CAP = (LEAF_CAP − 1) / 2` so keys and child pointers both fit in
`data[..]`. Max depth is chosen so the tree can index `u32::MAX` keys at the
worst-case branching factor of that layout.

## Workloads

All workloads use 1M unique `u32` keys generated from a fixed-seed LCG
(`bench_all` in `bplus_bench.rs`). `TRACK = false` for every configuration
— we measure the raw tree, not the mark/restore protocol.

| Workload | Description |
|---|---|
| `build_from_sorted_1m` | Bulk bottom-up construction from a sorted slice. |
| `insert_random_1m` | 1M per-key `insert` in random order into an empty tree. |
| `seek_monotonic_10k` | 10K monotonically-increasing seeks into a 1M-key tree. Exercises the cursor-local fast path (current leaf, then next-linked leaf). |

## Results

Medians, criterion `sample_size(10)`, Apple Silicon laptop, `release` profile.

| Workload           |  64-bin |   64-br |  128-bin |  128-br | 256-bin | 256-br | `BTreeSet` |
|--------------------|--------:|--------:|---------:|--------:|--------:|-------:|-----------:|
| build_from_sorted  | 1.42 ms | 1.37 ms |  1.00 ms | 0.83 ms | **0.65 ms** | 0.66 ms |  5.10 ms |
| insert_random      |  224 ms |  228 ms |   188 ms |  181 ms | **171 ms** |  181 ms |   157 ms |
| seek_monotonic_10k | 0.91 ms | 0.87 ms |  0.98 ms | 0.99 ms | **0.71 ms** | 0.81 ms |  0.64 ms |

Bold = fastest `BPlusTreeSet` configuration for that row. `BTreeSet` is
`std::collections::BTreeSet`, included as an external baseline.

## Analysis

**Node size dominates.** Moving from 64 → 256 bytes is:

- ~2.2× faster on bulk build,
- ~1.3× faster on random insert,
- ~1.3× faster on monotonic seek.

Two mechanisms explain this. First, fewer tree levels means fewer arena
loads per descent (depth drops from 6 → 3 at 1M keys). Second, every `VecI`
write copy-modifies one full node into the diff log; a 256-byte node
amortizes that cost across 62 keys instead of 14, so insert-heavy workloads
cost roughly `O(nodes_touched × NODE_SIZE)` rather than `O(keys × NODE_SIZE)`.

**`Branchless` barely moves the needle.** At 14-key leaves it's ~4% faster;
at 30 keys it's a wash; at 62 keys `BinarySearch` wins on seek (log₂ 62 ≈ 6
probes vs. a 62-element linear scan the compiler is not fully vectorizing
on this target). Net: keep `BinarySearch` as the default. `Branchless` may
still be the right call on targets where LLVM emits good SIMD for the linear
form — worth re-measuring before shipping to a different ISA.

**vs. `std::BTreeSet`.** We beat it by ~8× on bulk build (our
`from_sorted` is a single bottom-up pass; `BTreeSet::from_iter` is `n`
insertions). Seeks match within ~10%. Random insertion is ~9% slower — the
`VecI` arena copy-modifies a whole node on each mutation, whereas `BTreeSet`
mutates in place. That gap is the price of semi-persistence; it disappears
in workloads that care about build or query more than mutation.

**Cursor fast path.** The monotonic-seek numbers include the fast path added
in Part 1: before descending from root, the cursor checks (a) the current
leaf and (b) the next linked leaf. For strictly-increasing seek patterns
(leapfrog join, delta iteration) every seek after the first is an O(1) leaf
step rather than an O(log n) root descent. Not isolated in this table, but
the shape of the `seek_monotonic_10k` column vs. seek-into-cold-tree runs
confirms the intended behavior.

## Recommendation

Change the default layout from `Layout64` to `Layout256`:

```rust
pub struct BPlusTreeSet<
    L: NodeLayout = Layout256,          // was Layout64
    S: SearchKind = BinarySearch,
    const TRACK: bool = true,
> { ... }
```

The 64-byte default was chosen when the node was hand-written to fit one
cache line. Now that the layout is parameterized and benchmarked, 256 is
strictly better on every workload measured here; the only reason to pick
a smaller layout is memory-constrained deployments where tree footprint
matters more than throughput.

## Caveats

- Single machine, single architecture (Apple Silicon). x86_64 with AVX-512
  is likely to move the `Branchless` numbers; re-run before changing that
  default for other targets.
- `TRACK = false` throughout. Once the `IndexStore` integration (the
  configurable B+tree index backend — see the egraph crate's
  `doc/future/semi-naive-deferred-work.md`) lands, re-measure with
  `TRACK = true` — mark/restore cost scales
  with node size, so the "bigger nodes win" conclusion could soften.
- `insert_random` is the worst case for a B+ tree (no locality). Real
  e-graph index updates are more clustered; a future bench should cover
  that pattern once semi-naive evaluation (Part 3) exposes representative
  insertion traces.

---
[← Ch 7: BPlusTreeSet](07-bplus-tree.md) · [Table of Contents](00-table-of-contents.md)
