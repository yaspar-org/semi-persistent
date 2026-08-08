# Layout, Algorithm, and Erasure Parity with Production

*Status: living audit, updated with fix 3 (2026-08-02). The
conformance crate (`containers-conformance`) enforces the testable rows:
`tests/layout_parity.rs` (sizes), `tests/differential.rs` +
`tests/list_arena_differential.rs` (behavior),
`benches/retained_containers_bench.rs` (performance, gate: ±10% or a
recorded exception).*

The migration requires the verified containers to use the SAME layouts,
algorithms, and bit-stealing niches as production, and the same
compile-time erasure of tracking code under `TRACK=false`. This chapter
records the audit per container.

## Erasure model

`TRACK` is a const generic on every container. Production gates every
tracking touch on `if !TRACK { return; }` / `TRACK && ...`, which
monomorphization folds away. The verified crate now does the SAME
(fix 2): the `DiffStore` capture contract is `TRACK ==>` conditional, both
store impls gate flag work on the const, and `Vec`'s wf carries
`!TRACK ==> frames.len() == 0` so the hot paths' `TRACK &&` gates are
provably complete. Disassembly-verified: the `TRACK=false` push loop
compiles to the same `Vec::push` code as production's.

## Per-container audit

| container | layout | algorithm | niche/bit-stealing | erasure | perf (prod → verus) |
|---|---|---|---|---|---|
| `Vec` + `ParallelStore` | data `Vec<T>` + packed `Vec<u64>` capture words (fix 2) | first-write-wins capture; on-demand flag materialization at `set_bit`, with `prepare_mark` EAGERLY bulk-resizing the word vector to cover the data length (production's protocol verbatim — `zero_and_materialize`; see the fix-3 note below), `finish_restore` zeroing in place | flag bits packed 64/word, same as production's bitset | ✅ TRACK=false push/pop = plain `Vec` ops | untracked push +20% residue (codegen, see below), pop verus faster; tracked mark-churn at parity |
| `Vec` + `InlineStore` | `Vec<T::Repr>` — the value IS its repr | tag-bit capture in the stolen MSB; `prepare_mark` = production's SPARSE clear (only prev-frame diff slots, O(diffs) — backed by the new no-stray-flags wf invariant); `finish_restore` = set-only O(surviving) | ✅ same stolen-MSB scheme | ✅ TRACK-gated | mark-churn sweep (200 marks × 8 writes): **verus faster at 1k/100k/1M** (8.0/10.2/11.5 µs vs 9.8/15.2/16.3) |
| `ListArena` | node/head ELEMENT layouts production-identical (8B/12B @ 31-bit, asserted by layout_parity). ARENA representation differs: inner vecs are `ParallelStore` with `usize` diff indices (production: `VecI`/InlineStore with typed `N::Index` diffs) — tracked mode carries two side bitmaps production doesn't | same: intrusive singly-linked arena, O(1) append/prepend/splice via cached tail, single head read per op | ✅ next/head pointers niche-packed via the verified `Opt<N>` MSB tag; the arena's capture flags are side-bitmap (production: stolen bit in the element repr) | ✅ (arena is TRACK-gated through its inner Vecs) | TRACK=false: append_iter **verus 20% faster**, build+splice composite **verus 8% faster** (setup-dominated — does not isolate splice); tracked arena still unbenchmarked (the gated ring rows use `CircularList`) |
| `AppendOnlyVec` | `Vec<T>` + frame lengths | push-only, restore = truncate | n/a | ✅ | parity (85.4 vs 85.8 µs) |
| `SparseSet` | 3 parallel columns | swap-remove permutation, LIFO id pool | inline stores steal the id MSB | ✅ | **verus 14% faster** |
| `SpMap` | `AppendOnlyVec` log + `std::collections::HashMap<K, usize, IndexHasher>` index | log = source of truth, index rebuilt on restore — same algorithm; index uses production's hash ALGORITHM (hashbrown 0.17 default = foldhash), seeded deterministically by default | n/a | ✅ | **parity across u64/String/composite — exception CLOSED, see below** |
| `BPlusTreeSet` | fat nodes (documented divergence; frozen per rev 3 descope) | verified insert/cursor | arena ids niche-packed | ✅ | not gated (descope) |
| `CircularList` | `payload + usize` ring | O(1) ring splice | not packed (PR 3 consumer work) | ✅ | not gated until PR 3 |

## Closed exception: SpMap index hasher (was map/intern +100%)

Originally the verified `SpMap` index was `std::collections::HashMap` with
its default `RandomState` (SipHash), while production's `Map` index is
`hashbrown::HashMap` (foldhash) — a +48–100% gap depending on key shape.
The fix does NOT require a hashbrown model. The KEY OBSERVATION: vstd models
`std::collections::HashMap<K, V, S>` GENERICALLY over any `S: BuildHasher`
(`insert`/`get`/`contains_key`/`len`/`clear`/`default` are all `S`-generic,
gated on `builds_valid_hashers::<S>()`), and std's HashMap is hashbrown
internally. So the index is now
`std::HashMap<K, usize, IndexHasher>`, where `IndexHasher` is an 8-byte
crate-local `BuildHasher` delegating to foldhash's `fast` family — the same
hash ALGORITHM production uses, in the SAME container vstd already models.
Full production speed, zero algorithmic change.

Two precision notes, since "the same hasher" is easy to overclaim:

- **Not the same type.** hashbrown 0.17's default is
  `hashbrown::DefaultHashBuilder`, a newtype wrapping
  `foldhash::fast::RandomState` that forwards every `write_*` to it
  (hashbrown-0.17.1/src/hasher.rs:14). `IndexHasher` is a different newtype
  over the same foldhash algorithm — same speed, one wrapper apart.
- **Hash values ARE reproducible by default** (unlike production). Production's
  `DefaultHashBuilder` draws a random per-process seed. `IndexHasher` instead
  defaults to a fixed seed and lets the operator control it (`SP_HASHER_SEED`,
  `set_default_seed`, `with_seed`), so a run's hashing is byte-for-byte
  reproducible. This is a deliberate divergence FROM production, in the
  reproducibility direction; it changes no observable `SpMap` behaviour (the
  index is transient, rebuilt from the log in insertion order, never iterated),
  only the internal bucket layout — see `src/hasher_spec.rs`.

Cost: exactly one axiom,
`hasher_spec::axiom_index_hasher_builds_valid_hashers`, mirroring
vstd's own shipped `axiom_random_state_builds_valid_hashers` for std's
`RandomState` — same shape, same strength, same `admit()` justification
(the predicate is `uninterp`; `builds_valid_hashers` asserts only
byte-determinism, which `IndexHasher` satisfies at least as strongly, its seed
being stored by value). Plus 2 contract-free type registrations
(`ExIndexHasher`, `ExFoldHasher`) so the types can be named in specs. It is
UNCONDITIONAL (not `literal-types`-gated) because the index is core.

Re-measured (HEAD, criterion medians). The SpMap exception is **closed**:
all three map rows are at or better than parity, where before the fix
`map/intern` was +100%.

| row | prod | verus | delta |
|---|---|---|---|
| `map/intern` (u64) | 1.31 ms | 1.31 ms | +0.4% |
| `map/intern_string` | 3.54 ms | 3.58 ms | +1.2% |
| `map/intern_composite` ((u32, Vec<u32>)) | 3.31 ms | 3.29 ms | −0.6% |

**Run-to-run caveat on `map/intern`.** An earlier isolated measurement read
1.98 ms prod vs 1.24 ms verus ("verus 1.6× faster"). That ratio does NOT
reproduce: the *production* side alone moved 1.98 → 1.31 ms between runs, so
the apparent win was mostly measurement context, not an algorithmic
advantage. Both sides run the same append-only-log + rebuilt-index
algorithm over the same hash algorithm, so **parity is the expected and
claimed result**; treat u64 intern as "between parity and modestly faster,
depending on run context" until the perf-ratio gate pins it with fixed
seeds and multiple samples.

## Fix 3: eager capture-word materialization (was nested_mark +28–112%)

`nested_mark/vecp_deep_history` measured +112% at depth 2 / +28% at depth 32.
It was a REAL algorithmic divergence, and the only one found in the mark /
restore / capture paths:

- Production's `prepare_mark` (`containers/src/diff_store.rs:118-127`) zeroes
  the materialized capture words AND THEN calls
  `captured.resize(data.len().div_ceil(64), 0)` — one bulk memset that
  materializes every word the frame could need.
- The verified `prepare_mark` called `zero_all()` only. Words were still
  materialized correctly, but LAZILY, inside `set_true`'s one-word-at-a-time
  push loop — so a frame paid the growth loop on its own write path.

The divergence is invisible when a frame's writes are clustered and severe when
they are spread, which is why the depth-2 nested case (few writes, 100k-element
span, ~1560 words to materialize) was the worst row in the suite. Isolated
per-write cost over a 100k-element vector, 128 writes:

| write span | words to materialize | prod | verus (lazy) | verus (fix 3) |
|---|---|---|---|---|
| 1 000 | 16 | 11.0 ns/write | 7.0 ns/write | 5.8 ns/write |
| 100 000 | 1 563 | 6.8 ns/write | 15.9 ns/write | 6.1 ns/write |

`CaptureBits::zero_and_materialize` now mirrors production exactly. Criterion,
same run context, before → after:

| row | prod | verus before | verus after |
|---|---|---|---|
| `nested_mark/.../2` | 1.30 µs | 2.78 µs (+112%) | 1.70 µs (+31%) |
| `nested_mark/.../8` | 4.51 µs | 6.39 µs (+38%) | 4.88 µs (+8%) |
| `nested_mark/.../32` | 15.08 µs | 19.61 µs (+28%) | 17.27 µs (+14%) |

Depth 8 is now inside the gate. Depths 2 and 32 are not, and the residue is
NOT the bitmap: a hand-timed decomposition of the same workload puts first
mark, later marks, writes, and restore all within ±4% of production
(d=32: marks 4.71 vs 4.54 µs, writes 10.70 vs 11.01 µs, restore 2.50 vs
2.49 µs), and a single-timer whole-body run measures −0.8%/−1.4%/−0.0% at
depths 2/8/32. The gap only appears under criterion's `iter_batched_ref`
batching, so it is measurement-context-sensitive and needs the automated
perf gate (fixed seeds, multiple samples) to attribute; it is recorded here as
OPEN rather than explained.

## Closed: the tracked-Vec gap was ONE missing `inline(always)` (RETRACTS the "layout artifact" reading)

The `mark`/`set`/`restore` rows are now at parity or verus-faster for a
substantive reason, and a previous conclusion in this chapter is **retracted**.

**What was wrong.** After the PR-2 consumer swap, `nested_mark` shifted toward
+7–11% and this chapter concluded "code-layout alignment, not an algorithmic
regression", citing a dead-code experiment (200 never-called functions in the
pre-swap crate reproduced the shift). The dead-code result is real and layout
effects at that scale are real — but the conclusion was **wrong**, and the error
was one of *scope*: a genuine per-op regression was present at the same time, and
a plausible artifact explanation was accepted for it without a test that could
distinguish the two. The tell was ignored: the egraph's own
`vec_bench mark/bitset` row was **+12.8% uniformly across n = 1k … 1M**, and a
layout delta cannot track n over three decades.

**The actual cause.** `CaptureBits::set_true` was missing the
`#[inline(always)]` that production carries on its equivalent `set_bit`
(`containers/src/diff_store.rs:80`). It is the one bitmap op on the `set` capture
path; out-of-lining it costs a call plus spills per first-write, against a body
whose steady-state case is load/or/store.

Restoring the attribute exposed a second, opposite effect: inlining the whole
function also inlined its cold word-growth loop into `finish_restore`'s survivor
pass, raising register pressure enough to spill in `Vec::restore`'s replay loop
(restore 46 → 60 µs, visible in the disassembly as two extra stack reloads per
iteration that production does not have). Splitting the growth path into an
`#[inline(never)] grow_to` gives both: the hot path inlines, the cold path does
not.

| row (100k, index=usize) | before | after |
|---|---|---|
| egraph `vec_bench mark/bitset/1000` | +12.8% | **−9.8%** |
| egraph `vec_bench mark/bitset/1000000` | +12.8% | **−22.0%** |
| `sets` phase (n/2 sequential) | +4.0% | **−31.9%** |
| `restore` phase | +3.6% | **+1.9%** |
| `nested_mark/depth32` | +7…+11% | **+2.3%** |
| `mark_set_restore` | ~parity | **−14.7%** |

`nested_mark` returning to +2.3% is itself the disproof of the artifact reading:
no layout change accompanied the fix.

**Two process lessons.**
1. A confirmed artifact mechanism does not license attributing the *next* gap to
   it. "Layout" was a real phenomenon used as an unfalsifiable explanation.
   The dead-code test shows layout *can* produce a shift; it does not show that
   *this* shift was layout. Ask what observation would distinguish them — here,
   scaling with n — and make it.
2. Gate on **phases, not cycles.** A whole mark/set/restore cycle is
   set-dominated, so it read −25% while `restore` alone was +30%. `perf_gate`
   now carries a separate `restore_replay` row for exactly this reason, and the
   gate is one-sided (only *slower* fails — an `abs()` gate failed the build for
   beating production).

**Standing check:** production's `#[inline]` attributes are part of the interface
to match, not incidental. `containers/src/diff_store.rs` marks `is_bit_set` and
`set_bit` `inline(always)`; any verified counterpart on a per-element path needs
the same, and adding one warrants re-measuring the *neighbouring* phases, since
inlining shifts register pressure into the caller.

## Closed: untracked push is at parity; the +40% was measurement artifact

`micro/push_only_untracked` reported 57.4 µs prod vs 80.5 µs verus (+40% at
100k, +20% at 10k). It is at **parity (+0.1%)**. The reported gap was two
independent measurement confounds, each worth about +18% on its own, and
neither attributable to either implementation.

Two earlier attributions in this chapter were WRONG and are retracted below.
This one is backed by a single-call-site experiment that eliminates both
confounds by construction, so it does not rest on comparing two numbers from
two different program positions.

### The sound measurement

`examples/onesite.rs` selects the implementation at *runtime*, so both arms are
reached through one identical call site, in one binary, at one code offset, and
each is timed both first and last with the best time taken:

```
prod 56.64 us   verus 56.71 us   +0.1%
  (prod first=56.71 last=56.64 | verus first=56.72 last=56.71)
```

Corroborated by `examples/alignprobe.rs`, which pads the text section through
six layouts (PAD = 0/16/32/48/64/80) and finds both arms within 0.1% of each
other at ~56.5 µs in every one.

### Confound 1: position in the process (~+18%)

Whichever arm criterion registers *second* pays it. Registering the **same**
`prod` closure four times in one group:

| slot | time |
|------|------|
| 1st  | 57.9 µs |
| 2nd  | 68.5 µs |
| 3rd  | 68.8 µs |
| 4th  | 68.8 µs |

Swapping the two `bench_function` calls in `micro_untracked.rs` moves the
penalty to `prod` (verus 57.1, prod 67.6). The cause is glibc's `brk`-heap
reuse state after a prior arm has grown and freed 2 MiB: forcing every large
allocation to `mmap` (`MALLOC_MMAP_THRESHOLD_=65536`) collapses the spread from
+18% to within 3.5%. Pre-warming the heap from inside the benchmark does NOT
fix it — the relevant state is per-arena and not reachable from there.

### Confound 2: hot-loop cache line alignment (~+18%)

The same verus source measures 57.5 µs in one bench binary and 70.2 µs in
another, both in isolated single-benchmark processes. The only difference is
where the 8-instruction push loop lands modulo 64:

| binary | loop head `%64` | straddles 64B line | time |
|--------|-----------------|--------------------|------|
| `micro_untracked` prod  | 21 | no  | 57.7 µs |
| `micro_untracked` verus | 21 | no  | 57.5 µs |
| `posprobe` prod         | 21 | no  | 56.5 µs |
| `posprobe` verus        | 56 | yes | 69.9 µs |

Every ~57 µs reading has the loop contained in one cache line; every ~69 µs
reading straddles two. Forcing alignment globally with
`-C llvm-args=-align-all-blocks=N` shifts *both* arms together rather than
closing the gap, which is why it looked like a real regression.

### Why the code cannot account for it

Both arms compile to byte-identical code. Disassembling the actual bench binary
(not a reproducer — that was the earlier mistake):

- the push loop is the same 8 instructions, same registers, same shape;
- both call the *same* `alloc::raw_vec::RawVec::grow_one` symbol;
- `drop_in_place` is 42 instructions on both sides, differing only in jump
  targets;
- the enclosing `Bencher::iter` monomorphizations are 94 instructions each,
  differing only in stack offsets and `lock xadd %eax` (u32) vs `%rax` (u64);
- an instrumented global allocator counts **16 allocations totalling 2,097,120
  bytes on both sides**, identical.

Neither `shr $0x20` nor a `base + i` length recompute appears anywhere in the
real bench binary.

### Two retracted attributions

Both were recorded here as fact and both were falsified. They are kept because
the failure mode is the lesson.

1. **"Instruction selection around the length overflow check."** This chapter
   previously claimed verus emitted `mov`/`shr $0x20`/`jne` (a per-iteration
   high-word test) where production emitted one hoisted `cmp`, and that 12-vs-10
   instructions accounted for +20%. Falsified twice: a standalone reproducer
   produced byte-identical 10-instruction loops on both sides *both containing*
   `shr $0x20`, and the real bench binary contains no `shr $0x20` in either arm.
   Aligning `ParallelStore::len`/`InlineStore::len` to production's exact
   one-liner was still worth doing for structural parity, and it changed no
   codegen.

2. **"The `ContainerId` allocator."** A long instruction-shape bisection
   appeared to show that the `fetch_update` CAS loop and the diverging
   exhaustion panic each split the basic block in `Vec::with_store`, spilling
   the partially-initialized `Vec` and costing +21.8%. The shapes were real and
   reproducible *in the reproducer*, and a control experiment even reproduced
   them in production's `token.rs` — but the reproducer was not the program
   criterion compiles, and the real bench shows none of it. The allocator was
   nonetheless simplified to production's plain `fetch_add` (see
   `src/container_id.rs`), which is the right shape on its own merits; the
   unconditional trap now lives behind the off-by-default
   `strict-id-exhaustion` feature.

The common error in both: attributing a criterion delta to code read from a
*reproducer* rather than from the binary criterion actually ran, and never
testing whether the delta survived swapping the two arms. Both checks are cheap
and are now the first thing to do.

### Standing rule for this chapter

Do not record a prod-vs-verus ratio from criterion's two arms alone. Before
attributing any gap:

1. swap the registration order — if the penalty follows the slot, it is
   positional, not real;
2. reproduce it through `examples/onesite.rs`, which holds call site and code
   offset fixed;
3. if attributing to codegen, disassemble the *bench* binary, not a reproducer.

`benches/micro_untracked.rs` carries a header warning that its
`push_only_untracked` arms are not comparable to each other. It is deliberately
left un-"fixed" so the artifact stays on record.

**Status of the ±10% gate.** The tracked-Vec rows are now CLOSED by the
`set_true` inline fix above (see that section's table): `mark_set_restore`
−14.7%, `restore_replay` +3.3%, `nested_mark` +2.3%/+2.6%, and the egraph's own
`vec_bench mark/bitset` 10–22% faster than production at every size from 1k to
1M. `perf_gate` gates all four rows and passes. The historical readings for these
rows (`nested_mark` +31%/+14%, `mark_set_restore` straddling ±10%) are superseded:
they were the missing-inline regression plus the two confounds, not separate
open questions.

Still open:

- Tracked `ListArena` is still unbenchmarked. The consumer swap landed and did
  NOT close this: `perf_gate`'s tracked ring rows (`class_merge_restore`) run
  `CircularList`, not `ListArena`.
- `list/append_iter`, `list/splice`, `vec/push_pop_untracked` live only in the
  criterion benches; port any disputed row into `perf_gate` before trusting it.
- The remaining containers (`bplus`, `sparse_set`, `map`) have no phase-level
  rows. Given that a single missing `inline(always)` cost 12% here and hid
  behind a set-dominated cycle, per-phase rows are the only trustworthy form.

A RETRACTED claim, kept as a caution: an earlier revision of this chapter
recorded `tracked_vecp` mark-churn @1M as "**verus 45% faster** (247 vs
453 µs)". It does not reproduce. Production measures 453–455 µs (matching), but
verus measures 466–471 µs — roughly 4% SLOWER, not 45% faster. Two independent
runs confirmed. Same class of overstatement as the retracted `map/intern`
"1.6× faster" above: a single isolated measurement read as an algorithmic
result. Do not record a ratio here without a repeat run in a second context.

The automated gate that this warning argues for now exists:
`containers-conformance/benches/perf_gate.rs`, with its recorded per-row
ceilings and their measured spreads in `containers-conformance/BASELINE.md`.

## Closed: the B+tree descent gap was the *lowering* of the bisection, not its shape

The verified `BPlusTreeSet` descent measured **+15…+21% slower** than production
on out-of-cache trees (100k/400k keys) and drove `insert shuffled` to +27%. It is
now **~20% faster** than production, and the cause was one instruction.

**The mechanism.** Production searches a node with `slice::partition_point`, which
internally uses `core::hint::select_unpredictable`. That lowers the loop's
`base` update to `cmovbe`. Our hand-written bisection had already been rewritten
into `partition_point`'s *shape* — `size` shrinks by `half` unconditionally, so
the trip count is exactly `log2(n)` and only `base` is data-dependent — and it
*read* branchless:

```rust
base = if lt { mid } else { base };
```

LLVM does not lower that to `cmov`. Its if-conversion heuristic judged the
compare predictable and emitted `ja`/`jmp`; an arithmetic mask
(`(a & !m) | (b & m)`) gets folded straight back to the same branch. On shuffled
keys that compare is a coin flip, so it mispredicted at roughly half the levels
of every descent. `bplus_layout::sel_usize` now routes the choice through
`select_unpredictable`, and the descent matches production's codegen rather than
only its source shape.

| row (Layout256, n=100k, `onesite_bplus`) | before | after |
|---|---|---|
| `descent (iter)` | +23.5% | **−2.3%** |
| `sm descent` (L1-resident) | +2.2% | **−10.1%** |
| `redescent (dup)` (descent, no mutation) | +29.0% | **+7.0%** |
| `insert shuffled` | +27.6% | **+12.3%** |
| pure descent @400k (both build orders) | +20.9% | **−19.1%** |

The tail step deliberately keeps the plain `if`: it lowers to `adc` on the
compare's own flag, which is cheaper than a forced `cmov`, and is what
`partition_point`'s tail compiles to. `bplus_search.rs`'s `SearchKind::find_ge`/
`find_gt` got the same treatment. `Branchless` (the counting scan) needs none —
its accumulate is branch-free by construction.

**Cost in trust and proof:** one `external_body` wrapper (`sel_usize`, a total
expression with no `unsafe`, whose postcondition *is* `if c { b } else { a }` —
`select_unpredictable` is a codegen hint, not a semantic one) and **zero** proof
debt. `bplus` 139, `bplus_layout` 311, `bplus_search` 9, whole crate **1405
verified / 0 errors** (`./verify-all.sh`, exit 0) — unchanged counts.

**One cost, recorded honestly:** the `cmov` is a small pessimization where the
branch genuinely *is* predictable. `insert asc` moved −0.9% → **+1.7%** and
`from_sorted` +843% → **+965%**, both ascending workloads where the compare
always falls the same way. This is the right trade — shuffled descent is the
common case and worth ~14 points against ~2 — but it is a trade, not a free win,
and `from_sorted`'s real problem is the missing bulk loader, not this.

### Three hypotheses that died, and what killed them

Recorded because each was plausible from *reading* the code, and each was
falsified by measurement. Per this chapter's standing rule, none of them should
have been written down as a cause without the measurement.

1. **Node read shape.** Production's `Node` *is* its `Repr` (`type Repr = $name`,
   `from_repr` = `*r` + a flag mask), so it reads a node as one aligned 256-byte
   block. Ours has `is_leaf: bool` where the repr has `flags: u8`, making them
   different types, so `from_repr` rebuilds field-by-field: 4 scalar loads, a
   `memcpy(248)` from the unaligned `base+4`, and 4 scalar stores. Visible in the
   disassembly, and it looks decisive. It is worth **±1%**: a probe bisecting a
   random arena through both shapes across 32 KB / 1 MB / 64 MB measured +1.8% /
   +1.1% / −0.6%. LLVM forwards neither copy into the arena, so both arms pay the
   same materialization. (In-place search — bisecting the arena slot without
   copying at all — *is* 28–35% faster than either, so there is a real
   optimization here; it is just not a prod-vs-verus difference.)
2. **Arena node ordering.** Production unwinds splits bottom-up from a
   `path: [(ArenaIdx, usize); 24]` array; ours unwinds a recursive `insert_rec`,
   so a parent and its new sibling can land in a different relative order, and
   equal node counts say nothing about parent→child index deltas. Killed by
   building the same key set ascending (where both arms take the append fast path
   and split left-to-right, forcing identical ordering) and shuffled, then timing
   the same probe against each: the gap was +15.3% and +15.5%. Ordering is
   innocent.
3. **Footprint.** A counting global allocator gives prod 1048640 bytes / 4096
   nodes / 24.4 keys-per-node against verus 1048576 / 4096 / 24.4 — ratio
   **1.000x**. Identical node count, heap size, and split policy.

### The process lesson: "branchless in source" is not a measurement

An earlier revision of this work concluded that the branchless rewrite "verified
clean but did not move the benchmark, so branch prediction is not the cause."
That conclusion was **wrong**, and the error is worth naming: the *source* was
branchless and the *machine code* never was, so the hypothesis had not been
tested at all. Priced standalone, the branchy bisection cost +137% on 31-key
nodes with random targets — the signal was there; the tree run simply never
exercised the branchless version.

What finally found it was diffing the two arms' disassembly of the *same*
function and reading the branch instructions: `cmovbe` at production's bisection
against `ja` at ours. That is this chapter's rule 3 ("if attributing to codegen,
disassemble the bench binary") applied to a *negative* result — and the general
form is the addition:

**When a source-level optimization measures as no-change, verify it was
compiled before concluding the mechanism is absent.** A no-op result has two
readings — the mechanism is innocent, or the change never happened — and they are
distinguished by reading the asm, not by re-running the benchmark.

## The honest new bounds (verified surfaces production's silent wraps)

Two places the verified crate REFUSES what production silently corrupts:
- `Vec::push` past the index type's capacity: production's
  `try_from_usize(len).expect` panics after the fact; verus traps at the
  guard with the same observable panic, and verified callers prove it
  can't happen.
- `ListArena` length caches are u32 (production parity); a list of 2^32
  elements would silently wrap production's cache. Verus surfaces
  `len + 1 < 2^32` as a requires (dischargeable from the arena bound for
  ≤31-bit ids) and runtime-guards it for unverified callers.

One place the verified crate *declines* to add a bound, because it cannot be
made free: the `ContainerId` allocator. Production's `AtomicU32` counter wraps
after 2^32 containers and silently reuses ids; the verified crate widens the
counter to `u64` (4 billion times the range) but, by default, does **not** trap
on the 2^64 boundary. A trap is available behind `strict-id-exhaustion`. It is
off by default because branching the freshly minted id to a diverging arm costs
+21.8% on constant-count push loops — this was itself one of the retracted
attributions above before the bench artifact was understood, but the +21.8% is
a real, separately reproducible cost of the trap (it degrades production's
`token.rs` identically when added there). The default posture is therefore
"same algorithm as production, 4 billion times the headroom, debug-asserted";
the strict trap is one feature flag away for anyone who wants it fatal.
