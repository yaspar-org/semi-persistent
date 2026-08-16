# Hot-path audit: recomputation and cache locality in the matcher

Audits the matching hot path of the e-graph engine on
`comparison/math-microbenchmark.rules.egg` for redundant recomputation and for
cache-locality defects, and decides between the two with a hardware-counter
measurement. It is a measurement record of one engine on one program. It sits
beside `throughput-gap-ours.md`, which locates the time, and
`throughput-gap-egglog.md`, which records the same for egglog; the fix proposals
in `egraph/doc/design/20-index-selectivity-and-delta-suffixes.md` are the plan
this file supplies evidence for.

**The verdict is compute-bound, and it is not close.** We retire 19.6x more
instructions than egglog for the same program at an instructions-per-cycle rate
within 12% of theirs. No re-layout of any structure can close a gap of that
shape. Every fix below that pays is a fix that removes instructions.

## Base and protocol

Engine at `c895265` (branch `egraph-wf`), release profile (`lto = "fat"`,
`codegen-units = 1`), built and instrumented in a private clone; nothing in this
file is committed to the engine. Runs are
`semi-persistent math-microbenchmark.rules.egg --types machine`, naive strategy.
egglog is the same build the companion file measured, at
`/tmp/egglog/target/release/egglog -j 1 math-microbenchmark.egglog.egg`.

Machine: Apple M4 Pro. Every process launched from this shell runs on the
efficiency cores: a dependent-`add` chain of known length reports 2.60 GHz in
every configuration measured, which is the E-core clock. Both engines were
measured in the same session under the same placement, so the comparison is
sound; absolute cycle counts are not comparable to a P-core measurement.

Instructions and cycles come from `proc_pid_rusage(pid, RUSAGE_INFO_V4)`
(`ri_instructions`, `ri_cycles`), polled at 1 ms until the child exits, in a
27-line C wrapper. Xcode is not installed on this machine, so `xctrace` and the
`CPU Counters` template are unavailable; `powermetrics` does not report
per-process instruction counts. The counters are validated against two
programs with analytically known costs: a loop compiled to exactly 6
instructions per iteration over 10^9 iterations reports 6.012 G instructions,
and a dependency chain of 2 x 10^9 single-cycle `add` instructions reports
2.009 G cycles. Instruction counts repeat to within 0.05% across runs of the
benchmark; wall times vary by up to 5%, so every claim below is stated on
instructions and cycles.

Match-step counts come from `--count-match-steps`. Sample profiles are
`sample <pid>` on the same binaries.

## A. The discriminating measurement

| configuration | instructions | cycles | IPC | wall |
|---|---|---|---|---|
| ours, as shipped | 112.81 G | 30.9 G | 3.65 | 11.8-12.3 s |
| ours, `+P5` (root-driven order) | 9.57 G | 2.28 G | 4.20 | 879 ms |
| ours, `+P5 +P6` | 7.31 G | 1.99 G | 3.66 | 769 ms |
| egglog | 5.75 G | 1.38 G | 4.16 | 534 ms |

**Ours is 3.65 IPC against egglog's 4.16, measured back to back on this
machine.** The task's anchor for egglog was 9.41 G instructions / 2.11 G cycles
/ IPC 4.5; today's build of the same commit reports 5.75 G / 1.38 G / 4.16 on
this machine. The ratio is what matters and the two agree on it: egglog runs at
roughly 4.2 instructions per cycle and we run at roughly 3.7.

An IPC of 3.65 is not a memory-bound engine. A memory-bound engine on this
workload would sit below 1.5. Our load mix is dominated by dependent random
accesses (Section C says where), and the machine still finds enough independent
chains to retire 3.65 instructions per cycle.

The consequence for the audit is sharp. Our wall time is 22.1x egglog's; our
instruction count is 19.6x theirs and our cycle count is 22.4x theirs. If every
load in our engine hit L1 tomorrow and IPC rose to egglog's 4.16, the run would
go from 11.8 s to 10.3 s. **The entire gap is instruction count.** Layout work
is worth doing only where it removes instructions, and this file ranks it on
that basis.

The instruction budget also bounds the residual. With the join order corrected
(`P5`), we retire 9.57 G instructions against egglog's 5.75 G: 1.66x, at IPC
parity (4.20 against 4.16). That is the honest size of the per-step throughput
gap once planning is out of the way, and it is small.

## B. Recomputation inventory

Ranked by measured or estimated instruction share of the shipping
configuration. "Hoist level" names the loop the work is invariant across.

### B1. The whole-relation `ByOp` cursor, rebuilt and re-galloped per partial match

`schedule.rs:331` puts `IndexLookup::ByOp { op }` first in the lookup list of
every `Plain` atom, unconditionally, including atoms that already have a bound
child. `run_join` (`ematch.rs:1430`) then resolves all of them into cursors on
every partial match, and `LeapfrogJoin` intersects them.

On the benchmark's dominant plan, the third join is
`Join(a2 v5<-[op102 & pos0=v0 & pos1=v3])` and it executes 66,981,473 times.
Two of its three cursors are `by_child_pos` buckets holding a handful of parent
ids each. The third is `by_op[Add]`: 86,061 contiguous node ids at iteration 10.
Leapfrog seeks that cursor from position 0 to a target near the maximum on every
one of those 66.98 M calls, which is about 17 doublings plus 17 bisection steps
per call.

The work is invariant at the level of the whole query: the op is a literal in
the plan. Nothing about it depends on any binding.

**Measured**: dropping the `ByOp` cursor from any join that has at least one
other lookup, and re-imposing the operator as a per-candidate `node_op` test,
removes 31.97 G instructions, 28.9% of the run (`P2` in Section D). That is 477
instructions per execution of that join, which is the right size for a 34-probe
gallop plus a hash probe plus one extra cursor in the ring.

The transformation preserves the result set because `IndexStore::build_from`
(`index.rs:139`) files every non-subsumed node into `by_op` and into its child
buckets from the same id stream, so `by_op[op] ∩ by_child_pos[k]` and
`{n ∈ by_child_pos[k] : op(n) = op}` are the same set; the same argument holds
for the delta index and for the difference of the two, because both are built
from a single id stream each. Confirmed empirically: match-step count identical
at 220,704,805 and final node count identical at 1,234,678.

### B2. `completion_column` recomputed, with an allocation, once per fresh node

`OpRegistry::completion_column` (`registry.rs:538`) calls `completion_ops()`
(`registry.rs:522`), which allocates a `Vec<O>` and scans the whole operator map
twice (once filtering `OpKind::MSet`, once `OpKind::Set`), then does a linear
`position` over it. `EGraph::register_if_fresh` (`egraph.rs:2260`) calls it for
every node the engine creates, and `node_monomial_into` (`egraph.rs:951`) and
the splice loop (`egraph.rs:2617`) call it again.

The result is a pure function of the operator registry, which is fixed after
declaration. The hoist level is the program.

**Measured**: memoizing it as an op-indexed table keyed on the registry length
removes 2.24 G instructions, a constant independent of the join order: 2.0% of
the shipping run and 23.7% of the run with the order corrected. That is about
1,800 instructions per fresh node. The doc comment on `completion_column` says
"the pool builder caches the array per round rather than calling this in a hot
loop"; the node-creation path does call it in a hot loop.

### B3. The match-step counter's thread-local read, per `run_step`

`bump_match_steps` (`ematch.rs:70`) reads a `thread_local!` flag on every
`run_step` entry, 220.7 M times. On this target a thread-local read is an
out-of-line call to `_tlv_get_addr`. The hoist level is the query.

**Measured, and the existing attribution is an overstatement**: mirroring only
the flag into a process-global `AtomicBool` removes 0.45 G instructions (0.4%),
because LLVM still emits the `_tlv_get_addr` call for the counter itself,
hoisted out of the disabled branch (TLS address computation is speculatable).
Moving the counter as well removes 2.09 G instructions in total, 1.85%.
`throughput-gap-ours.md` reads the profile's 2.3% self time on `_tlv_get_addr`
as the recoverable cost; the recoverable cost is 1.85% of instructions, and both
halves have to move to get it.

### B4. `find_const` per lookup per partial match

`cursor_in` (`ematch.rs:1493`, at `c895265`) canonicalizes each lookup key with
`eg.find_const(...)` before probing. For the dominant join's first lookup the
key is `v0`, bound two plan steps higher: the value changes 54,051 times while
the call happens 66,981,473 times. The hoist level is the plan step that binds
the key variable.

**Superseded in part.** `ebce993` (already on `egraph-wf`, from the concurrent
snapshot-consistency work) adds `IndexStore::repr`, a per-build canonicalization
snapshot, and replaces the live `find_const` in `cursor_in` with an array read
into it. That removes the union-find walk. The remaining invariant work is the
hash probe itself, below.

### B5. Hash probes for lookup keys bound at a shallower level

After B4, `cursor_in` still does one `FastMap` probe per lookup per partial
match. For the dominant join's `pos0=v0` lookup the key is invariant across
1,239 consecutive calls on average. A one-entry memo per (plan step, lookup
position), keyed on the pre-canonical bound id, would hit 99.92% of the time on
that lookup and 0% on the sibling lookup whose key is bound immediately above.

**Not prototyped.** Estimated at half of `cursor_in`'s share. In the shipping
configuration `cursor_in` is 11.4% of self time; after `P2` it is 17.3% of a
smaller total. The estimate is an inference from the binding structure of the
plan, not a measurement.

### B6. Per-partial-match cursor-set construction and sort

`LeapfrogJoin::new` (`leapfrog.rs:114`) probes every cursor's `key()` to detect
an empty intersection, then calls `sort_unstable_by_key(|it| it.key())`
(`leapfrog.rs:132`), which re-reads `key()` per comparison and enters std's
generic sort driver even at k = 2. `throughput-gap-ours.md` measures the pair at
5.1% of self time and design chapter 20 lists it as a lever.

**Measured, and rejected.** Specializing the sort for k <= 4 (compare-and-swap
at k = 2, an inline insertion sort otherwise) *increases* instructions by 2.4%
and leaves wall time unchanged (`P4` in Section D). std's sort is already
adequate at these sizes, and the hand-rolled insertion sort re-reads `key()`
quadratically. The 5.1% is real, but it is the cost of constructing k cursors
per partial match, not the cost of ordering them: the fix is to construct fewer
of them (B1) or fewer times (B5), not to sort them faster.

### B7. `child_at`: two dependent random loads per extraction

`EGraph::child_at` (`egraph.rs:2542`) resolves `node_ref(id)` through the
routing table and then indexes the arity-specific arena. It is called twice per
`ExtractChild` and once per `CheckChildEq`, and the same child of the same
parent is re-read on every sibling iteration of the join below it. 2.9% of self
time in the shipping profile, 2.3% after the order is corrected. The hoist level
is the parent binding. Not prototyped; the share does not justify the plumbing
before B1 and B2 land.

### What is not recomputed

Index construction is not a recomputation defect on this workload despite being
a full rebuild every iteration: 21.5 ms over the whole run, 0.34%, already
recorded in `throughput-gap-ours.md`. Query planning is 0.26 ms over the whole
run. Match buffers are already recycled through `MatchPool` (`ematch.rs:930`,
`ematch.rs:944`). Nothing in the hot path clones a `Match`.

## C. Layout map of the hot loads

One execution of the dominant join, `Join(a2 v5<-[op102 & pos0=v0 & pos1=v3])`,
in the shipping configuration. Ids are 31-bit (`#[repr(transparent)] struct
ENodeId(u32)`), so every id is 4 bytes.

| # | access | structure and stride | size at iteration 10 | classification |
|---|---|---|---|---|
| 1 | `env.get(v0)` | `Match::nodes`, `Vec<Option<G>>`, one entry per query variable | tens of bytes | L1, sequential |
| 2 | `eg.find_const(v0)` | `UnionFind::parent`, `Vec<u32>` | 4.9 MB | random, pointer-chase of 1-2 links |
| 3 | `by_child_pos.get(&(r, pos))` | hashbrown: control byte array plus entry array, entry is `((u32,u32), SortedVec)` = 32 B | ~2.4 M keys, ~90 MB | two random loads |
| 4 | bucket contents | `SortedVec<G>`, one heap allocation per key, `Vec<u32>` | 2-8 ids typical | dependent random load |
| 5 | leapfrog gallop on `by_op[Add]` | `Vec<u32>`, contiguous | 86,061 ids = 344 KB | doubling stride then bisection inside 344 KB: L1 misses, L2 hits |
| 6 | `child_at` step 1 | `TypedRouting::entries`, `NodeRef` enum, 8 B stride | 1.23 M nodes = 9.9 MB | random |
| 7 | `child_at` step 2 | `FixedArityCache::nodes`, `FixedArityNode<G,O,2>` = 20 B stride | ~20 MB | random, dependent on 6 |

The worst offender for the leapfrog seek specifically is access 5, and it is
worst by instruction count rather than by miss count: 344 KB fits in L2 on this
machine, so the 34 probes per join are mostly L2 hits, and what they cost is 34
iterations of a branchy loop. This is why B1 shows up as a 29% instruction
saving and not as a miss-rate story. Accesses 3 and 4 are the worst by miss
count: one hash probe plus one dependent load into a separate small allocation,
both far outside any cache, per lookup per partial match.

The structure is an array of structures at the node level (`FixedArityNode`
interleaves `global_id`, `op`, `flags`, and the children) and a hash map of
independently allocated sorted arrays at the index level. egglog's is the
opposite on both counts: `SortedWritesTable` holds contiguous tuples sorted by
their timestamp column, column indexes are cached at the table level and
refreshed incrementally from `updates_since` rather than rebuilt, and a delta is
a dense offset range obtained by binary search rather than a separate structure
(`throughput-gap-egglog.md`, "How the delta restriction enters").

Three re-layouts follow from the map. None is implemented here.

**R1. Fold the operator into the `by_child_pos` key**: `by_child_pos[(child_repr,
pos, op)]`. This is B1 done at the source instead of by post-filtering: the
whole-relation cursor never enters the intersection, and each bucket shrinks by
the number of distinct operators that can appear at that position. Expected
magnitude: the same 29% that `P2` measures on the shipping plan, and nothing on
a plan that already drives from the outermost atom (`P2` measures exactly zero
there). Cost: one more word in the key, more keys, a larger index build than the
current 21.5 ms. It is worth doing as insurance against planner mistakes on rule
sets this file does not cover, not as a fix for this one.

**R2. Arena-back the index buckets**: one `Vec<G>` pool per index with
`(start, len)` spans in the map, replacing one heap allocation per key. Removes
access 4's separate allocation, gives neighbouring buckets line sharing, and
turns ~2.4 M allocations per round into one. Expected magnitude on the probe
side: unmeasured. On the build side it is bounded above by the 21.5 ms the
build costs today, which is 0.34% of the shipping run and 2.8% of the run with
the order corrected.

**R3. Replace the `by_child_pos` hash map with a class-indexed two-level
structure.** Class ids are dense, so access 3's hash probe can be an array
index. Expected magnitude: removes one of the two random loads at access 3.
Unmeasured, and it interacts with R1 (which multiplies the key count).

**A layout probe was considered and not run.** The audit's discriminating
measurement (Section A) already establishes that miss attribution cannot explain
the gap, so an A/B on a padded or pruned variant of one structure would measure
a quantity that is bounded by 1.14x end to end. The measurement to make instead,
if R2 is ever pursued, is cycles per probe on the `by_child_pos` path in
isolation.

## D. Prototypes measured

All in the private clone, all switchable by environment variable so one binary
produces every configuration, all against the same benchmark. Instructions are
the primary metric because they repeat to 0.05%; wall time is reported for
scale.

| prototype | what it changes | instructions | delta | wall | verdict |
|---|---|---|---|---|---|
| baseline | `c895265` unmodified | 112.81 G | | 11.8-12.3 s | |
| `P1` | match-step *flag* off the thread-local | 112.36 G | -0.4% | 12.2 s | **partial**: LLVM keeps the TLS call for the counter |
| `P1b` | flag *and* counter off the thread-local | 110.72 G | -1.85% | 11.8-12.1 s | **accepted**: 2.09 G instructions, no behavior change |
| `P2` | drop `ByOp` from multi-lookup joins, re-impose as a per-candidate test | 78.75 G | -28.9% | 7.17-7.34 s | **accepted**: 1.55x, identical match steps and node count |
| `P4` | specialize `LeapfrogJoin::new`'s sort for k <= 4 | 113.40 G | +2.4% | 11.7 s | **rejected**: std's sort is already adequate at k <= 4 |
| `P6` | memoize `completion_column` per op | 108.48 G | -2.0% | 11.6 s | **accepted**: constant 2.24 G, independent of join order |
| `P5` | drive every query from a pattern-root atom | 9.57 G | -91.4% | 879 ms | **evidence only**: changes the match set, see below |
| `P5 + P6` | | 7.31 G | -93.5% | 769 ms | |
| `P5 + P6 + P2` | | 7.31 G | -93.5% | 761-775 ms | `P2` is neutral once the order is right |

`P1b`, `P2`, and `P6` compose additively and none of them changes the result:
match-step count is 220,704,805 and final node count 1,234,678 in every
combination, identical to the baseline.

`P5` is the counterfactual from `throughput-gap-ours.md` obtained without
touching cardinalities: on the first atom selection only, restrict the candidate
set to atoms whose node variable is not a child of any other atom, then let the
existing greedy cost model choose among them. It reproduces the documented
13.57 s -> 0.89 s result (11.8 s -> 0.879 s here) and it reproduces the
documented blocker: the final node count moves from 1,234,678 to 1,247,940,
+1.07%. It also regresses `math-add-ac` (122.8 M -> 133.2 M instructions), so it
is a measurement instrument, not a proposed heuristic. The proposed fix remains
S1 of design chapter 20, measured per-access-path selectivity, with the
snapshot-consistency prerequisite that `ebce993` is addressing.

**`P2` is worth 1.55x when the plan is wrong and exactly nothing when it is
right.** Under `P5` the remaining joins are `ByRepr ∩ ByOp` with `ByRepr`
buckets averaging 2.51 entries, and they execute 2.3 M times rather than 67 M,
so the whole-relation cursor costs nothing measurable. Across the smaller
benchmarks the same pattern holds: `math-add-ac` gains 4.9% from `P2` at the
shipping order and nothing at the root order; `eqsat-basic` and `addac-n17` run
in 3 ms and show nothing either way.

### Profile after the order is corrected

`sample` at 1 ms over the `P5 + P6` run, 532 samples on the main thread. The
matcher is no longer the majority of the work.

| share | symbol |
|---|---|
| 26.3% | `LeapfrogJoin::search` |
| 12.4% | `ListArena::try_append` |
| 9.2% | `FixedArityCache::probe` |
| 9.0% | `ematch::run_step` |
| 7.7% | `UnionFind::find` |
| 6.0% | `apply::eval` |
| 5.5% | `EGraph::add` |
| 2.8% | hashbrown `reserve_rehash` |
| 2.8% | `rebuild_congruence` |
| 2.3% each | `child_at`, `EClasses::add_use`, `NodeStore` insert path |
| 2.1% | `ematch::cursor_in` |

Matching is about 45% of the run and term construction (hash-consing, use-list
append, congruence rebuild) is about 40%. That is a different engine from the
one `throughput-gap-ours.md` profiled, where the join machinery was 89.6%.

## Ranked fix list

Magnitudes are on the shipping configuration unless stated. Cost is an estimate
of implementation effort, not of risk.

| rank | fix | magnitude | cost | evidence |
|---|---|---|---|---|
| 1 | S1 of design chapter 20: per-access-path selectivity constants in the cost model | 12.9x | medium, plus the snapshot prerequisite | `P5` measures the ceiling at 9.57 G instructions |
| 2 | Memoize `completion_column` per operator | 2.24 G instructions, constant: 2.0% shipping, 23.7% post-S1 | one afternoon | `P6` |
| 3 | Drop `ByOp` from any join with a bound-child lookup (or R1, fold the operator into the key) | 1.55x shipping, 1.00x post-S1 | small for the post-filter, medium for R1 | `P2` |
| 4 | Move both the match-step flag and its counter off the thread-local | 1.85% | one hour | `P1b` |
| 5 | S3 of design chapter 20: per-binding driver selection inside the leapfrog seek | attacks 26.3% of the post-S1 run | medium | unmeasured |
| 6 | Memoize the per-lookup bucket resolution for keys bound at a shallower level (B5) | estimated half of `cursor_in`: 8-9% of the post-`P2` run | medium: needs a per-plan-step scratch area threaded through `run_step` | unmeasured |
| 7 | R2, arena-back the index buckets | bounded by 21.5 ms of build plus an unmeasured probe win | medium | unmeasured |
| | | | | |
| -- | Specialize `LeapfrogJoin::new`'s sort | **rejected**, +2.4% instructions | | `P4` |

## What the 10%-of-egglog target needs

Design chapter 20 sets acceptance at within 10% of egglog's wall time on the
rules encoding. Measured on this machine today that is 534 ms, so the target is
588 ms.

Fixes 1 and 2 get to 769 ms, which is 1.44x the target. They are both necessary:
fix 1 alone is 879 ms and fix 2 alone is 11.6 s. Neither is optional and no
combination of the rest substitutes for fix 1.

The residual 1.31x has to come out of the profile above, and it is no longer
mostly matching. At 769 ms we retire 7.31 G instructions against egglog's
5.75 G, 1.27x, at an IPC of 3.66 against their 4.16. Closing it needs both a
1.27x instruction reduction and the IPC to hold, and the IPC is the part this
audit cannot promise: `P6` removed cheap high-parallelism work and IPC fell from
4.20 to 3.66, which is what remains when the easily-pipelined instructions are
gone. Fix 5 attacks the largest single remaining item (`LeapfrogJoin::search`,
26.3%) and fix 6 the third-largest path; together they are the right size for
1.31x only if they land near their estimates, and both estimates are unmeasured.

The term-construction half of the post-S1 profile is untouched by every fix in
this file. `ListArena::try_append` at 12.4%, `FixedArityCache::probe` at 9.2%,
and hashbrown's `reserve_rehash` at 2.8% are the hash-consing and use-list path,
and they are 24% of the run. Whether that path has a 1.3x in it is a
measurement, not an inference, and it is the measurement to make after fixes 1
and 2 land: at that point it is a larger target than the join.

**Fixes 3 and 4 do not move the target and should still land.** Fix 3 is worth
1.55x on any rule set where the planner picks an inner atom, which is a
correctness-of-cost-model failure that S1 reduces but does not prove absent;
fix 4 is 1.85% for an hour's work and it corrects a comment in `ematch.rs:30-34`
that claims the disabled counter costs zero.

## Addendum, 2026-08-16: the state after the selectivity fix, and one correction

Re-measures the same benchmark at `5289140`, the first commit carrying both of
the audit's top two fixes (S1 measured selectivity in `16ddfea`,
`completion_column` memoized in `84af7d6`), then records what nine further
changes did. Same machine, same efficiency-core placement, same `ipcwrap`
counters, egglog re-measured in the same session. The sections above are the
record of an earlier commit and are left as written.

### A'. The gap at `5289140`

| configuration | instructions | cycles | IPC | wall |
|---|---|---|---|---|
| ours at `5289140` | 6.89 G | 1.96 G | 3.52 | 758 ms |
| egglog | 5.74 G | 1.35 G | 4.25 | 524 ms |

Section A measured a 19.6x instruction gap. At this commit it is 1.20x, and
the cycle gap is 1.45x. The verdict "compute-bound, and it is not close" was
true of the configuration it described and is no longer true here: with the
instruction counts within 20% of each other, IPC is half the remaining gap.

### B'. Where the instructions go, by phase

`proc_pid_rusage` read around each stage of `saturate_spec` in a private clone.
The probe costs 5,887 instructions and is called 825 times over the run, so it
accounts for 0.14% of what it measures. Phases sum to 96.5% of the total; the
remainder is parsing, sort checking, and the `print-size` and `print-stats`
commands the benchmark ends with.

| phase | instructions | share | cycles |
|---|---|---|---|
| apply and term construction | 3.43 G | 49.6% | 960 M |
| matching | 2.82 G | 40.7% | 793 M |
| index build | 237 M | 3.4% | 73 M |
| rebuild | 188 M | 2.7% | 60 M |
| outside the saturation loop | 242 M | 3.5% | 52 M |
| query planning | 3.6 M | 0.05% | 1.0 M |
| index statistics | 0.1 M | 0.00% | 0.05 M |

The audit's closing prediction holds: term construction is the larger half,
and it is untouched by every fix ranked above.

The trailing print commands are 220 M of our instructions and 50 M of our
cycles, measured by deleting them from the program. They are 430 M and 89 M of
egglog's, so they are not a source of the gap and both engines keep them.

### C'. Correction: fix 3 is worth 19% of cycles, not nothing

Section D concluded that dropping `ByOp` "is worth 1.55x when the plan is wrong
and exactly nothing when it is right", on the evidence of `P2` measured under
the `P5` root-driven counterfactual. **That conclusion does not transfer to the
order the selectivity constants actually choose, and the ranked list understated
fix 3 by a factor it can be measured at.** Chapter 20 records the chosen plan:
it scans `Mul`, joins `Add` through `by_child_pos`, and re-joins the second
`Mul` through `by_repr`. Two of those three joins intersect a bound-child bucket
with the whole `Add` or `Mul` relation, where `P5`'s remaining joins intersected
`ByRepr` buckets of 2.51 entries. Measured at `5289140`: 6.89 G to 6.35 G
instructions, 1.96 G to 1.59 G cycles, 758 to 615 ms, with match steps and node
counts identical.

The general lesson is narrower than "P2 is neutral": a whole-relation cursor
costs nothing only when every other cursor in its ring is already small, and
whether that holds is a property of the plan the cost model picks, not of the
cost model being correct.

### D'. Changes measured and landed

Each row is the cumulative state after that commit, rules encoding, and each
was checked to leave match steps at 7,284,276 and the final node count at
1,233,013. All twenty programs under `comparison/` were also checked node for
node and step for step against `5289140`.

| commit | change | instructions | cycles | wall |
|---|---|---|---|---|
| `5289140` | base | 6.89 G | 1.96 G | 758 ms |
| `790ba05` | `ByOp` demoted to a per-candidate operator test | 6.35 G | 1.593 G | 615 ms |
| `e32feda` | per-round `op[id]` table beside `repr[id]` | 6.21 G | 1.575 G | 608 ms |
| `9c6f2aa` | hash-cons entry 16 bytes to 8 | 6.19 G | 1.552 G | 601 ms |
| `e87ebaf` | match-step counter off the per-step thread-local | 6.00 G | 1.540 G | 596 ms |
| `d92a86e` | index buckets filled in place, no map rebuild | 5.95 G | 1.515 G | 586 ms |
| `d9357e6` | fan-out pass reads the `op` table | 5.94 G | 1.514 G | 585 ms |
| `8c62891` | per-op facts of a new node derived once | 5.83 G | 1.490 G | 576 ms |
| `a838f08` | one `extend` per match instead of one push per variable | 5.79 G | 1.489 G | 576 ms |
| `96d222e` | bound node handed to `add` without canonicalizing first | 5.54 G | 1.467 G | 567 ms |

### E'. Final state

Seven interleaved runs of each engine, medians:

| | instructions | cycles | IPC | wall |
|---|---|---|---|---|
| ours | 5.539 G | 1.467 G | 3.78 | 566.7 ms |
| egglog | 5.741 G | 1.352 G | 4.25 | 523.8 ms |
| ratio | 0.965 | 1.085 | 0.89 | 1.082 |

**We now retire 3.5% fewer instructions than egglog and take 8.2% longer.**
Chapter 20's acceptance is within 10% of egglog's wall time on the rules
encoding, and 566.7 ms against 523.8 ms is 8.2%: met.

**The verdict inverts.** Section A's discriminating measurement concluded that
no re-layout could close a gap of the shape it saw, because the gap was
instruction count. The instruction count is now below egglog's and the entire
residual is IPC, 3.78 against 4.25. The re-layout items this file listed and
did not implement (R2, arena-backed index buckets; R3, a class-indexed
`by_child_pos`) are the list that applies from here, together with the use-list
layout below. Whether any of them is worth its cost is a measurement, not an
inference, and none of them has been made.

### F'. Proposed, not landed: append to prepend on the class use-list

`ListArena::try_append` is 14% of the profile at the end of this work, and it
is the largest single item. An append reads the list head, pushes the new node
at the arena's end, then reads and rewrites the old tail node to link it
forward: two random locations. A prepend links the new node to the old head and
rewrites only the head: one. The use-list has no order contract that any
consumer reads.

Measured on top of `96d222e` by swapping `EClasses::add_use` from
`ListArena::try_append` to `ListArena::try_prepend`, which is already verified
with the same postconditions: 5.539 G to 5.488 G instructions, 1.467 G to
1.410 G cycles, 567 to 552 ms. That is 1.054 of egglog's wall time. Match steps
7,284,276 and final node count 1,233,013, unchanged; the e-graph library tests
(639), the AU differential fixture (5) and the egg fixtures (99) all pass.

It is not landed because `EClasses::add_use`'s proof body asserts the appended
list shape directly (`um == oum.update(li, oum[li].push(oun.len()))`, and an
index case split on `um[l].len() - 1`), and the prepend obligations are
`seq![oun.len()] + oum[li]` with the indices shifted by one. Rewriting those
two blocks is mechanical, but Verus is not installed on this machine and
`verus.yml` verifies this crate, so the rewrite cannot be checked here. It is
the next change to make, and it is the one that would take the rules encoding
inside 6% of egglog.

## Addendum, 2026-08-16: R2 and R3 measured

Records what the two re-layout items this file proposed and did not implement
are worth, now that they are implemented. Section E' left the residual as IPC,
3.78 against egglog's 4.25, and named R2 (arena-backed index buckets) and R3 (a
class-indexed `by_child_pos`) as the list that applies from there. They landed
as one change: the four index families moved onto `containers-verus`'s verified
`DenseSpanMap`, which is a flat value pool with `(offset, length)` spans (R2)
addressed by a dense integer key (R3). Splitting them would have meant building
an intermediate structure that was neither.

Same machine, same efficiency-core placement, same `ipcwrap` counters, medians
of seven interleaved runs. **egglog was not re-measured in this session**, so
the egglog column is section E's value and the wall-time comparison against it
is across sessions, not back to back.

| configuration | instructions | cycles | IPC | wall |
|---|---|---|---|---|
| ours before, rules, naive | 5.581 G | 1.484 G | 3.76 | 574.4 ms |
| ours after, rules, naive | 5.484 G | 1.389 G | 3.95 | 537.4 ms |
| ours before, native, naive | 6.056 G | 1.403 G | 4.32 | 542.2 ms |
| ours after, native, naive | 5.748 G | 1.232 G | 4.67 | 477.2 ms |
| egglog (section E', earlier session) | 5.741 G | 1.352 G | 4.25 | 523.8 ms |

Under semi-naive evaluation the same change takes the rules encoding from
620.0 to 560.3 ms at IPC 3.58 to 3.83, and the native encoding from 562.9 to
448.1 ms at IPC 4.09 to 4.65.

**The cycle reduction is three to four times the instruction reduction**, which
is what distinguishes a layout change from a work reduction: 1.7% of
instructions against 6.4% of cycles on the rules encoding, 5.1% against 12.2% on
the native one. Section A's discriminating measurement asked whether re-layout
could pay on this engine and answered no for the configuration it saw; at 0.965x
egglog's instruction count the answer is yes, and this is the size of it.

**Section 4 of the ranked fix list said R2 was "bounded by 21.5 ms of build plus
an unmeasured probe win". Both halves were wrong in the same direction.** The
build did not cost more, it cost less: timed around every `IndexStore::build*`
call over a whole saturation, the rules encoding goes 25.9 to 17.9 ms under
naive evaluation and 45.3 to 27.7 ms under semi-naive, and the native encoding
66.4 to 30.5 ms and 107.1 to 48.9 ms. A two-pass counting sort over a key space
wider than the stream still beats one hash insert and one `Vec` push per entry
into roughly 2.4 M separately allocated buckets per round. And the probe win is
the 6.4% to 12.2% of cycles above.

Peak resident memory rises 3.2% on the rules encoding, 247 to 255 MB, which is
the span tables: they are sized by the largest key in use rather than by the
number of occupied keys.

Match steps and node counts are unchanged on all twenty programs under
`comparison/`, under both scheduling strategies.
