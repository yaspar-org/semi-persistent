# What semi-persistence buys, measured

Work item E6 of `doc/egglog-comparison-plan.md`: quantify the value of
semi-persistence. This file records the mechanism survey, the four
cost-per-cycle tables, and what the numbers do and do not establish. It is not a
claim that our push/pop is asymptotically better than egglog's: the measurement
says it is not, and section 6 says why.

Read `comparison/methodology.md` first. Every divergence this pass introduces is
registered there.

## 1. How each engine implements push and pop

**egglog copies the whole e-graph on push.** `EGraph::push` clones the entire
frontend state and links the copy into a stack; `pop` throws the current state
away and reinstates the copy.

```rust
// egglog src/lib.rs:697
pub fn push(&mut self) {
    let prev_prev: Option<Box<Self>> = self.pushed_egraph.take();
    let mut prev = self.clone();
```

```rust
// egglog src/lib.rs:708, inside pop
Some(mut e) => { ...; *self = *e; Ok(()) }
```

The clone is deep, not a shared-structure copy. `EGraph` holds
`backend: egglog_bridge::EGraph` (`src/lib.rs:286`), whose `db: Database`
(`egglog-bridge/src/lib.rs:116-117`) holds `tables: DenseIdMap<TableId, TableInfo>`
(`core-relations/src/free_join/mod.rs:290-293`). Cloning a `TableInfo` calls
`self.table.dyn_clone()` (`core-relations/src/free_join/mod.rs:175`), which for
the concrete table type is `Box::new(self.clone())`
(`core-relations/src/table/mod.rs:290`), and that `Clone` copies the row storage
and the hash index outright:

```rust
// egglog core-relations/src/table/mod.rs:154
impl Clone for SortedWritesTable {
    fn clone(&self) -> SortedWritesTable {
        SortedWritesTable {
            ...
            data: self.data.clone(),
            hash: self.hash.clone(),
```

So egglog's push is a snapshot copy, cost linear in the base size S, and its pop
is a pointer reinstatement plus the deallocation of the modified copy. Neither a
rebuild-from-log replay nor a journaled undo appears anywhere on the path.

**We journal the difference.** `(push)` takes a mark on every container and
`(pop)` restores to it: `interpret.rs:387` mints `self.eg.mark(policy)`,
`interpret.rs:508-511` calls `self.eg.restore(mark.token)` and truncates the rule
and global tables. `EGraph::mark` (`egraph/src/egraph.rs:2210`) rebuilds, then
marks each of the nine sub-containers; `EGraph::restore`
(`egraph/src/egraph.rs:2232`) restores each. Underneath, the containers store
overwritten values in a diff log and replay only those entries
(`containers/src/diff_store.rs`, the `capture` / `restore_entry` /
`finish_restore` protocol), which is O(cells written since the mark). One
container backend is not: `ParallelStore::prepare_mark` clears a capture bitset
of S/64 words per mark (`containers/src/diff_store.rs:118`), against
`TaggedStore::prepare_mark`, which clears only the previous frame's diff entries
(`containers/src/diff_store.rs:274`). At S = 1e6 that bitset pass is tens of
microseconds and is not what section 3 measures.

The design is therefore O(touched) and the measurement is not, for a reason that
is in our code rather than in the design: **every cache rebuilds its hashcons
index from scratch on restore.** `FixedArityCache::restore`,
`VariableArityCache::restore` and `LitCache::restore` all end with
`self.rebuild_index()` (`egraph/src/caches.rs:318, 634, 767`), and
`rebuild_index` clears the index and re-inserts every live node
(`egraph/src/caches.rs:321`). `NodeStore` holds ten such caches
(`egraph/src/node_store.rs:72-83`), so one `(pop)` re-hashes the whole e-graph.
Section 3 measures exactly that: a bare `(push)(pop)` pair with nothing between
them costs the same as a pop that has real work to undo, and both grow linearly
in S.

## 2. The programs

`gen-semipersistence.py` writes them from seed 20260816. The base is T ground
terms `(Mul (Num a) (Add (Num b) (Num c)))` over constants drawn from one seeded
generator, plus two constant-folding rewrites run to fixpoint. One cycle is

```
(push)
five (Add (Num f) (Num f')) and five (Mul (Num g) (Num g'))   ; ten fresh terms
(union (Var "spuKa") (Var "spuKb"))                            ; fresh classes
(union (Num b) (Num b'))                                       ; two BASE classes
(run 1)
(check ...)
(pop)
```

The second union is deliberate: without it a cycle only appends, and restore
would have nothing in the base to undo. With it, each cycle dirties base state
and each pop must roll it back.

Five variants per base size and per syntax:

| variant | what it runs | cycles |
|---|---|---|
| `base` | the base build alone: the control subtracted from the others | 0 |
| `empty` | base, then bare `(push)(pop)` pairs | 200 |
| `norun` | base, then cycles with the `(run 1)` dropped | 200 |
| `cycles` | base, then full cycles | 20 |
| `rerun` | base plus ONE full cycle body, no push/pop | 1 |
| `rerunnorun` | base plus ONE no-run cycle body, no push/pop | 1 |

`empty` and `norun` run 200 cycles rather than 20 because a 20-cycle delta is
about 15% of the base wall time at the largest size, which is inside this
machine's background-load noise; at 200 the delta dominates the term it is
subtracted from.

**Base-content equivalence.** The two syntaxes carry the same constants, the same
terms and the same two rules, and both engines reach the same base:

| terms T | Add | Mul | Num | egglog reports | we report |
|---|---|---|---|---|---|
| 880 | 880 | 880 | 4 103 | 5 863 | 9 966 |
| 2 650 | 2 650 | 2 650 | 11 531 | 16 831 | 28 362 |
| 8 900 | 8 900 | 8 900 | 36 598 | 54 398 | 90 996 |
| 27 000 | 27 000 | 27 000 | 108 995 | 162 995 | 271 990 |
| 100 000 | 100 000 | 100 000 | 400 966 | 600 966 | 1 001 932 |

The per-operator counts are identical on both engines. The totals differ by
exactly the count of interned `i64` literals, which we count as nodes and egglog
does not (methodology.md section 3). Tables below index base size by our total,
so S = 1e4 through 1e6; egglog's own reading of the same base is the fifth
column.

## 3. Cost per cycle: bare push/pop

Our columns here are superseded by section 11 (2026-08-16), which re-measures
them after restore stopped rebuilding the hashcons index; the egglog column
stands.

Milliseconds per `(push)(pop)` pair, 200 pairs, base wall time subtracted.

| S (our nodes) | egglog | ours, naive | ours, semi-naive |
|---|---|---|---|
| 9 966 | 0.07 | 0.08 | 0.07 |
| 28 362 | 0.19 | 0.21 | 0.22 |
| 90 996 | 0.64 | 0.76 | 0.76 |
| 271 990 | 1.46 | 2.99 | 3.06 |
| 1 001 932 | 6.05 | 12.21 | 12.60 |

Both engines are linear in S. Over the 100.5x range of base sizes egglog's cost
grows 86x and ours grows 153x. egglog's constant is the memcpy of the row buffers
and the hash index; ours is the hashcons rebuild of section 1. At S = 1e6 their
snapshot copy of a 600 966-row database is 2x cheaper than our restore of a
1 001 932-node one.

## 4. Cost per cycle: assume, derive, retract

Our columns here are superseded by section 11 (2026-08-16), which re-measures
them after restore stopped rebuilding the hashcons index; the egglog column
stands.

The same cycle without the saturation step: ten fresh ground terms, two unions,
one check, then pop. 200 cycles, base wall time subtracted.

| S (our nodes) | egglog | ours, naive | ours, semi-naive |
|---|---|---|---|
| 9 966 | 0.26 | 0.10 | 0.10 |
| 28 362 | 0.69 | 0.24 | 0.25 |
| 90 996 | 2.06 | 0.77 | 0.79 |
| 271 990 | 8.07 | 3.06 | 3.07 |
| 1 001 932 | 33.01 | 12.60 | 12.60 |

Ours is 2.6x cheaper at S = 1e6 and both are still linear in S (127x and 126x
cost over a 100.5x size range).

The two engines pay in different places. Our cycle costs 12.60 ms against 12.21
for the bare pair: the twelve assertions, the base-class union and the check add
0.4 ms, and that difference does not grow with S. egglog's cycle costs 33.01 ms
against 6.05 for the bare pair: the same twelve assertions cost them 27 ms, and
that part grows with S too, because a union against the base forces a rebuild
over the tables. So our in-scope work is O(touched) as designed and our
bookkeeping is not; theirs is the other way round.

## 5. Cost per cycle: the full cycle, with one saturation round

**Retracted, 2026-08-16: the "ours, semi-naive" column below was measured at a
stale commit and must not be cited.** It predates the index families moving onto
`DenseSpanMap`, so it charges the semi-naive path a delta index built the way the
full index was. `comparison/span-table-sparsity.md` sections 3 and 5 carry the
superseding per-phase and wall-time numbers. The "ours, naive" and "egglog"
columns stand, and so does the conclusion drawn from them below: the gap at
S = 1e6 is the `(run 1)`, not the push or the pop.

20 cycles, base wall time subtracted.

| S (our nodes) | egglog | ours, naive | ours, semi-naive |
|---|---|---|---|
| 9 966 | 0.95 | 1.88 | 1.90 |
| 28 362 | 1.44 | 5.36 | 5.29 |
| 90 996 | 2.90 | 20.76 | 20.55 |
| 271 990 | 8.44 | 76.14 | 69.24 |
| 1 001 932 | 34.77 | 366.14 | 390.94 |

egglog is 10.5x faster end to end at S = 1e6, and every millisecond of the gap
is the `(run 1)`, not the push or the pop: our cycle costs 366.14 ms against
12.60 for the same cycle without the run, so one round of matching over a
saturated million-node base costs us 353 ms. The control confirms the run is
not being made expensive by the pushed scope: outside any scope, the `rerun`
program costs 1 659.3 ms against `rerunnorun`'s 1 284.0, a difference of 375 ms
for the identical run. egglog pays 1.8 ms per cycle for its run in scope and
30 ms outside it.

That is a result about incremental saturation, not about semi-persistence: after
an assertion batch we re-match the whole base and they match the delta. It
belongs in the E6 write-up because it decides which engine finishes the workload
first, and it is the number to fix before our push/pop advantage is worth
anything end to end.

## 6. The internal baseline: restore versus re-running the prefix

Our columns here are superseded by section 11 (2026-08-16), which re-measures
them after restore stopped rebuilding the hashcons index; the egglog column
stands.

Ours only, so no cross-engine caveat applies. The alternative to semi-persistence
is to re-run the program prefix per cycle in a fresh process, which the `rerun`
programs measure directly: their whole wall time is the per-cycle cost of the
non-persistent scheme.

| S (our nodes) | restore, full cycle | re-run, full cycle | ratio | restore, no-run cycle | re-run, no-run cycle | ratio |
|---|---|---|---|---|---|---|
| 9 966 | 1.88 | 13.38 | 7.1x | 0.10 | 11.30 | 117.3x |
| 28 362 | 5.36 | 32.08 | 6.0x | 0.24 | 26.95 | 114.6x |
| 90 996 | 20.76 | 106.19 | 5.1x | 0.77 | 86.80 | 112.8x |
| 271 990 | 76.14 | 354.42 | 4.7x | 3.06 | 281.38 | 91.9x |
| 1 001 932 | 366.14 | 1 659.27 | 4.5x | 12.60 | 1 283.98 | 101.9x |

Restoring to a mark is 92x to 117x cheaper than rebuilding the base for a cycle
that assumes, propagates a union and checks a consequence, and 4.5x to 7.1x
cheaper once the cycle also pays for a full round of naive matching. Both ratios
are flat in S, because both terms grow with S: the re-run rebuilds S nodes and
our restore re-hashes S nodes, and the second is two orders of magnitude cheaper
per node.

## 7. Macro: calc.egg

`calc.egg` substitutes for the herbie program the plan named. herbie.egg is
`tests/web-demo/herbie.egg` at egglog 7b1adf2, 570 lines with 14 push blocks, and
it is outside the intersection set: it needs `BigRat`, two `:merge` lattice
functions (`hi`, `lo`) and a `(relation non-zero ...)`, none of which we have, and
the non-zero analysis those support gates a large share of its 180 rewrites and
16 rules (methodology.md section 5). `calc.egg` is 61 lines, four push/run/check/pop
blocks, `:until` goals, and needs nothing we lack.

Each block is timed as the difference between two cumulative prefixes
(`gen-calc.py` cuts them), because process-level wall clock cannot see inside a
program.

| config | prefix | block 1 | block 2 | block 3 | block 4 | whole program |
|---|---|---|---|---|---|---|
| egglog | 4.19 | 0.10 | 0.25 | 0.75 | 0.21 | 5.50 |
| ours, naive | 3.05 | -0.15 | 0.08 | 0.31 | -0.05 | 3.25 |
| ours, semi-naive | 2.97 | 0.01 | 0.05 | 0.25 | 0.13 | 3.40 |

Every block on both engines is under 1 ms, which is under this machine's
process-level noise: two of our deltas are negative. The exhibit establishes that
our engine runs a real multi-block egglog program, `:until` goals included, to
the same four checks, and nothing about per-block cost. It cannot establish more,
and neither can any other program in egglog's corpus. Their seven largest
multi-block programs run to completion on egglog itself in, respectively, under
10 ms (`calc`, `web-demo/cyk`, `web-demo/multiset`), 20 ms
(`web-demo/lambda`), 30 ms (`web-demo/typeinfer`), 40 ms (`web-demo/math`) and
60 ms (`web-demo/herbie`, 14 push blocks). There is no large-base push/pop
workload in their test suite to translate.

## 8. What this does and does not show

**Shown.** egglog's push is a full snapshot copy, quoted in section 1 and
consistent with its measured linear growth. Our push/pop is cheaper per cycle
than theirs on the assume/derive/retract cycle at every size measured, by 2.6x at
S = 1e6, and the advantage comes from the in-scope work being O(touched) rather
than from the pop. Restoring to a mark instead of re-running the base is worth
92x to 117x per cycle on our engine, or 4.5x to 7.1x when the cycle also
saturates.

**Not shown: an asymptotic separation. RETRACTED 2026-08-16, see section
11.4; do not cite this paragraph.** The expected shape was flat-versus-linear
and the measurement is linear-versus-linear. Our pop is O(S) because it rebuilds
ten hashcons indexes, so the O(touched) diff journal underneath never shows
through. Nothing here supports a claim that semi-persistence changes the cost
class of push/pop against a copying engine; it supports a constant-factor claim
of about 2.6x on this workload, and an O(touched)-versus-O(S) claim only about
the work done inside a scope.

**Not shown: an end-to-end win on this workload.** egglog finishes the full
cycle 10.5x faster at S = 1e6 because their incremental saturation costs 1.8 ms
where our naive round costs 353 ms. Cheap push/pop does not pay for that.

**Caveats.** Base content is equivalent by construction and verified per-operator
(section 2), but the two engines' totals are not comparable and no claim here
rests on comparing them. The confounds methodology.md section 7 lists apply: one
machine, one OS, both engines single-threaded, no CPU pinning, and this pass ran
with a user application holding roughly half a core, which is why the reported
statistic is the minimum of the timed runs rather than the median. The 2.6x in
section 4 is a ratio of two engine implementations on one workload shape, not a
property of the two state-management designs.

**Postponed, with the condition that would revive it.** The flat-versus-linear
result is not disproved, only unmeasured: it needs a pop that does not rebuild
the hashcons index. Making `restore` roll the index back through the same diff
journal that rolls the node arena back would remove the only O(S) term we found
on the path. Re-run section 3 after that change; if the bare push/pop cost stops
growing with S, the separation this experiment looked for exists and this file's
conclusion is superseded. Section 11 is that re-run: it stopped
growing, and one term the paragraph did not anticipate, the literal interner's
own index rebuild, had to go with it.

## 9. Conclusion

Sections 11.1 to 11.4 supersede the two paragraphs below that give factors for
our push/pop: after the index fix the separation is one of cost class, not of
constant. The rest of this section stands.

Semi-persistence is worth 92x to 117x per assume/check/retract cycle against
re-running the base, and that number needs no cross-engine caveat: it is the
honest answer to what you would do without it. Against egglog it is worth 2.6x
per cycle at a million nodes and not a change of cost class, because our pop
re-hashes the whole e-graph even when the cycle touched thirty nodes, and because
their snapshot copy of the same base is a memcpy that runs at a similar rate per
node. The workload's total time is decided elsewhere: at a million nodes egglog
runs the whole cycle 10.5x faster than we do, on the strength of incremental
saturation, and no improvement to push/pop closes that.

## 10. Reproducing

```
python3 gen-semipersistence.py      # writes sp-t<T>.<variant>.<engine>.egg from seed 20260816
python3 gen-calc.py                 # cuts calc.{egglog,native}.egg into cumulative prefixes
python3 run-semipersistence.py --runs 7 --warmups 2 \
    --ours <pinned>/semi-persistent --egglog <pinned>/egglog
```

Only the T = 880 programs are committed; the larger ones are 87 MB and the
generator reproduces them byte for byte from the pinned seed. `semi-persistence.csv`
holds every timed run.

Binaries for the tables above were pinned copies, because another agent rebuilt
the shared `target/` mid-sweep and the first pass mixed two binaries:
`semi-persistent` md5 038284b34342ebc52148956704677c83, branch egraph-wf at
413f590 plus the uncommitted engine changes in flight at 2026-08-16 13:04;
`egglog` md5 9213d10fe3777cce331a6eba317e3945 at their commit 7b1adf2. The
contaminated first pass is a usable control: it reproduces every number in
sections 3, 4 and 6 within 8%, so the in-flight matcher and scheduler changes do
not move these measurements. Per methodology.md section 6 the submission's final
tables re-run at one pinned commit.

## 11. Addendum, 2026-08-16: restore stopped rebuilding the hashcons index

Section 8 postponed the flat-versus-linear result and named the condition that
would revive it: a pop that does not rebuild the hashcons index. This section
records that change and its measurement. It supersedes our columns in sections
3, 4 and 6 and the two "not shown" claims in section 8; it does not re-measure
sections 5 and 7, and the egglog columns everywhere are unchanged.

**What changed.** `FixedArityCache::restore`, `VariableArityCache::restore` and
`LitCache::restore` delete the index entries of the nodes added since the mark,
which the append-only arena keeps as the contiguous suffix at or above the mark's
length, plus the entries of the pre-mark nodes `recanonize_node` re-keyed inside
the scope, which each cache records in a per-frame list. Both sets are O(touched).
`rebuild_index` survives as the fallback, taken when the two sets together exceed
a quarter of the surviving arena, which bounds the cost of a restore that takes
the rebuild it did not need to a quarter of one. A debug assertion compares the
incrementally corrected index against a from-scratch rebuild after every restore
and runs in the proptest suites.

The literal interner needed the same fix. With the ten node caches corrected, a
sampling profile of 20 000 bare pairs at S = 1e6 put 87% of what remained in
`LitValStore::restore`, which reached `containers::Map::restore`: that map
rebuilds its lookup index from the surviving log on restore, cloning every live
key. Interning is append-only, so `LitValStore` now holds the log and the lookup
index directly and deletes the suffix's keys, on the same fallback terms.

**Protocol.** Same generator, same seed 20260816, same runner, same statistic
(minimum of the timed runs). The two binaries differ only in `egraph/src/caches.rs`
and `egraph/src/literal.rs` and were built three minutes apart from one tree, so
the other engine work in flight on the branch is in both: `semi-persistent` md5
0d315c89bc7ce8b69e5196e9885ca64a (rebuild) and 352ce26b2e6359fb452f4c62293619af
(suffix). egglog md5 9213d10fe3777cce331a6eba317e3945 at 7b1adf2, re-run this
session, reproduces its published columns within 1%, which is what makes this
session's numbers comparable to the tables above. Every run is in
`semi-persistence-index-restore.csv`.

### 11.1 Cost per cycle: bare push/pop

Milliseconds per `(push)(pop)` pair, 200 pairs, base wall time subtracted: the
protocol of section 3, so the first two columns are directly comparable to it.

| S (our nodes) | egglog | ours, rebuild | ours, suffix | ours, suffix, 20 000 pairs |
|---|---|---|---|---|
| 9 966 | 0.07 | 0.08 | 0.005 | 0.0042 |
| 90 996 | 0.64 | 0.76 | 0.009 | 0.0041 |
| 1 001 932 | 5.99 | 12.38 | 0.074 | 0.0029 |

Read the fourth column as an upper bound and the fifth as the value. Once a pair
costs a few microseconds, its 200-pair total is under a millisecond against a
base build of 1.3 s, and the difference is dominated by run-to-run variation in
the base term; the fifth column runs 20 000 pairs per program (`empty20k`,
opt-in in both scripts), which puts the difference at 4.4%, 94% and 690% of the
base for the three sizes. On that
column the cost per pair does not grow over a 100.5x range of base sizes: 4.2,
4.1 and 2.9 microseconds, where the ordering inside that spread is noise rather
than a trend. Measured their way in the same pass, ours grew 164x over that
range before the change.

The separation section 3 looked for is therefore present: our bare pair is flat
in S and egglog's grows 81x over the same range, ending 5.99 ms against our
0.074 ms measured their way, or 0.003 ms measured at full resolution.

### 11.2 Cost per cycle: assume, derive, retract

The section 4 cycle without the saturation step, 200 cycles, base subtracted.

| S (our nodes) | egglog | ours, rebuild | ours, suffix |
|---|---|---|---|
| 9 966 | 0.26 | 0.10 | 0.027 |
| 90 996 | 2.06 | 0.77 | 0.036 |
| 1 001 932 | 33.00 | 12.40 | 0.075 |

The cycle now costs what the work inside the scope costs: twelve assertions, a
union against the base, and a check, for 27 to 75 microseconds, against 12.38 ms
of index rebuilding for the same base size before. The 2.6x of section 4 becomes
440x at S = 1e6, and the shape rather than the factor is the result: ours is
flat over the 100.5x size range and theirs grows 129x, because a union against
the base forces a rebuild over their tables.

### 11.3 The internal baseline: restore versus re-running the prefix

Section 6's comparison, no-run cycle, ours only, with `rerunnorun` re-measured on
the suffix binary (the re-run programs contain no push or pop, so the change
cannot move them, and it does not: 12.35, 86.53 and 1 311.25 ms against 11.30,
86.80 and 1 283.98 ms in section 6).

| S (our nodes) | restore, no-run cycle | re-run, no-run cycle | ratio |
|---|---|---|---|
| 9 966 | 0.027 | 12.35 | 459x |
| 90 996 | 0.036 | 86.53 | 2 408x |
| 1 001 932 | 0.075 | 1 311.25 | 17 514x |

Section 6 reported this ratio as flat in S at 92x to 117x, because both terms
grew with S. Only the re-run term grows now, so the ratio grows with the base:
that is the same measurement reporting a change of cost class rather than a
constant factor.

### 11.4 What this changes in the conclusions

Section 8's "Not shown: an asymptotic separation" is retracted: do not cite it.
The expected shape was flat-versus-linear and 11.1 measures flat-versus-linear,
on the bare pair and on the assume/derive/retract cycle alike. Section 9's
"2.6x per cycle at a million nodes and not a change of cost class" is retracted
with it.

Section 8's "Not shown: an end-to-end win on this workload" stands unchanged and
is now the whole story: at S = 1e6 the full cycle costs 366 ms of which 353 ms
is one round of naive matching (section 5), and this change removes 12.3 ms of
the remaining 12.6. Cheap push/pop still does not pay for naive saturation, and
incremental matching is still the number to fix before any of this decides which
engine finishes a workload first.

What is left on the bare pair is 3 to 4 microseconds at every size measured.
Section 1's remaining O(S) candidate, `ParallelStore::prepare_mark` clearing an
S/64-word capture bitset per mark, is inside that figure and is not separable
from it at this resolution: the per-pair cost at S = 1e6 is no larger than at
S = 1e4, so whatever that pass costs is under a microsecond. Nothing here needs
another fix; the next measurement that would move this file is a workload with
marks deep enough to make the per-frame bookkeeping visible.

### 11.5 Reproducing this section

```
python3 gen-semipersistence.py --terms 880 --terms 8900 --terms 100000
python3 run-semipersistence.py --configs ours-naive,ours-semi \
    --variants base,empty,norun --terms 880 --terms 8900 --terms 100000 \
    --skip-calc --ours <pinned>/semi-persistent --out <csv>
python3 run-semipersistence.py --configs ours-naive,ours-semi \
    --variants base,empty20k --terms 880 --terms 8900 --terms 100000 \
    --skip-calc --ours <pinned>/semi-persistent --out <csv>
```

`--configs`, `--variants` and `--skip-calc` select a subset of the sweep and are
new in this pass; without them the runner behaves as section 10 documents.
`empty20k` is the 20 000-pair twin of `empty`, generated always and never run by
default, because 20 000 pairs of a snapshot-copying engine is minutes per run.
