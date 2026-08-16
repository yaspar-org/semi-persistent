# add-ac width-scaling sweep

Part (b) of the convergence target in
`egraph/doc/design/20-index-selectivity-and-delta-suffixes.md`: demonstrated separation
under native AC canonization, as a width-scaling sweep of the `add-ac` block over
n = 7..20. The target's claim is that the rules encoding and egglog grow super-linearly
in the sum width while native AC stays flat. This file records what the sweep measured
and where the claim needs qualifying.

It is not a status page. The numbers are one machine, one day, from the binaries named
under "Provenance"; `run-addac-sweep.py` regenerates them and `gen-addac-sweep.py`
regenerates the programs.

## The programs

`gen-addac-sweep.py` emits three programs per width n, generalizing the `add-ac` ruleset
block of `egglog/tests/web-demo/math.egg` (7b1adf2, lines 138-160) from its fixed
seven-term sum to width n:

| file | engine | encoding |
|---|---|---|
| `addac-n<k>.egglog.egg` | egglog | A/C as its two rewrite rules, `(run add-ac 50 :until …)` |
| `addac-n<k>.rules.egg` | ours | the same two rewrite rules, the same budget and goal |
| `addac-n<k>.native.egg` | ours | `Add` declared `:assoc-comm`, both rules deleted, `(run add_ac 1)` |

The input is the right-nested sum 1+(2+(…+n)) and the goal is its full reversal
n+((n-1)+(…+1)), the shape the original block uses at n = 7. Both engines take
`:until`, so egglog and our rules encoding both run `(run … 50 :until (= res goal))`:
the budget of 50 is never the binding constraint at any n measured here (the largest
run reaching the goal uses 4 iterations), so the measurement is time-to-goal, not
time-to-budget. The native configuration keeps `(run add_ac 1)` and the check, so its
command sequence matches the rules encoding.

Our engine runs under the naive saturation strategy, which `src/main.rs` makes the
shipped default. Semi-naive is not reported: it is under investigation, and the
access-path audit named in the design doc gates any semi-naive claim.

**The goal term is bound as a global in all three programs**, rather than left inline in
the check as the original block writes it. This is the one deviation that changes the
problem, and it is deliberate, because without it the three programs are not the same
problem. Our `check` and our `:until` build their terms into the e-graph
(`interpret.rs`, `CCommand::CheckEq` and the `RunGoal` construction both call
`build_cterm`); egglog's query theirs and fail if the term is absent. With the goal
inline, egglog must derive the reversed nesting by rewriting while we get it by
construction and need only connect two existing roots, which is a different and much
smaller search: measured at n = 13, egglog takes 461 ms with the goal inline and 15 ms
with it bound. Binding the goal in all three gives every configuration the same starting
e-graph and makes the wall-time columns comparable. Our language has no non-constructive
check, so this is the only shape both engines express identically.

The check passes in every configuration at every n. No configuration is DNF.

## What the sweep measured

Median wall time over 5 runs after 1 warmup, and the node and iteration counts the
engines report. Per-run values are in `addac-sweep.csv`.

| n | egglog | ours, rules | ours, native |
|---|---|---|---|
| | wall / nodes / iters | wall / nodes / iters | wall / nodes / iters |
| 7 | 6.1 ms / 451 / 3 | 3.5 ms / 501 / 3 | 3.1 ms / 25 / 1 |
| 9 | 6.0 ms / 857 / 3 | 3.9 ms / 947 / 3 | 3.4 ms / 33 / 1 |
| 11 | 6.2 ms / 1 275 / 3 | 4.0 ms / 1 405 / 3 | 3.3 ms / 41 / 1 |
| 13 | 14.8 ms / 13 827 / 4 | 10.3 ms / 15 390 / 4 | 3.6 ms / 49 / 1 |
| 15 | 18.6 ms / 19 685 / 4 | 12.9 ms / 21 768 / 4 | 3.4 ms / 57 / 1 |
| 17 | 22.1 ms / 25 607 / 4 | 16.1 ms / 28 212 / 4 | 3.5 ms / 65 / 1 |
| 20 | 28.1 ms / 34 508 / 4 | 19.8 ms / 37 902 / 4 | 3.5 ms / 77 / 1 |

Over n = 7 to 20: egglog grows 76.5x in nodes and 4.6x in wall time, our rules encoding
75.7x and 5.6x, our native encoding 3.1x and 1.1x.

## The growth

**Native AC is flat, and flat with an exact formula.** Its node count is 4n - 3 at every
width measured, its iteration count is 1 at every width, and its wall time does not move
outside 3.1-3.6 ms across the whole sweep. The 4n - 3 nodes are n literals, n `Const`
nodes, and the 2n - 3 distinct multisets the two nested constructions pass through on
the way in. Both terms flatten to the same multiset over `{Const 1.0 … Const n.0}` at
construction, so the goal holds before the run starts and the run fires nothing. Wall
time is at the floor: an empty process costs about 2.0 ms on this machine, so the
measurement bounds native's own work at roughly 1.1-1.6 ms and cannot resolve it
further.

**The rules encoding and egglog grow super-linearly, as a staircase rather than a smooth
curve.** At a fixed iteration count the node count is linear in n: 451, 857, 1 275 for
egglog at n = 7, 9, 11 is a line of slope 206, and 13 827, 19 685, 25 607, 34 508 at
n = 13, 15, 17, 20 is a line of slope 2 954. The super-linearity is entirely in the step
between those lines. Each time n forces the run to take one more iteration to connect
the two terms, the node count multiplies: 11x at the 3-to-4 step between n = 11 and
n = 13. Both engines step at the same width and to the same iteration counts, which is
expected, because the staircase is a property of the encoding and not of either engine.

A confirmation probe past the sweep's range finds the next step and finds it larger.
Regenerate it with `python3 gen-addac-sweep.py 24 28` and run each program once:

| n | egglog | ours, rules | ours, native |
|---|---|---|---|
| 24 | 46.8 ms / 46 376 / 4 | 40.0 ms / 50 822 / 4 | 5.9 ms / 93 / 1 |
| 28 | 1 983.7 ms / 1 580 627 / 5 | 1 192.9 ms / 1 766 096 / 5 | 6.0 ms / 109 / 1 |

The 4-to-5 step costs 34x the nodes and 30x the wall time for a 17% increase in width,
against native's 109 nodes and 6.0 ms. These two widths are single runs, not medians,
and are not in the CSV; they are reported to establish that the staircase continues and
steepens, not as timings.

**The verdict.** Native AC stays flat and the rules encoding does not, so the
convergence target's part (b) holds. The separation is 20x in nodes at n = 7 and 492x at
n = 20, and it is 16 200x at n = 28. The qualification the target's wording does not
carry is the shape: within the measured range the rules encoding's growth is a step
function of the iteration count, not the factorial curve the term "super-linear in the
sum width" suggests, and its wall-time separation from native (5.7x at n = 20) is far
smaller than its node separation because the wall times are close enough to the process
floor that the floor dominates. At n = 28, where the floor no longer dominates, the wall
separation is 199x.

## Protocol

Both engines are built in release mode and driven as separate processes, so the wall
time includes process start, parse, sortcheck, term construction, saturation, and the
statistics commands. Each pair runs 1 warmup then 5 timed runs; the tables report the
median. egglog runs `-j 1 --mode no-messages` and ours runs `--types machine`, which is
what puts `f64` in scope. This matches `run-pilot.py`.

Node counts are not measured the same way by the two engines, and the difference runs in
egglog's favour: their `print-size` reports table cardinality after rebuild, ours reports
stored nodes, and our totals include one node per distinct interned literal, which theirs
never count. `eqsat-basic.deviations.md` demonstrates this. The ~10% gap between the
egglog and ours-rules node columns at every n is that accounting difference, not a
difference in the search.

**A measurement trap, recorded because it silently erases the result.** Timing these
runs by passing `timeout=` to Python's `subprocess.run` destroys the signal. CPython
implements a bounded wait by polling with an exponentially backing-off sleep, so short
processes snap to the polling boundaries: measured that way every configuration in this
sweep reports a wall time drawn from 6, 12, 24, 48 ms, the native column stops being
flat, and the growth disappears into the quantization. `run-addac-sweep.py` therefore
passes `timeout=` only on the one bounded run that decides completion or DNF, and times
the recorded runs with a blocking wait. Anyone re-running this on a machine where the
programs are still this fast has to keep that split.

The sweep is also sensitive to load, because the wall times are small. An earlier pass
taken while another process held a core reported the same quantized 6/12/24/48 ms
sequence from load alone. Re-run it on an idle machine and cross-check that the native
column stays flat before reading anything else.

## Provenance

Our binary is a build of the working tree at c895265 with uncommitted modifications to
`egraph/src/ematch.rs` and `egraph/src/index.rs` from concurrent work, md5
`3ab419d2389b00289a9673ede3beace8`; egglog is 7b1adf2, md5
`9213d10fe3777cce331a6eba317e3945`. Our binary was rebuilt by that concurrent work
partway through the first pass, which moved the rules encoding's node count at n = 20
from 38 056 to 37 902: every number above comes from a single pinned copy of both
binaries taken after that rebuild. The node counts are deterministic across runs of a
fixed binary, verified at n = 20 over five runs.

## What this does not cover

One machine, no CPU pinning, no isolation from other load. Native AC only under the
naive strategy. The inline-goal shape, which is the original block's, is measured only
at n = 13 and only on egglog, because our language cannot express it. No extraction or
proof mode on either side.
