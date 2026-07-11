# AC Completion Performance: Investigation and Negative Results

Status: a record of completion-round performance work. One local optimization paid (the
per-round `nf_rules` hoist, ~4× on the convergent sweep, §5.4); the rest were rejected by
measurement (§5): the indexed normalizer (§6), a targeted-confirmation-round attempt that
turned out inert (§5.3), and merge-by-larger-use-list survivor selection, which was a wash on
convergent graphs and ~16 % slower on the diverging one (§5.6). The standing conclusion holds:
once the redundant per-pair clone is removed, the remaining cost is algorithmic at the round
level, so the next lever is scoping (when completion runs), not further inner-loop tuning (§6).
The algorithm and its correctness are unchanged throughout. Companion to
[ac-completion-review-debt.md](ac-completion-review-debt.md) (§1, the divergence budget)
and the design chapter (`../design/ac-congruence-completeness.md`).

## Addendum (2026-07-09): the destination-passing round landed, and two new observations

The "remaining per-round cost is algorithmic" conclusion above predates the adversarial
allocation pass (the 2026-07-09 Kapur-conformance series; retired plan in git history). What landed:
`NfRuleRef` borrowed rule views end the O(targets × rules) per-target deep clones in (A′)
(the §5.4 hoist only covered Bclose, and still cloned once per rule); all normalize calls
go through the `_into` forms with reused buffers; the (B) lcm/residual arithmetic is
destination-passing; the rule dedup is clone-free (sort + `dedup_by`);
`node_monomial_into` no longer allocates internally; flatten/materialize scratch is
hoisted. Combined-branch measurements on rule-heavy convergent workloads (vs. the
pre-conformance base, release): 4.5×–440×, dominated by the admissible-order fix
producing far smaller bases (one instance: 91 rounds/20k nodes → 44 rounds/2.7k nodes) —
the old tie-break minted guard-truncated junk rules.

Two operational observations from the same measurements: (i) the transition into the
doubly-exponential regime is razor-sharp (a few extra leaf merges took an instance from
0.2 s to >10 min); (ii) `MAX_COMPLETION_NODE_GROWTH` is checked **between** rounds, so a
single blown-up round (one measured round generated 2M critical pairs) burns unbounded
wall-time before the backstop triggers. An in-round budget check is the cheap fix and
feeds directly into the scoping lever (§6).

§2 to §4 below analyze the dominant term and the indexing idea that motivated attempt 3; §5
records the measurements; §6 explains why indexing backfired and what to do instead. Read §6
first if you only want the conclusion.

## 1. What we measured (and what is NOT the bottleneck)

A completion round was suspected of being non-optimal. Two hypotheses were tested by
paired before/after timing on the converging stress sweep
(`investigate_completion_sweep`) and reasoned against the diverging-graph trace
(`investigate_completion`, rules up to ~2000, `crit(B)` up to ~30k per round):

- **Per-pair `Vec` allocation (lcm/union/subtract reducts).** Converted to
  destination-passing and tried eliminating the `nf_rules` clone via a per-rule predicate
  closure. Result: ~40% **slower**, equal RSS. Reverted. Short-lived same-size `Vec`s are
  recycled by the allocator; the closure added per-iteration cost to the normalizer inner
  loop. Allocation per se is not the cost. (Distinct from the *hoist* in §5.4, which keeps
  the clone but does it once per round instead of once per pair — that one paid.)
- **Full-graph scan to find AC nodes.** Both per-round scan loops iterated
  `0..node_count()` and filtered with `is_mset`. Changed to iterate the AC node partition
  (`self.nodes.mset`) directly. Result: ~1% (within noise) on the AC-dense sweep, because
  these graphs have little non-AC majority to skip. Kept (it is a strict, correctness-
  preserving improvement and pays more on realistic mixed graphs), but it is not the
  bottleneck either. See §5.5.

## 2. The actual dominant term

`normalize` (`normalize_ms` / `normalize_with`) is called **twice per critical pair**
(both reducts) and **once per (A′) target**, and each call runs a fixpoint loop that, on
every rewrite step, **linearly scans all rules** testing `multiset_subset(rule.lhs,
current)`. Cost per round:

```
normalize cost  ≈  (2·crit(B) + targets) × rewrite_steps × rules × cost(multiset_subset)
```

With `crit(B)` ~30k and `rules` ~2000 on the diverging graph, the `× rules` factor is the
term that dominates the round. The lcm/union/subtract arithmetic is a small constant next
to it. A second, independent `O(rules²)` term is the `reducible[]` pass, which tests every
rule against every other for sub-multiset containment.

The brute-force scan asks "which rule LHS is `⊆ current`?" by trying every rule. But a rule
whose LHS is `⊆ current` must share **every** one of its child classes with `current`, so
only rules reachable through a child-class index can apply. The round already uses this
idea for the (B) partner search (`iter_uses` / `by_contains`); the normalizer and the
`reducible` check do not.

## 3. The shared index

Build, once per round, a rule-level child-class index:

```
by_contains[class] → sorted list of rule-ids whose LHS contains `class`
```

(The rule-set analogue of the matcher's node `by_contains`.) Three queries use it; they are
**not** the same set operation, and that distinction decides whether leapfrog applies.

### 3a. Collapse / reducibility: multi-way leapfrog intersection ✅

Rule `r` (LHS `A`) is reducible by rule `s` (LHS `B`) iff `B ⊆ A`. From `s`'s side: find
every rule whose LHS contains all of `B`'s classes. A rule contains class `c` iff it is in
`by_contains[c]`, so

```
containment-candidates(s) = ⋂_{c ∈ B} by_contains[c]      (intersection over B's classes)
```

That is exactly a leapfrog triejoin (worst-case-optimal multi-way sorted intersection), the
existing `LeapfrogJoin` engine. Then a cheap per-candidate check: `B`'s multiplicities ≤
`A`'s, and `B ≠ A`. This replaces the `O(rules²)` `reducible[]` pass and is the one query
where leapfrog is the principled fit.

### 3b. Overlap / superposition partners: k-way union (NOT leapfrog)

A superposition partner shares **≥1** class with `M`:

```
partners(M) = ⋃_{x ∈ M} by_contains[x]      (union, not intersection)
```

Leapfrog is the wrong operator: an intersection would demand sharing *every* class of `M`
and miss the overlapping-but-not-containing partners that §4b is about. This is a k-way
sorted merge with dedup, which the current `partner_buf` (collect + sort + dedup over
`iter_uses`) already is. Leapfrog buys nothing here; the win, if any, is only in using a
rule-level index instead of the node use-lists.

### 3c. Normalization candidates (LHS ⊆ M): union-generate, then verify

For normalizing `M`, an applicable rule has `B ⊆ M`. "Every class of `B` lies in `M`"
cannot be written as an intersection of fixed `by_contains` lists (each rule has a
different class set). It decomposes as:

1. **generate** `candidates = ⋃_{x ∈ M} by_contains[x]` (union: a subset must share a
   class), dedup;
2. **verify** each candidate with the full `multiset_subset(B, M)` test (a 2-way sorted
   merge walk).

This turns the inner scan from `O(rules)` to `O(candidates)`, where candidates ≈ the few
rules sharing a child with `M`. The verify is a 2-way merge (leapfrog's degenerate k=2
case); leapfrog's worst-case-optimality only matters at k ≥ 3, so a plain merge is optimal
for the verify itself.

## 4. Summary: where leapfrog fits

| query | set operation | leapfrog? |
|---|---|---|
| collapse / reducibility (`B ⊆ A`, find the `A`s) | intersection over `B`'s classes | **yes** (the natural fit) |
| superposition partners (share ≥1 class) | union over `M`'s classes | no (k-way merge) |
| normalize candidates (`B ⊆ M`, find the `B`s) | union over `M`'s classes, then per-candidate verify | no for generate; verify is k=2 |

So the biggest measured cost (normalization rescanning all rules, §2) is fixed by
**indexing + cheap per-candidate verify**, not by leapfrog itself. Leapfrog's distinctive
value lands on the collapse query (§3a). Both share the one per-round `by_contains` index.

## 5. Attempts and results

Optimizations implemented and measured paired (before/after, same sweep). The benchmark is
`investigate_completion_sweep` (10 convergent configs, release). Each result is the median of
≥2 runs; isolation was by a runtime toggle on one binary where possible (so the only variable
is the code path, not the build).

Rejected (recorded so they are not re-derived):

1. **Allocation removal (DPS + per-rule `applies`-closure clone elimination).** ~40% slower,
   equal RSS. Reverted (§1). Note this is *not* the per-round hoist below: it tried to drop
   the `nf_rules` clone entirely via a per-rule predicate closure, and the closure cost in the
   normalizer inner loop outweighed the saved clone.
2. **Indexed normalizer + indexed `reducible` (the §3 plan).** Built the per-round
   `lhs_contains` index; gathered normalize/reducibility candidates from it instead of
   scanning all rules. **Dramatically slower** on the large configs (the seed-999 sweep run
   did not finish in 6+ min vs ~137 s baseline); small/converging cases unaffected. Reverted.
   §6 explains why.
3. **RHS-shift delta (targeted confirmation round).** Hypothesis: the per-round full
   confirmation pass is wasteful because incremental rounds keep *falsely* converging — they
   miss critical pairs whose rule RHS shifted (the rule's own class merged, changing
   `min_monomial`/`atomic`, without its node being recanonicalized), so a full round has to recover
   them. Fix attempted: track those survivor classes in `fold_min_monomial` (`ac_rhs_shifted`) and
   fold the affected rule nodes into the incremental delta, so incremental rounds catch the
   shift directly and the full round runs only once at true convergence. Measured ON vs OFF on
   one binary (runtime toggle): **no effect.** Convergent sweep 1.62 s either way, round census
   byte-identical (66 rounds / 21 full), `crit`/`targets`/`nontrivial` identical. The diverging
   case (seed 42) likewise unchanged (81 rounds / 25 full, ~1.11 M crit, ~12.8 s either way).
   The premise was wrong: the full rounds on these benchmarks are the *structurally
   mandatory* ones (round 0, which legitimately generates every pair as the base case, plus the
   single final certifying round) — roughly two per config — not false-convergence triggers.
   There are no mid-completion false-convergence full rounds here for the delta enrichment to
   eliminate. The "full rounds = 54.6 % of all critical pairs" figure that motivated this
   conflated *round 0 generating all pairs (correct, unavoidable)* with *wasteful
   re-superposition (does not occur)*. The code was correct and cheap and preserved the
   completeness certificate exactly, but since it bought nothing measured it was **removed from
   the hot path** (the `ac_rhs_shifted` tracking in `fold_min_monomial` and the delta enrichment in
   `cc_round`); the incremental driver is back to the plain node-touch delta plus the
   full confirmation round. If a future incremental driver (S3b worklist) ever exhibits real
   mid-completion false-convergence, this is the fix to revive.
6. **Merge by larger use-list (parent-count survivor selection).** Hypothesis: choosing the
   merge survivor as the class with the *larger* parent use-list (instead of by union-find
   rank) leaves the *smaller* class to be absorbed and recanonicalized, so the post-merge
   `rebuild_congruence` re-canonicalizes fewer parents. Implemented as `union_directed` /
   `merge_directed` plus an O(1) `ListArena::len` (a count cached in the list header,
   maintained on `append`/`splice`, semi-persistent like the rest of the header), toggled by
   `MERGE_BY_USES`. Measured ON vs OFF on one binary: **no help, slightly worse.** Convergent
   sweep a wash (~2.55 s either way); the diverging pathological case (seed 42) consistently
   ~16 % *slower* (≈19.7 s → ≈22.8 s). Reasons: (a) the post-merge recanonicalization cost is
   not the round bottleneck — `Bclose` is (§2), and survivor choice does not change the
   critical-pair count; (b) forcing the survivor against rank gives up union-by-rank's height
   optimality, so `find` climbs slower trees, and `find` is on the hot path of every multiset
   canonicalization; (c) it changes which intermediate monomial nodes get materialized, which
   on the diverging graph nudges the basis onto a slightly larger trajectory (8382 → 8588 AC
   nodes at the backstop). It was sound (the leaf equivalence relation was verified identical
   under both policies before removal), but since it did not pay, the `merge_by_uses` flag and
   the wiring at the two rebuild merge sites were **removed**; rebuild is back to plain
   rank-based `merge`. What was **kept** is the reusable infrastructure that has value
   independent of the heuristic: `ListArena::len` (O(1) cached count, semi-persistent), and the
   `UnionFind::union_directed` / `EClasses::merge_directed` primitives (forced-survivor union,
   covered by their own unit tests). They cost nothing when unused and are the building blocks
   for any future survivor-selection policy.

Accepted:

4. **Per-round `nf_rules` hoist.** The (B) close loop normalizes both reducts of every
   critical pair against the rule set. The rule set is identical for every pair in the round,
   but it was being rebuilt (one `NfRule` clone per rule) *inside* the per-pair loop — the
   `O(crit × rules)` clone term §2 names as the dominant `Bclose` cost. Building it once,
   outside the loop, removes that term without changing any work *count*. Paired measurement
   on the convergent sweep: **6.7 s → 1.63 s (~4×)**, identical node counts, byte-identical
   round census and `crit`/`targets`/`nontrivial` counters (the signature of a pure
   per-iteration-cost win: same work, less time). A cheap raw-equality pre-check (`r1 == r2`
   skips the two normalizations for an already-coincident pair) rides along in the same change.
   This is the one local optimization that paid, and it is consistent with §2: the cost was a
   *clone repeated per pair*, which is not the same as the irreducible subset-test count §6 is
   about.
5. **Iterate the AC node partition instead of all nodes.** ~1 % (within noise) on these
   AC-dense graphs, because they have little non-AC majority to skip. Kept anyway: it is a
   strict, correctness-preserving improvement that drops the two per-round scans from
   `O(total nodes)` to `O(AC nodes)`, which pays on realistic mixed graphs where most nodes
   are not AC. Not a bottleneck on this benchmark.

## 6. Why indexing backfired, and what it means

The §3 plan assumed "few rules share a child class", so a child-class index would prune the
candidate set. **That assumption is false for exactly this workload.** AC completion
diverges *because* the rules are densely connected by shared child classes (overlapping
pure-sum classes are what generate the critical pairs, AC spec §3.3). So for a common class
`c`, `lhs_contains[c]` lists most rules, and the union over a monomial's classes is ≈ the
whole rule set. The index then adds cost (HashMap lookups, stamp-array writes, candidate
`Vec` pushes) **on top of** still testing nearly every rule. Net loss, growing with rule
count, which is why only the large configs showed it.

The deeper lesson across the attempts: the round's cost is not allocation, not the node
scan, and not "we test too many rules per normalize step" in a way *indexing* can fix. It is
that there are genuinely `O(crit × rules)` (rule, monomial) subset tests because the basis is
large and dense (AC spec §3.3: the divergence is genuine canonical-basis growth on a
pathological input). Indexing the inner test does not change that the inner-test count is
intrinsically large on the diverging graph; on the converging graphs the round is already
cheap.

One important qualification, learned from §5.4: there *was* one local win, but it was not in
the inner *test* — it was a per-pair *clone of the rule set* sitting redundantly inside the
critical-pair loop. Hoisting it out (build the `NfRule` set once per round, not once per
pair) cut the convergent sweep ~4× with byte-identical work counts. The distinction matters:
that clone was `O(crit × rules)` *work the algorithm never needed to repeat*, whereas the
`O(crit × rules)` subset *tests* §3 targeted are work it genuinely must do. Indexing attacks
the latter and loses (the candidate set is ≈ all rules on a dense graph); hoisting removes
pure redundancy and wins. After the hoist, the remaining per-round cost really is the
irreducible subset-test count, and no further local optimization on this benchmark has paid.

The levers that reduce the *irreducible* work are algorithmic at the round/driver level, not
the inner loop:

- **Scope completion so it never runs on the pathological dense case** (the growth guard /
  on-demand / degree-bound options in plan §0.5). The real answer: do not pay the
  `O(crit × rules)` cost at all when the basis is exploding.
- **Incremental driver (S3b worklist, plan §9a):** process only the delta each round instead
  of re-deriving and re-superposing the whole rule set. This changes *what work is done*, so
  it can pay where indexing cannot.

Conclusion: after the one redundant-clone hoist (§5.4), stop micro-optimizing the completion
round. The remaining performance question is the same as the on-by-default question (plan
§0.5), and the answer is scoping, not further inner-loop tuning.
