# Comparison methodology and divergence registry

The canonical account of every decision and divergence in the
egglog-vs-semi-persistent comparison, written for a PLDI submission and its
artifact evaluation. Rule: every future benchmark, translation, or harness
change that introduces a difference between the two systems adds a row
here, with the justification and the measured consequence. A divergence
that cannot be justified drops the benchmark; nothing is fudged.

## 1. Systems under test and pinning

- egglog: commit 7b1adf2 (egraphs-good/egglog), built `--release` with
  Rust 1.93.0 because the repo's pinned 1.91.0 was not installable on this
  machine (deviation, recorded; no behavioral difference observed against
  their own test suite). Registry dependencies vendored from
  static.crates.io because cargo could not reach index.crates.io here;
  procedure in comparison/README.md. Binary 8.98 MB.
- semi-persistent: branch egraph-wf at the commit each measurement names;
  the study landed engine fixes mid-flight (section 6), so every table
  states its binary's commit. Timed binaries are pinned copies under
  /tmp/addac-bin with recorded md5s where cross-agent rebuilds were a risk.
- Hardware: one Apple Silicon machine, single-threaded on both engines
  (`-j 1` for egglog; ours has no threading). Artifact note: record the
  exact machine model and OS build at final-run time; interim numbers were
  taken under occasional background load and the affected docs say which
  numbers are load-sensitive.

## 2. Timing protocol

Process-level wall clock over the release CLIs, N runs after warmups
(pilot: 10 after 2; sweep: 5 after 1), medians reported, all raw runs in
the CSVs. egglog run `--mode no-messages -j 1`; ours with default flags
and the strategy stated per table (naive is our shipped default; both
strategies reported where relevant). Machine-readable stats:
`print-stats :file` on both engines (ours since commit 5001280). Two traps
found and neutralized, kept here because artifact evaluators will hit
them: Python `subprocess.run(timeout=...)` quantizes millisecond timings
via its polling backoff (pass timeout only on DNF-deciding runs), and
concurrent builds on the same machine corrupt sub-10 ms medians (re-run
quiet, pin binaries).

## 3. Metric semantics divergences

- **Node counts are not comparable across engines.** egglog prints
  post-rebuild table cardinality (congruence-deduplicated rows); we count
  stored nodes, including nodes made duplicate by later congruence and one
  node per interned literal. Verified probe: after merging f(a) with f(b),
  egglog prints `f: 1`, we print `f: 2`. The bias favors egglog in any
  "smaller e-graph" reading; we therefore never claim node-count wins
  against them, only within-engine comparisons (rules vs native) where the
  counting is consistent.
- **Iteration semantics.** Their `(run N)` is at-most-N with early
  fixpoint stop; ours is the same (cap + early exit). Tables that fix N
  verified both engines actually ran the same iteration count.
- **`check` semantics.** Their `check` is a database query (facts may be
  non-constructive); ours builds the term then asserts `=`/`!=`. This is
  the reason for the goal-binding decision in section 4.

## 4. Translation decisions (with measured consequences)

Per-benchmark detail lives in `<name>.deviations.md`; the registry rows:

- **Goal terms bound as globals in all three configurations** (add-ac
  sweep). Left inline, egglog must *derive* the goal's nesting while our
  check *constructs* it: different problems, measured 461 ms vs 15 ms at
  n=13. Binding the goal is the only shape both engines express
  identically. Applies wherever a check's term is large.
- **Literal-op qualification.** Their bare `(+ x y)` becomes our
  sort-qualified `(IBig::+ x y)` / `(i64::+ x y)` per benchmark type
  profile. Pure renaming; no consequence.
- **Native-AC columns are "the same mathematics", not the same program.**
  Binary patterns are exact against flattened variadic nodes, so
  math-microbenchmark's native column restates eleven rules in n-ary
  rest-variable form. A rule-for-rule native translation would be strictly
  weaker (rules stop firing at arity 3+). Cross-checks verify the same
  equivalences hold in all configurations.
- **eqsat-basic native uses `:comm` only**, because the original has
  commutativity but no associativity rule; declaring AC would compare
  against a strictly stronger system.
- **Universe-relation boilerplate dropped** (integer_math, when
  translated): 13 rules that exist as egglog's groundedness workaround,
  not part of the problem; documented per file.
- **Interval-lattice functions stripped** (herbie family, when
  translated): the 2-function hi/lo lattice gates a minority of rules; the
  delta is documented and those rules are dropped on both sides or the
  benchmark column is scoped.
- **Ruleset default reading.** Our `(run N)` runs the default ruleset
  (untagged rules), egglog-style; the alternative (run everything) would
  let scoped AC rules fire in main runs and destroy the isolated add-ac
  experiment.
- **calc.egg substitutes for herbie.egg in the E6 macro exhibit.** Their
  `tests/web-demo/herbie.egg` needs `BigRat`, two `:merge` lattice functions
  and one relation, all outside the intersection set, and the analysis they
  support gates a large share of its 180 rewrites. `calc.egg` translates
  with two renamings and nothing else: `(datatype G)` with no variants
  becomes `(sort G)`, and identifiers outside our lexical class are renamed
  (`g*` -> `gmul`, `$X` -> `gX`). Measured consequence: none on cost, all
  four blocks run under 1 ms on both engines, which is the finding
  (comparison/semi-persistence/semi-persistence.md section 7).
- **E6 reports the minimum of the timed runs, not the median.** Its
  cost-per-cycle numbers are differences of two wall times whose delta is a
  fraction of either term, and this pass ran with a user application holding
  roughly half a core; a median of either term leaks that noise into the
  difference and produced negative per-cycle costs. The CSV keeps every run,
  so a median is recomputable. Applies only to E6.
- **E6's binaries are pinned copies, not a commit.** Another agent rebuilt
  the shared `target/` mid-sweep, so the tables were re-run against copies at
  recorded md5s; the doc states them and states that the first, mixed pass
  reproduces sections 3, 4 and 6 within 8%, which bounds what the in-flight
  engine changes could have moved.
- **Literal-matcher workaround, since withdrawn.** Six math-microbenchmark
  rules used let-bound globals while a matcher defect made LHS literals
  dead (section 6); after the fix, direct literals reproduce the
  workaround runs exactly (node counts to the digit; the 2-node delta is
  the dropped let commands). History kept in the ledger.

- **Class counts at truncated budgets are order-sensitive under
  incomplete closure.** The add_use prepend (use-list registration order
  reversed) leaves every saturating program byte-identical (congruence
  closure is confluent at a fixpoint) and nodes/match-steps identical
  everywhere, but math-microbenchmark's `(run 11)` stops mid-closure and
  its class count moves 507,992 -> 507,995 (+3, 6 ppm): the final round's
  rebuild had discharged three fewer pending merges when the budget
  expired. Both partitions are sound. Consequence: class counts on
  non-saturating programs are reported with this caveat, and final tables
  re-run at one pinned commit as already required.

## 5. Benchmark selection and exclusions

The intersection principle: both systems must express the problem without
emulation. Excluded and why: egglog's datalog relations, lattices/merges,
and containers (we lack them); their proof and term-encoding modes
(different system by their own architecture); their `scripts/bench.py`
production suite (all 12 programs are container/lattice/subsume workloads
- the paper must say our comparison covers their test corpus's eqsat core,
not their headline benchmarks); our unbounded arithmetic beyond i64 where
a benchmark needs their side to follow (herbie's BigRat is IN scope -
they have bigrat; our advantage claims there are about performance, not
expressiveness). Known-nondeterministic egglog programs (their
tests/files.rs list) are excluded from timing. Qualitative-only exhibits:
their multiset AC workarounds (eqsat-basic-multiset, factoring-multisets),
discussed but never timed head-to-head.

## 6. Engine changes landed during the study (provenance)

The study found and fixed defects in our engine; every number states
which side of each fix it was measured on:

- 165cc9f: LHS literals never matched (empty-lookup join scheduled first
  by a cost-1 estimate). Found by translation; fix verified by exact
  node-count equivalence against the workaround.
- 3f4e066 + successor (in flight at time of writing): order-dependent
  match-count discrepancy characterization and the planner selectivity
  constants (fixed-halving cost model vs measured fan-outs 2.51/1239;
  bad order was 95.3% of the rules-encoding run; counterfactual
  13.57 s -> 0.89 s). Post-fix numbers re-run the affected tables.
- Semi-naive access-path audit and hot-path locality audit in flight;
  their findings and any fixes append here.
- 2026-08-16, restore stopped rebuilding the hashcons index: the ten node
  caches and the literal interner delete the index entries of what the
  scope added instead of re-inserting every live entry, with the rebuild
  kept as a fallback above a quarter of the arena. E6's bare push/pop at
  S = 1e6 goes 12.38 ms -> 0.07 ms measured its way, 0.003 ms at 20 000
  pairs, and stops growing with S. Supersedes our columns in
  semi-persistence.md sections 3, 4 and 6 and retracts the no-asymptotic-
  separation claim in section 8; the addendum is section 11 and its runs
  are in semi-persistence-index-restore.csv. egglog re-run in the same
  session reproduces its published columns within 1%, so the pre-fix and
  post-fix tables in that file are comparable despite the rule above.

- 2026-08-16, the index build stopped writing its whole key space: the
  four index families build into a caller-owned span arena that outlives
  the map, so a build stamps a generation and writes only the keys its
  stream carries instead of a span table dense over the key space. At
  S = 1e6 the E6 round's index build goes 57.61 ms -> 32.64 ms and the
  delta index build 12.75 ms -> 1.38 ms; peak resident set size goes
  1 047.3 MiB -> 608.2 MiB. Matching costs 5% more, measured and
  reproducible, because a stamped span is 24 bytes against 16; the round
  total falls from 170.5 ms to 151.2 ms. Retracts the attribution in
  semi-persistence.md section 5 of the whole `(run 1)` cost to matching,
  and supersedes its "ours, naive" column; the addendum is section 12 and
  the diagnosis is span-table-sparsity.md. Corpus byte-identical on 26
  programs under both strategies and three scheduling modes.

Comparisons must never mix pre-fix and post-fix numbers in one table; the
final submission re-runs every table at one pinned commit.

## 7. Threats to validity

- One machine, one OS; no cross-platform replication yet.
- Wall-clock floors (~2 ms process startup) dominate small instances; the
  sweep reports node counts alongside for the asymptotic story, and the
  growth-shape qualification (staircase in iteration count within
  n=7..20, not a smooth curve) is stated where it applies.
- Our stats and their stats are computed by different code; both engines'
  reporting was cross-checked on small instances by hand.
- The two engines' costs concentrate in different places (their rebuild
  42% vs our 0.34% on math-microbenchmark; our matching vs theirs
  conversely): single-benchmark ratios do not generalize, which is why
  the set spans AC-dominated, mixed, and non-AC workloads.
- Author-implemented translations: mitigated by the deviation ledgers,
  the drop-don't-fudge rule, and cross-checks asserting the same
  equivalences in every configuration.

## 8. Maintenance rule

Every agent or author touching comparison/ re-reads this file first and
appends any new divergence with justification and consequence. The
deviation ledgers stay per-benchmark; this registry is the index a
reviewer reads.
