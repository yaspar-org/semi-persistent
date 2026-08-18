# Comparison methodology and divergence registry

The canonical account of every decision and divergence in the
egglog-vs-semi-persistent comparison, written for a PLDI submission and its
artifact evaluation. Rule: every future benchmark, translation, or harness
change that introduces a difference between the two systems adds a row
here, with the justification and the measured consequence. A divergence
that cannot be justified drops the benchmark; nothing is fudged.

Two status words, used with these meanings everywhere in comparison/:
**dropped** means out of the comparison, with the reason recorded;
**postponed** means blocked on a measured cost, with the condition that
revives it stated. Three encoding words, by role: the **native encoding**
is the program style (A/C carried by operator declarations), a **native
column** is that encoding's slot in a table, and a benchmark's **native
dual** is the translated counterpart file itself.

## 1. Systems under test and pinning

- egglog: commit 7b1adf2 (egraphs-good/egglog), built `--release` at its
  pinned Rust 1.91.0, checkout at `~/tools/egglog`. Nothing in this study
  lives under /tmp, because the operating system reaps files there by
  access age. Registry dependencies vendored from static.crates.io because
  cargo could not reach index.crates.io here; procedure in
  comparison/README.md. The pinned-toolchain binary is 8.82 MB and
  reproduces the committed ledgers exactly (eqsat-basic 11 nodes / 3
  iterations, math-add-ac 1 939 / 7, addac-n7 451).
- semi-persistent: branch egraph-wf at the commit each campaign's pinning
  block names; the study landed engine fixes mid-flight (section 6), so
  every table states its binary's commit. E6's tables were timed against
  pinned binary copies with recorded md5s because concurrent rebuilds were
  a risk during that experiment; the E6 doc states them.
- Hardware: one Apple Silicon machine, single-threaded on both engines
  (`-j 1` for egglog; ours has no threading). The exact machine model, OS
  build, binary md5s and measured load are recorded in section 9, which the
  earlier artifact note asked for and which the final campaign supplies;
  interim numbers were taken under occasional background load and the
  affected docs say which numbers are load-sensitive.

## 2. Timing protocol

Process-level wall clock over the release CLIs, N runs after warmups
(campaigns: 10 after 2; sweeps: 5 after 1), medians reported, all raw runs in
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
- **Multi-block programs report neither metric comparably.** On any
  benchmark whose work happens inside `push`/`run`/`check`/`pop` blocks
  (`calc`, `until`, `herbie`), the node count printed at the end is the
  base state after the last `(pop)` and reflects none of the work; and
  egglog's stats file accumulates one entry per iteration across every
  `(run …)` in the program while ours reports the last `(run …)` only
  (herbie: 24 against 1). Wall time is the metric for these three, and
  their node and iteration columns are reported only to show the runs
  happened.
- **Goal-terminated runs have no stable node count.** `until` halts on a
  `:until` goal while a non-terminating rule generates, so the size at
  the moment the goal is noticed depends on engine, encoding and
  saturation strategy: 52 nodes naive against 75 semi-naive in the same
  encoding, both correct. Stronger form of the truncated-budget caveat
  below; that benchmark's node column is not an e-graph size comparison.

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
- **Universe-relation boilerplate dropped** (integer_math, translated
  2026-08-16): 13 rules that exist as egglog's groundedness workaround.
  Larger than anticipated: two of the rules driven by `MathU` introduce an
  `Add`-with-zero and a `Mul`-with-one for every node, and are what makes
  the benchmark grow, so the strip takes term nodes from 537 to 100 at
  `(run 4)`, an 81% reduction. integer_math therefore ships as a **scoped column**,
  the same reduced program in all three configurations, and its timings
  are not comparable to anything upstream calls integer_math. Its
  `evals-to` relation is removed with no consequence (provably a no-op:
  every union it can perform is a node with itself); its five
  `is-not-zero`- or disequality-guarded rewrites are removed because we
  have neither relations nor guards, and keeping them unguarded would be
  unsound at zero; its three bitwise constant folds are removed for want
  of i64 bitwise primitives, at a measured cost of zero (0 matches, node
  count identical either way). Ledger: `integer_math.deviations.md`.
- **Interval-lattice functions stripped** (herbie): the 2-function hi/lo
  lattice plus the `non-zero` relation it feeds (32 forms, of which 12 are
  gated rewrites), and 5 constant folds over rational
  `pow`/`log`/`ceil`/`floor`/`round`, which our RBig primitive set lacks.
  Applied to the egglog program too. 163 of 180 rewrites and 12 of 14 test
  blocks survive; the two dropped blocks were identified by running the
  stripped program and reading which checks failed, not by inspection, and
  both engines agree on all twelve remaining checks. herbie is a **scoped
  column**. Ledger: `herbie.deviations.md`; `gen-herbie.py` regenerates
  the egglog and rules programs.
- **A datalog relation re-encoded as a constructor, on both sides**
  (until). Its generator rule is the benchmark, the thing `:until` has
  to cut short, so `(relation allgs (G))` becomes
  `(constructor allgs (G) U)` into an empty sort in all three
  configurations rather than being dropped. Consequence: a relation row
  becomes a node, so `allgs` now counts on both sides. Justified only
  because the same re-encoding is applied to the egglog program; a
  one-sided emulation would violate the intersection principle.
- **Two type groups compose on the command line** (herbie). It needs
  `RBig` from `bignum` and `String` from `machine`, and
  `--types machine,bignum` supplies both; no benchmark is untypeable for
  a missing sort.
- **Ruleset default reading.** Our `(run N)` runs the default ruleset
  (untagged rules), egglog-style; the alternative (run everything) would
  let scoped AC rules fire in main runs and destroy the isolated add-ac
  experiment.
- **calc.egg is the E6 macro exhibit.** herbie's blocks all run under
  1 ms on both engines, so E6 exhibits multi-block push/pop on `calc.egg`,
  which translates with two renamings and nothing else: `(datatype G)` with no variants
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
- **Node and class counts at truncated budgets are order-sensitive under
  incomplete closure.** A run stopped at a budget before saturation ends
  wherever the match order put it, so any change that reorders matching
  moves those counts without changing what the run concludes. Measured at
  two amplitudes: the add_use prepend moved math-microbenchmark's class
  count 507 992 -> 507 995 (+3, 6 ppm) with every saturating program
  byte-identical; a window of about twenty ematch and scheduling commits
  moved math-add-ac's rules encoding 3 256 nodes -> 3 317 (1.9%), with
  the egglog column unchanged at 1 939 nodes / 7 iterations. Counts are
  deterministic at any one commit (repeated runs agree), which is why
  campaigns pin one commit. Counts on non-saturating programs carry this
  caveat wherever they appear; figures from other commits are marked in
  `math-add-ac.deviations.md` as not to be cited.

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

Per-benchmark notes on the selections that carry conditions:

- **matrix** (ranked 7, mixed AC and A-only). Its conditional Kron/MMul
  rewrite guards on an equality between two derived terms, written
  `:when ((= p (ncols a)) (= p (nrows c)) ...)`: each conjunct binds one
  pattern's root e-class, and the repeated variable requires the two to be
  one class. Both assertions pass. Two native configurations ship:
  `matrix.native.egg` with native AC on `Times`, and `matrix.native-A.egg`
  adding native A on `MMul` and `Kron`, which is the A-only half the
  benchmark was selected for. `matrix.deviations.md`.
- **bdd** (ranked 9, commutative-without-associative). The six
  variable-ordering rules keep their guard, written `:when ((i64::< n m))`
  over the two i64 labels the `ITE` patterns bind. Twelve checks pass in
  all three configurations. `bdd.deviations.md`.
- **eqsolve** (ranked 10, the set's only extraction-path benchmark). Two
  adjustments apply to every configuration, and both engines take them:
  the budget is 6 rather than 5, because at 5 our engine has not joined
  `(Var "x")` to `(Num 5)` while all seven original checks already pass;
  and the three extracted answers are asserted rather than only printed.
  The native encoding is validated under `--lazy-ac-eqs` (all ten checks,
  one 484 s run) and excluded from timed tables on that cost; the rules
  encoding's gap to egglog is e-matching volume, measured at 2.74 M match
  steps on 9.6 k nodes with extraction contributing nothing measurable.
  `eqsolve.deviations.md`.
- **herbie** (ranked 3, scoped). Both encodings ship and are timed; the
  native program is hand-derived because nested same-operator patterns
  must be reshaped rather than lifted (a rule pair whose two sides
  flatten to one multiset is contentless and is deleted, not restated).
  `repro-herbie-vanilla` (ranked 4) is dropped: at the pinned commit it
  is a typed-lowering unsoundness reproduction with no checks, not a
  benchmark. `herbie.deviations.md`,
  `repro-herbie-vanilla.deviations.md`.

Coverage, as the paper states it: the comparison covers the seventeen-benchmark
set (the ranked ten-benchmark intersection plus seven second-pass
additions). Every ranked-intersection benchmark has rules and native
encodings timed except eqsolve, whose native encoding is validated and
excluded from timed tables on its measured completion cost; of the seven
additions, acgen has both encodings and the other six (combinators,
resolution, typecheck, knapsack, levenshtein-distance, intersection) ship
rules-only. Selection conditions for the additions and for the BLOCKED
carriers (array, subsume) are in `comparison/README.md`; their
per-benchmark notes live in the `*.deviations.md` ledgers.

## 6. Engine changes landed during the study (provenance)

The study found and fixed defects in our engine; every number states
which side of each fix it was measured on:

- 165cc9f: LHS literals never matched (empty-lookup join scheduled first
  by a cost-1 estimate). Found by translation; fix verified by exact
  node-count equivalence against the workaround.
- 3f4e066 + 16ddfea: order-dependent match sets fixed by snapshot
  canonicalization, then the planner selectivity constants replaced the
  fixed-halving cost model with measured fan-outs (2.51/1239; the bad
  join order was 95.3% of the rules-encoding run; 13.57 s -> 0.89 s).
  Post-fix numbers re-ran the affected tables.
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

- 2026-08-16, found while translating; both fixed 2026-08-17, and both
  entries are kept so that the pilot's first published numbers stay
  attributable:
  - **Fixed 2026-08-17 in e998295: `:assoc` did not flatten.** A nested
    application of an A-only operator stayed a distinct node and a
    one-element node was not collapsed to its element; `:assoc-comm` was
    correct on both counts. The calc and until native columns no longer
    carry the pre-flattening workaround. Reproduction, and the record of
    what the workaround was, in `calc.deviations.md`.
  - **Fixed 2026-08-17 in 93d698d: `A1-language-guide.md` line 149
    documented a `:when` form that did not exist.**
    `(rewrite (Add x y) (Mul x y) :when ((= x zero)))` was given as the
    way globals appear in guards, and sortcheck rejected `=` as an
    operator. It is the root-binding form, with a global on one side, and
    it now resolves to the O(1) equality check the guide describes. This
    is what made the matrix and eqsolve guards look expressible on a
    first reading, and they now are.

- 2026-08-17, found while translating matrix's A-only native dual,
  **fixed the same day**: a variadic expansion unbound variables it had
  not bound. With `MMul` and `Kron` declared `:assoc` and the eight
  matrix rules that mention them restated n-ary, the guarded Kron/MMul
  rewrite drove `ematch.rs:229` to read an unbound variable through an
  `IndexLookup::ByRepr`. The cause: `ExpandA` checks a fixed child whose
  variable an earlier atom already bound, but its cleanup cleared every
  local child, including the checked ones. The panic is the milder
  symptom. The other is silent: the next window rebound the cleared
  variable from its own children instead of checking it, which erases the
  constraint the earlier atom carried, so the guarded rewrite fused
  Kronecker products whose dimensions do not line up. Fixed by recording
  which variables each binding pass bound and clearing exactly those, in
  both matcher engines and in all three decompositions; `ematch.rs`'s
  `expand_a_checks_a_prebound_fixed_child` and the two `a_prebound`
  fixtures in `egraph/tests/egg/` are the fences.

  **The campaign numbers are unaffected, verified rather than argued.**
  No committed benchmark program reaches the pattern: all 32 programs in
  this directory produce byte-identical output before and after the fix,
  under both strategies and all three scheduling modes, and again under
  the default type groups. The program that does reach it was never a
  committed column: it is the A-only draft this entry was written about,
  now validated and shipped as `matrix.native-A.egg` with counts in
  `matrix.deviations.md`, measured after the fix and carrying no timing
  in the section 9 campaign, which predates it.

  **Why the differential oracle did not catch it.** `match_keys` runs
  every query through three engines and asserts they agree, but the push
  and pull engines carried the same defect, so on the minimal case
  (`expand_a_prebound_child_oracle_blind_spot`) all three agreed on the
  same wrong answer: three matches where the constraint admits one. An
  agreement between two implementations of one mistake is not evidence;
  the test that fails pre-fix is the one asserting the match set against
  the pattern's meaning, not against another engine.

Comparisons must never mix pre-fix and post-fix numbers in one table; the
final submission re-runs every table at one pinned commit.

- 2026-08-17, semi-naive class-growth blindness: a merge whose surviving
  representative is the id the parents already store recanonicalizes
  nothing, so a match created purely by class-membership growth reached
  no delta, and which union direction occurred decided whether the rule
  fired. Found by the herbie native encoding (block 9, 11/12), reduced
  to two four-line reproductions, fixed in two halves: merges under
  semi-naive record the absorbed class's members in the touched log, and
  rules referencing a let-bound global in a child or element position
  match the whole graph every round. herbie native semi-naive is 12/12;
  the corpus passes both strategies; semi-naive counts on budget-capped
  programs moved (eqsolve.rules 9085 -> 9398,
  math-microbenchmark.rules 1 254 903 -> 1 248 629) because the strategy
  now derives per round what it missed. Pre-fix semi-naive counts on
  capped programs are not complete derivations and are not cited.

- 2026-08-18, integer-to-rational lift: RBig::from_int / RBig::scale /
  RBig::pow in the mixed literal model (exact, checked), making herbie's
  multiplicity variants k-generic; the ledger's residual list is the
  parity-shaped cases only. Twelve checks pass both strategies, counts
  unchanged. Fixture rbig_mult_lift.egg pins multiplicity 3.

- 2026-08-18, merge survivor policy (--union-by): directed merges on
  verified per-class counters (member count with the new W7 accuracy
  clause in the kernel's wf; use-list length already verified). All four
  policies pass every check on the corpus; node counts move only within
  the documented order-sensitivity class. math-microbenchmark rules-semi
  drops 1.69 s (rank) to 0.60 s (size/uses/sum) with complete
  derivation, which prices the class-growth delta the 2026-08-17 fix
  maintains; campaigns run under the default (rank) unless a table says
  otherwise.

- 2026-08-17, RHS multiplicity expressions: RHS elements of a variadic
  operator take checked u64 expressions over bound multiplicities
  (`(Add b ..s):(u64::- k 1)`), interval-checked at rule install against
  the LHS constraints (a possible underflow or zero divisor is a compile
  error) with multiplicity 0 omitting the element. This makes the
  keep-k-1-copies multiplicity variant expressible: the distributivity
  variants are in `integer_math.native` (plus its LShift rule) and
  `math-microbenchmark.native`, counts identical to the campaign under
  both strategies (they fire zero times on the shipped workloads).
  Fixtures `rhs_mult_expr.egg` / `rhs_mult_expr_underflow.egg`.

- 2026-08-17, multiplicity variants: AC matching is a partition of
  distinct children (an element takes its child's whole multiplicity;
  unannotated, that multiplicity must be exactly 1), so the n-ary lift of
  a binary rule cannot match a repeated child (`Mul{t : 2}` unmatched by
  two-element patterns, `Add{0 : 2}` unmatched by a bare identity
  element) and each such rule carries a multiplicity variant covering
  multiplicity 2 or more. This is the intended semantics, not a matcher
  defect. The engine reads a bound multiplicity variable on the RHS in
  i64 positions, and `i64::pow` exists, which is what k-generic variants
  need. The variants are hand-written in `integer_math.native`,
  `math-microbenchmark.native` and both `matrix` native files
  (per-benchmark ledgers). Every count is identical to the campaign
  tables under both strategies: the variants fire zero times on the
  shipped workloads. Fixtures `ac_multiplicity_variant_gap.egg` /
  `ac_multiplicity_variant.egg` pin the base-rule gap and the variants.

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

## 9. Campaign records

A campaign is one timed pass over the whole set at one pinned commit of
each engine, on one quiet machine, with the hardware recorded. Each
campaign file in `final/` carries its own pinning block; the current
campaign is `final/final-r4-tables.md`, and r1 (`final-tables.md`), r2
(`final-r2-tables.md`) and r3 (`final-r3-tables.md`) are archived records whose raw CSVs stay cited by
ledgers and experiment write-ups. The r1 campaign's pinning block follows,
because it is the fullest record (machine, load, binary md5s) and the r2
and r3 blocks refer to it for the machine.

- **Pinned commit** c25fb2547b69fbfa0c5172ccf0e32c3ec637fbc6, branch
  egraph-wf, clean tree.
- **Machine** Apple M4 Pro, model identifier Mac16,8, 14 cores, 48 GiB,
  macOS 26.6.1 build 25G76. One machine, so section 7's no-cross-platform-
  replication threat stands.
- **Load** one-minute average 1.71 at the start and 1.77 at the end, verified
  below 2 before starting. A process left by an earlier session was holding a
  core: the `eqsolve --derive-ac-eqs` probe section 5 records as
  non-terminating, 54 minutes in, reading an input file no longer in the tree.
  It was killed before the campaign and the machine was otherwise idle, so no
  load qualification applies to these numbers.
- **Our binary** `cargo build --release` at the pinned tip on the repo's
  pinned Rust 1.97.1: 5 635 968 bytes, md5 80926a7fca2987f9afd3d1db9cfc4fb6.
- **egglog binary** commit 7b1adf249c918226871b9b3d5e8f089585e46e99 built at
  its pinned Rust 1.91.0: 9 247 232 bytes, md5
  f16c4c42abd2d24b360f48a345126a89. Not rebuilt, because it reproduces
  addac-n7 at 451 nodes and 3 iterations, which is the check section 1
  records for the toolchain-deviation withdrawal.
- **Protocol** 2 warmups and 10 timed runs per configuration, medians
  reported, all 460 runs kept. Ten benchmarks in 46 configurations, invoked
  one benchmark per process so that a failure would lose one benchmark and
  not the campaign; all ten succeeded.
- **Process startup measured, not assumed.** An empty program costs 2.88 ms
  on our binary and 3.58 ms on egglog's. Section 7 estimated this at about
  2 ms; the measured value is what `final-tables.md` uses to separate the
  four benchmarks whose ratios are startup-dominated from the six that
  measure throughput, and the paper should quote the restricted median.

Every configuration reproduced the node, class and iteration counts its
committed ledger records, to the digit, with one exception: math-add-ac's
rules encoding, whose movement and cause are the widened entry in section 4.
That exception is why this campaign exists, so it is a confirmation of the
rule rather than a defect.

**AU corpus, partially re-confirmed.** The committed curve tables regenerate
exactly from the committed `au/corpus.csv` through `au/analyze.py`, so the doc
is consistent with its data. Re-measuring the engine at the pin under a
reduced wall budget (`AU_CORPUS_SECS=360`, writing to a scratch directory)
covered 152 of the 673 instances and 2 280 of the 10 095 rows, with no exact
timeout, no MCGS timeout and no ladder cut, matching the committed run's
conditions. Every quality field agrees with the committed corpus on all 2 280
rows, and the headline statistics restricted to those 152 instances are
identical in both: zero fraction 0.513 at one playout and 0.836 at 2^14,
certified fraction 0.000 and 0.382, mean gap 0.0829 and 0.0152. One instance
disagrees on two census fields, xover-14 at `sum_a` 38 994 295 -> 39 212 064
and `or_states` 3 973 120 -> 4 000 000: it is census-capped in both runs and
is one of the 38 capped instances `anytime-corpus.md` already excludes from
the knee analysis because their `sum A(v)` is a lower bound, so the value
depends on where the traversal stopped and no headline number reads it.
Carried without re-measurement: the remaining 521 instances of the main run,
the full-corpus figures those 673 instances produce (zero fraction 0.290 to
0.798, certified fraction 0.193 at 2^14), and the entire deep-ladder run of
table (e).
