# Comparison methodology and divergence registry

The canonical account of every decision and divergence in the
egglog-vs-semi-persistent comparison, written for a PLDI submission and its
artifact evaluation. Rule: every future benchmark, translation, or harness
change that introduces a difference between the two systems adds a row
here, with the justification and the measured consequence. A divergence
that cannot be justified drops the benchmark; nothing is fudged.

## 1. Systems under test and pinning

- egglog: commit 7b1adf2 (egraphs-good/egglog), built `--release`.
  Registry dependencies vendored from static.crates.io because cargo
  could not reach index.crates.io here; procedure in comparison/README.md.
  **Toolchain deviation withdrawn 2026-08-16:** the earlier build used
  Rust 1.93.0 because the repo's pinned 1.91.0 was not installable on this
  machine. 1.91.0 is installed now, so the binary is built at the pinned
  toolchain and the deviation is gone. The rebuilt binary is 8.82 MB
  against 8.98, and reproduces the committed ledgers exactly: eqsat-basic
  11 nodes / 3 iterations, math-add-ac 1 939 / 7, addac-n7 451 — every
  figure identical to the published tables, which is the evidence that
  the toolchain change moved nothing observable.
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
  `(run 4)` — 81%. integer_math therefore ships as a **scoped column**,
  the same reduced program in all three configurations, and its timings
  are not comparable to anything upstream calls integer_math. Its
  `evals-to` relation is removed with no consequence (provably a no-op:
  every union it can perform is a node with itself); its five
  `is-not-zero`- or disequality-guarded rewrites are removed because we
  have neither relations nor guards, and keeping them unguarded would be
  unsound at zero; its three bitwise constant folds are removed for want
  of i64 bitwise primitives, at a measured cost of zero (0 matches, node
  count identical either way). Ledger: `integer_math.deviations.md`.
- **Interval-lattice functions stripped** (herbie, translated
  2026-08-16): the 2-function hi/lo lattice plus the `non-zero` relation
  it feeds — 32 forms, of which 12 are gated rewrites — and 5 constant
  folds over rational `pow`/`log`/`ceil`/`floor`/`round`, which our RBig
  primitive set lacks. Applied to the egglog program too. 163 of 180
  rewrites and 12 of 14 test blocks survive; the two dropped blocks were
  identified by running the stripped program and reading which checks
  failed, not by inspection, and both engines then agree on all twelve
  remaining checks. herbie is a **scoped column**. This supersedes the
  calc-substitution row below and the plan's closing claim that herbie is
  out of the intersection set: it is in, scoped. Ledger:
  `herbie.deviations.md`; `gen-herbie.py` regenerates it.
- **A datalog relation re-encoded as a constructor, on both sides**
  (until). Its generator rule is the benchmark — it is what `:until` has
  to cut short — so `(relation allgs (G))` becomes
  `(constructor allgs (G) U)` into an empty sort in all three
  configurations rather than being dropped. Consequence: a relation row
  becomes a node, so `allgs` now counts on both sides. Justified only
  because the same re-encoding is applied to the egglog program; a
  one-sided emulation would violate the intersection principle.
- **A-only native duals write their terms pre-flattened** (calc, until).
  Our `:assoc` does not flatten nested applications and does not collapse
  singletons, against the sequence normal form
  `ac-algebraic-properties.md` specifies (section 6 records the defect;
  `:assoc-comm` is correct). The native files therefore write every
  sequence in the flat form a correct implementation would have built,
  and state the singleton law `(rewrite (gmul x) x)` explicitly. Sound:
  the flat node is the one the nested text denotes, so when the defect is
  fixed the nested text reproduces these files unchanged. Same shape as
  the withdrawn literal-matcher workaround. Consequence: calc's blocks 1
  and 2 become true by canonization, which is the AC/A value proposition
  and not a weakened check — the same phenomenon as math-add-ac's native
  column saturating at 25 nodes in one iteration.
- **Two type groups compose on the command line** (herbie). It needs
  `RBig` from `bignum` and `String` from `machine`, and
  `--types machine,bignum` supplies both. Resolves the open note in
  README.md's protocol section that the `bignum` group has no `String`
  sort; no benchmark is untypeable for that reason.
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

**Three of the ten ranked intersection benchmarks are dropped, 2026-08-16,
on two missing pattern-language features.** Each has a ledger; none is
fudged into the set.

- **matrix** (ranked 7, mixed AC and A-only). Its subject is one
  conditional rewrite whose guard is an equality between two derived
  terms, `:when ((= (ncols A) (nrows C)) …)`. Expressing it needs a
  root-binding pattern form — egglog's `(= v (f x))` — which we do not
  have: our patterns are `(Op children…)` and cannot name a root, so two
  patterns cannot be required to share one. Both of the benchmark's
  assertions turn on that rule (the positive check derives through it and
  through nothing else; the `fail` check exists to show the guard blocks
  it), so removing it leaves fifteen unconditional rules and no
  assertions. `matrix.deviations.md`.
- **bdd** (ranked 9, commutative-without-associative). Six rules — the
  variable-ordering rules that make it a BDD — are guarded by a primitive
  comparison `:when ((< n m))`. A primitive operator may not appear in a
  left-hand side at all on our side. The guard is the rules' correctness
  condition, not a restriction: unguarded, both orderings fire and the
  ITE tree grows without bound, and the twelve checks assert exactly the
  canonicity the ordering buys. `bdd.deviations.md`.
- **eqsolve** (ranked 10, the set's only extraction-path benchmark).
  Three of its four rules desugar exactly by substituting the pattern for
  its root variable; the fourth needs both missing features at once — two
  patterns sharing a root class and a primitive divisibility guard. It is
  the rule that turns `3y = 12` into `y = 4`, so it produces the
  benchmark's output. Measured: removing it fails check 3 of 7 at the
  original `(run 5)`, and raising the budget to `(run 9)` to recover it
  does not terminate in 120 s, because the rule is also what keeps the
  search finite. `eqsolve.deviations.md`.

Consequence for coverage: the set loses its extraction-path column and
its A-only-operator column, and the honest scoping sentence for the paper
is that the comparison covers the intersection minus what two pattern
features would unlock. Both features are named in the ledgers: a
root-binding pattern form, and primitive predicates in `:when`.

**herbie's native-AC dual is deferred, not dropped**, and
`repro-herbie-vanilla` (ranked 4, 471 rewrites) behind it. The scoped
rules column ships and is validated; the dual needs a rule-by-rule pass
because nested same-operator patterns must be reshaped rather than
lifted — `(Mul (Mul a b) (Mul a b))` and `(Mul (Mul a a) (Mul b b))` are
the same multiset under AC, so that rule pair becomes a tautology and
must be deleted, and a mechanical n-ary lift would leave patterns that
silently match nothing. `herbie.deviations.md`.

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

- 2026-08-16, found while translating, not yet fixed (both in
  `egraph/src`, reported rather than changed because this pass owns
  `comparison/` only):
  - **`:assoc` does not flatten.** A nested application of an A-only
    operator stays a distinct node — `(seq (seq (Aa) (Bb)) (Cc))` and
    `(seq (Aa) (Bb) (Cc))` fail `(check (= …))` — and a one-element node
    is not collapsed to its element. `:assoc-comm` is correct on both
    counts, so only A-only operators are affected.
    `ac-algebraic-properties.md` lines 460 and 475 specify the flattened
    sequence as the normal form. Consequence: the calc and until native
    columns carry the pre-flattening workaround in section 4, and matrix
    would have needed it on operators whose whole role is re-association.
    Reproduction in `calc.deviations.md`.
  - **`A1-language-guide.md` line 149 documents a `:when` form that does
    not exist.** `(rewrite (Add x y) (Mul x y) :when ((= x zero)))` is
    given as the way globals appear in guards; `parse_rule_tags` reads
    `:when` as a list of `SurfacePattern` and sortcheck rejects `=` as an
    operator. Not a blocker for anything shipped — no translated
    benchmark needed it — but it is what made the matrix and eqsolve
    guards look expressible on a first reading.

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
