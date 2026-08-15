# AU solvers: bounds, ordering, hybrid, and the benchmark program

Plans the solver work that the crossover, certification, and rollout analyses
of 2026-08-15 motivate, and the benchmark program that measures it. It is a
work plan, not a status page: what is done is what the suites assert. The
findings this plan builds on are recorded in the crossover test's module doc,
the search-graph dump (`egraph/src/au/dump.rs`), and the anytime pilot
(`egraph/tests/au_anytime_bench.rs`).

## Standing facts the plan uses

- The exact solver minimizes lexicographic `(size, variant_mass)`; a variable
  costs `bs(l) + bs(r)`, the sizes of what it hides. It evaluates every
  action's children fully before comparing and prunes nothing.
- The projection identity
  `size(t) = size(proj_L) + size(proj_R) - #backbone` yields the admissible
  bound `LB(l, r) = bs(l) if l == r, else max(bs(l), bs(r)) + 1`. The inputs
  are the per-class snapshot fixpoint sizes, already stored per OR state
  (`space.rs:202-203`) and read today only by MCGS reward normalization.
- MCGS is deterministic. Its budget-1 answer is `initial_rollout`, a full
  greedy descent ranking actions by the exact cost of their laziest
  completion (`1 + sum of child bs pairs`). Expansion realizes one edge per
  playout in fixed index order; nothing is excluded and nothing is pruned.
- Certification is exhaustive: `Completion::Exact` requires every action of
  every reachable OR node realized, so the budget is `sum of A(v)`;
  the pilot's hardness filter selected instances where that sum is 1e4-1e6
  against a 4096 ladder, hence 0/263 certifications.
- Measured MCGS cost attribution (profiled on width d4w512 and ac m64c16):
  the full action-vector clone per expansion (`mcgs.rs:1753`) is 75-77% of
  playout runtime (removing it measures 4.3x at 4096 playouts); the
  first-empty-slot scan is refuted as a contributor at practical budgets
  (8.4e6 checks at p=4096, invisible in a 4300-sample profile) and only
  matters at certification-scale p close to A. The ac cliff at p=4096 was a
  separate quadratic defect in `close_completed_dag`'s postorder, which
  rebuilt the flattened child list per iteration; fixed with a regression
  canary, ac p=4096 from >6 min to 1.29 s at identical quality.

- The optimum can require suboptimal representatives. With
  `L = {k(k(k(p))), f(S, s1)}` and `R = {j(j(j(q))), f(S, s2)}`, `bs = 4` on
  both sides via the chains, which share no operator: the best combination
  of the optimal representatives is the bare variable at 8. Pairing the
  size-5 members yields `f(S_term, Variants(s1, s2))` at `1 + 3 + 2 = 6`.
  This is why actions range over the full member cross product rather than
  representative pairs, why the generalize value is only an upper bound, and
  why the projection bound is unaffected: a term's projections are some
  members of the classes, and `bs` floors all members.

## A. Algorithm work items

**A0. MCGS expansion cost: single-descriptor clone (and cursor at scale).**
Clone one action descriptor instead of the whole cached vector at expansion
(`mcgs.rs:1753`): measured 4.3x on width d4w512 at 4096 playouts (30.0 s to
7.0 s). The per-node cursor for the first-empty-slot scan is worthwhile only
for certification-scale budgets where p approaches A; implement it with the
same change but do not expect it to move the pilot numbers. The 1.7 GB pilot
peak was process-cumulative across ladders plus leaked guard workers, not a
per-run property; the anytime harness should recycle processes or subtract
leaked workers when reporting memory.
Done 2026-08-15: expansion clones only the selected descriptor, the initial
rollout reads the cache in place, and each OR node keeps a first-unrealized
cursor column restored with the other stats; width d4w512 at 4096 playouts
30.7 s to 7.8 s (4.0x, 1024: 8.0 s to 2.1 s), golden fixture unchanged.

**A1. The projection bound as a primitive.** `lb_pair(l, r)` beside
`static_generalize_quality`, plus a randomized test asserting the projection
identity on metamorphic terms. Days.
Done 2026-08-15: both helpers live in `egraph/src/au/estimates.rs` (moved
from mcgs.rs; the solvers import from there), and
`au_projection_bound.rs` pins the projection identity
`size = proj_L + proj_R - #backbone` and `size >= lb_pair` against the exact
solver's returned term on 200 seeded metamorphic instances; the differential
fixture is byte-identical.

**A2. Branch-and-bound in the exact solver.** Seed the incumbent with
generalize (already first), bound each action by
`1 + sum count * lb_pair(child)` before descending, skip on strict size
excess, and re-check with partial sums as child true values return.
Lexicographic care: prune only on strict size inequality, because an equal
size can still win on variant mass. Acceptance: crossover cycles=10 from
49.2 s to milliseconds; a differential flag runs pruned vs unpruned exact on
the metamorphic corpus and asserts equal qualities. About a week.
Done 2026-08-15 (`AuConfig::exact_pruning`, default false: the unpruned
search stays the default and is what the differential fixture pins): the
frame loop bounds each structural action by `1 + sum count * lb_pair` before
descending, re-checks with each solved child's true size substituted for its
bound, and bounds each AC representation pair by a min-cost flow over
`lb_pair` cell costs; every comparison is strict, size-only, and against the
node's own incumbent, so each memo entry stays the exact optimum of its
state. Flag off, the fixture is byte-identical; flag on, the exact qualities
equal the fixture's on all 211 corpus instances
(`au_differential.rs::pruned_exact_matches_reference`). Crossover cycles=10
completes in 0.19 ms at the measured optimum 39 against 49.2 s unpruned
(`au_scaling_crossover.rs::pruned_exact_crossover_c10`, release), and the
exact-only corpus drops from 65.7 ms to 31.7 ms release.

**A3. Best-first ordering and the anytime incumbent.** Sort actions by the
lazy-completion estimate (the MCGS rollout ranking) so good incumbents arrive
early and A2's pruning bites sooner; surface the incumbent on guard timeout
so exact degrades to anytime-with-proof-on-completion instead of
all-or-nothing. The remaining computation after the optimum is found is then
exactly the proof of optimality. Days, after A2.
Done 2026-08-15 (ordering and the anytime incumbent; A2's pruning is still
pending, so ordering is not yet expected to move runtime): exact sorts each
frame's structural actions by the lazy-completion estimate shared with the
MCGS initial rollout (`static_generalize_quality`), and
`AuConfig::exact_deadline` (default `None`) makes exact anytime — on expiry
it unwinds and returns the root incumbent as
`Completion::BudgetExhausted`, never claiming `Exact`. The differential
fixture is byte-identical (exact lines included), no tie-dependent
term-shape test needed adjustment, and the corpus release runtime is
unchanged (~0.9 s before and after), as expected without pruning;
`au_exact_anytime.rs` pins the deadline behavior on crossover cycles=8.

**A4. Memoize extracted terms per class.** Cache the interned minimal term
per class in the semi-persistent pool (restore truncates the cache with the
usual tokens); `build_best_term` becomes amortized O(1) after first build.
Acceptance: `au_deep_term_stress` depth-6000 from ~15 s debug to well under
a second; closes AU review perf item 5. 2-4 days.
Done: depth-6000 measures 0.16 s debug and 13 ms release (from ~15.5 s and
3.3 s); the differential fixture is unchanged, and a pool test pins that
restore truncates the cache with the term columns.

**A5. The bound inside MCGS.** Two sound uses. Dominance pruning at
expansion: an action whose bound strictly exceeds the node's generalize
value can never be optimal at that node, because the generalize value is
exact; drop it from `num_actions`. Closing: a node whose every action is
dominance-pruned closes without realization. Both shrink `sum of A(v)`, the
certification budget, and neither touches soundness because the comparison
is against an exact alternative, not an estimate. Note the honest limit: on
the width family the actions are genuinely under the generalize value, so
A(v) stays width^2 there; the win is on cycle-heavy and mutation-heavy
shapes. About a week.
Done 2026-08-15 (both uses; the closing rule needed no new code — it falls
out of the existing `num_actions == 0` terminal condition, and the
generalize seed is offered at every node-creation site): `dominance_pruning`
(`AuConfig`/`McgsConfig`, default false) drops, at OR-stats creation, every
structural action whose bound `1 + sum count * lb_pair(pair)` and every
transport descriptor whose lb-cost flow bound (A2's pre-screen, moved to
`estimates::transport_pair_lb` and shared with exact) strictly exceeds the
node's generalize value. Flag off, the fixture is byte-identical; flag on,
`au_differential.rs::dominant_pruned_mcgs_is_sound` moves 7 of 422 mcgs
lines, all certified-earlier at unchanged quality (xover c3..c6, both
budgets). Playouts to certification, flag off -> on: dump instance c3
(d2w2c3) 36 -> 3, xover c4 275 -> 5, c5 24801 -> 12, c6 uncertified at
2^20 -> 10; width d4w64 stays 16384, the honest limit above.

**A6. Context-independence subsumption in exact.** Track per OR state
whether any action was cycle-blocked, transitively through children; a
result untouched by blocking is context-free and memoizes on the bare
`(l, r)` pair. Acceptance: the c3 dump's 23 states collapse to 14; rand
stratum exact times drop. After A2, because A2 already neutralizes the
families where blocking is the only cost driver. About a week.
Done 2026-08-15, directly as the support-set tier (the blocked-nothing flag
alone is not simpler than the disjointness check, and the support is cheap
to collect from the frames): `context_subsumption` (`AuConfig`, default
false) marks a frame context-clean when every cycle-blocked structural
action's projection bound strictly exceeded the incumbent size (non-optimal
under every context, the A2 argument; without this exemption a cyclic
pair's self-re-entry action taints its whole subtree and nothing ever
memoizes), no transport cell was blocked, and every solved child was clean;
a clean completion memoizes its term plus the per-side support of the
winning derivation on the bare pair, and a later state on the same pair
reuses at entry iff the support is disjoint from both entry contexts
(argument on `exact::SubsumptionState`). Flag off, the fixture is
byte-identical; flag on, `subsumed_exact_matches_reference` pins the exact
qualities to the fixture on the full corpus, alone and combined with
`exact_pruning`. The c3 acceptance fell short of the prediction: 23 -> 19,
not 14 (`dump.rs::context_subsumption_collapses_c3_states`), because four
of the nine duplicate states are context variants nested inside the first
occurrence's own solve, entered while it is still `Visiting`, so no
completed result exists to reuse, and one is a duplicated terminal with no
children to save; A2 pruning removes those self-re-entry descents outright
and collapses the same instance to 6 states with or without subsumption.
At scale the reuse wins on its own
(`au_scaling_crossover.rs::subsumed_exact_crossover_c8_c10`, release,
Apple Silicon): exact times c8 788 ms -> 1.5 ms, c9 9.08 s -> 2.3 ms,
c10 TIMEOUT(30 s) -> 3.6 ms with subsumption alone, and 59/103/113 us at
c8/c9/c10 with both flags on.

**A7. Hybrid MCGS + exact below a threshold.** The consumer hook exists:
`results.mark_exact` already makes an OR node terminal for certification
(`mcgs.rs:1300`). Add exact entry at an arbitrary `(l, r, ctx)` (today it
assumes root entry with empty contexts), and a trigger: when a frontier
node's hardness estimate (reachable-pair count from the snapshot bitset, or
bs as a height proxy) falls under a threshold, run A2-exact with a budget
and mark the result. Proven values then propagate as closed subtrees, which
accelerates certification, and commitment-style variants become safe when
gated on certified children only. 1-2 weeks, after A0 and A2.

Order: A0, A1, A2, then A3 and A4 in parallel, then A5, A6, A7.

## Soundness arguments, per item

Every rule below compares against an exact quantity: a fixpoint size, the
generalize value, or a proven subproblem optimum. No rule compares against a
sampled estimate.

The standing gate for every item is `egraph/tests/au_differential.rs`, which
pins both solvers' outputs on a fixed corpus as a committed golden fixture
(`egraph/tests/au_golden/differential.txt`); its module doc states the
per-change protocol.

**A0.** No semantic content. The cloned vector is read at one index, so
cloning that descriptor is observationally identical. The cursor relies on
an existing invariant: expansion fills the first empty slot, so realized
slots form a prefix of the action indices and the first empty slot is a
counter. Determinism gives a total check: identical answers before and
after.

**A1.** The bound is a theorem over all AU terms for a pair, independent of
any search. `bs(c)` is the least fixpoint of the extraction recurrence,
hence the true minimum over ground member terms, not an incumbent. For
distinct classes every valid term contains a `Variants` node, because a
`Variants`-free term projects to itself on both sides and one term
inhabits one class, and distinct classes are disjoint. The identity
`size = proj_L + proj_R - backbone` with `proj_R >= backbone + #Variants`
forces `size >= bs(l) + 1`, symmetrically. The bound therefore holds at
every node under every context, and does not assume the projections are
optimal representatives (standing fact above).

**A2.** An action's value is `1 + sum count * V(child)` and
`V(child) >= LB(child)` under any context, because contexts only remove
candidates, so V is monotone non-decreasing in context. Discarding an
action whose bound strictly exceeds the node's incumbent size discards only
provably non-optimal actions, so the min over the survivors is unchanged.
Two guardrails: prune only on strict size excess, because an equal size can
still win on variant mass; and compare only against the node's own
incumbent, never a bound inherited from ancestors, so every memo entry
remains the exact optimum of its state and memo reuse stays valid.
Inherited alpha-beta bounds would make memo entries upper bounds and are
out of scope. Partial-sum tightening replaces a child's LB with its solved
value, which only raises a lower bound.

**A3.** Reordering permutes the operands of a min, and the min is
order-invariant, so the final value cannot change; ordering only moves when
the incumbent improves. The anytime return is sound because every incumbent
is feasible by construction (generalize is valid, and a composed action
term is valid because its children are valid inductively and projections
compose), and it is labeled uncertified: feasibility is the claim,
optimality only on completion.

**A4.** `build_best_term` is a deterministic pure function of the immutable
snapshot, and interning is idempotent, so the cache can only return the id
the computation would produce. The hazard is lifetime, not value: entries
must not outlive a restore that truncates the pool. Storing the cache in
the same semi-persistent storage, truncated by the same token bundle, makes
invalidation structurally identical to the pool's own.

**A5.** The comparison is against the generalize value, the exact value of
an always-available alternative. An action whose lower bound strictly
exceeds it loses under every completion, so removing it changes neither the
node's optimum nor any reachable best term. The certificate's claim becomes
"every action was realized or proven non-optimal", which is the same claim
exact-side pruning makes; cycle blocking already removes actions from
`num_actions`, so the certificate machinery handles filtered action sets. A
node whose every action is dominated closes at the generalize value, which
is then exact.

**A6.** Two tiers. Downward reuse: if a node solved under `ctx` had nothing
blocked anywhere in its derivation, its value equals the unconstrained
optimum `V(empty)`; for `ctx' subset of ctx`, monotonicity pins
`V(ctx')` between `V(empty)` and `V(ctx) = V(empty)`, so reuse is equality.
General reuse needs the support of the optimal derivation (the classes it
re-enters): reuse under `ctx'` iff the support is disjoint from `ctx'`,
because the stored term then survives unblocked (upper bound) while
monotonicity gives the lower bound. The blocked-nothing flag alone is sound
only for the downward case; implement the flag first, the support set if
the general case is measured to matter.

**A7.** Exact run on a frontier subproblem with that node's context and
cycle mode computes the identical quantity the MCGS certificate is defined
over, so `mark_exact` plus the value slots into backup and certification as
a truthful proven value. Term validity is independent of contexts (contexts
exist for termination of the search, not validity: any finite term whose
projections land in the classes is valid), so an exact-solved term is
always safe to offer; the write-once exact flag and `offer`'s
strict-improvement rule prevent silent degradation afterward.

For the benchmark program, soundness means the measurement supports the
claim: B1's knee prediction uses `sum of A(v)` computed by the dump,
independent of the measured run; B2 verifies the misranking per instance
against exact's ground truth instead of assuming it; B3 states its
selection rule and separates the zero-inflated gap mass from the mean among
nonzero gaps; B4's chain holds because the constructed oracle bounds
recoverable sharing from above, sort-checking rejects ill-typed formalizer
output before it reaches AU, and canonization-absorbed variability is
reported separately from search-recovered variability.

## B. Benchmark program

**B1. Grid v2: measurable certification.** Instrument `sum of A(v)` per
instance (the dump module computes it), select instances with the sum in
1e1-1e4, extend the playout ladder to 2^16, and report wall time beside
playouts because the initial rollout does per-node work comparable to exact
along one path. Falsifiable prediction to test: certification knees at
approximately `sum of A(v)` playouts.

**B2. The deceptive family.** Instances where the lazy-completion estimate
misranks actions: a decoy member pair whose children look cheaper by margin
m but cost more, and a true winner whose payoff is buried at depth d_b (a
shared subterm under d_b operators, differing at a mutated leaf). The
worked shape: decoy children ground-distinct (estimate equals true cost),
winner children factor through a shared chain (estimate exceeds true cost).
Knobs: d_b, m, decoy count, and mixing into the metamorphic corpus.
Prediction: playouts-to-gap-zero grows with d_b; greedy (budget 1) is wrong
on essentially all instances with m > 0. This family is what makes the
quality-vs-budget curve non-flat, since the pilot showed the symmetric
families are decided by depth-1 information.

**B3. The 1000-instance corpus.** Metamorphic generation with mixed
fresh/shared amplification plus deceptive injections; exact ground truth
under a guard (A2 raises the feasible hardness ceiling substantially);
deliverables per the standard methodology: quality profiles
(gap vs budget, means and quantiles, zero-inflation reported separately),
certification curves, primal integrals, and time-to-target plots against
exact's completion time, on both budget axes.

**B4. Auto-formalization variability benchmark.** The application story:
several LLM formalizations of one natural-language statement differ in
inessential structure; anti-unification extracts the stable core and places
the variation points optimally. The synthetic pipeline that keeps ground
truth while sounding like the application:

1. Sample ground-truth terms over application-shaped signatures (arithmetic,
   sets, logic; AC where the theory honestly is AC).
2. Generate K formalization variants per statement with variation operators
   modeling formalizer noise: AC reordering and unit insertion (absorbed by
   canonization, and reported as such), definitional unfolding via seeded
   rewrite rules, and genuine semantic drift as fresh-constant mutations.
   Construct the oracle lgg positionally as in the metamorphic suite.
3. Informalize: the signature becomes a glossary (operator and constant to
   controlled-vocabulary phrase with a one-line gloss); terms verbalize
   compositionally and deterministically; keep the term-to-text alignment.
4. Close the loop: an LLM formalizes the K statements against the glossary;
   sort-check rejects ill-typed outputs (`sortcheck.rs`); AU runs on the
   accepted terms; metrics are backbone precision and recall against the
   constructed oracle, variable-placement optimality (size vs oracle), and
   robustness as formalizer temperature and glossary ambiguity rise.

The validity chain is the point: the constructed oracle bounds recoverable
sharing from above, canonization-absorbed variability is reported as a
separate class from search-recovered variability, and the claim stays
"controlled-vocabulary natural language", not open-domain fidelity. Pilot at
50 statements x 5 variants with template verbalization and no LLM in the
generation loop; the LLM enters only as the formalizer under test.
