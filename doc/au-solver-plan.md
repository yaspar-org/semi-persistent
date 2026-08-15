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

**A1. The projection bound as a primitive.** `lb_pair(l, r)` beside
`static_generalize_quality`, plus a randomized test asserting the projection
identity on metamorphic terms. Days.

**A2. Branch-and-bound in the exact solver.** Seed the incumbent with
generalize (already first), bound each action by
`1 + sum count * lb_pair(child)` before descending, skip on strict size
excess, and re-check with partial sums as child true values return.
Lexicographic care: prune only on strict size inequality, because an equal
size can still win on variant mass. Acceptance: crossover cycles=10 from
49.2 s to milliseconds; a differential flag runs pruned vs unpruned exact on
the metamorphic corpus and asserts equal qualities. About a week.

**A3. Best-first ordering and the anytime incumbent.** Sort actions by the
lazy-completion estimate (the MCGS rollout ranking) so good incumbents arrive
early and A2's pruning bites sooner; surface the incumbent on guard timeout
so exact degrades to anytime-with-proof-on-completion instead of
all-or-nothing. The remaining computation after the optimum is found is then
exactly the proof of optimality. Days, after A2.

**A4. Memoize extracted terms per class.** Cache the interned minimal term
per class in the semi-persistent pool (restore truncates the cache with the
usual tokens); `build_best_term` becomes amortized O(1) after first build.
Acceptance: `au_deep_term_stress` depth-6000 from ~15 s debug to well under
a second; closes AU review perf item 5. 2-4 days.

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

**A6. Context-independence subsumption in exact.** Track per OR state
whether any action was cycle-blocked, transitively through children; a
result untouched by blocking is context-free and memoizes on the bare
`(l, r)` pair. Acceptance: the c3 dump's 23 states collapse to 14; rand
stratum exact times drop. After A2, because A2 already neutralizes the
families where blocking is the only cost driver. About a week.

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
