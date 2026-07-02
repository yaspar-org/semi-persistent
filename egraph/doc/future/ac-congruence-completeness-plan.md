# AC Congruence Completeness — Implementation Plan

Status: **partially implemented, gated off by default.** The completion algorithm
(A inter-reduction + B superposition + collapse + the reduced-basis machinery) is
implemented and passes its worked-example tests under both saturation strategies, but
is **disabled by default** (`set_cc`, opt-in) pending nested same-op
**flattening** (`WF_flat`), which is the gate to turning it on. See §0 for the exact
current state and next steps. This branch is `feature/ac-congruence-completeness`.

- **What/why** (problem, fix, proof sketch): [AC Congruence Completeness](../design/ac-congruence-completeness.md).
- **Status & verification staging** (the canonical summary): [A3 Future Work](../design/A3-future-work.md#ac-congruence-completeness-via-critical-pairs).
- **Task breakdown** (the checklist this plan feeds): [tasks](ac-congruence-completeness-tasks.md).

This plan records (0) current state and next steps, (1) where the new code lands,
(2) the architectural decisions, (3) the net-new primitives, and (4) the commit
sequencing and test strategy. Read the design doc §0–§9 first.

---

## 0. Current state and next steps  ← START HERE

### What is implemented and landed (all on this branch, full suite green)

The completion pass exists in `egraph/src/egraph.rs::cc_round`, called from
`rebuild()` when `cc` is enabled. The supporting machinery:

- **Multiset primitives** (`multiset.rs`): `multiset_disjoint/subset/subtract/union/lcm`,
  `monomial_cmp` (degree-lex), `normalize_ms`, plus destination-passing `_into` forms
  (no hot-loop allocation). [T1, S2]
- **AC-op enumeration** (`registry.rs`): `is_mset` / `mset_ops`. [T2]
- **(A) inter-reduction**: substitute a contained known sub-sum, materialize, merge. [T4]
- **(B) superposition**: lcm of two overlapping rules, both reducts normalized to normal
  form before merge. [T5]
- **Convergence machinery** (the §6b divergence fix): orientation by `monomial_cmp`,
  **minimal-monomial RHS** (never class-as-atom), **normalize-before-materialize**, and
  **collapse** of reducible rules via a *distinct* `FLAG_AC_COLLAPSED` (NOT `FLAG_SUBSUMED`:
  a collapsed node stays matchable, only leaves completion's active set; design §6b). [T5b]
- **Per-class slot** (`classes.rs` `ClassData{use_list, min_monomial, atomic}`): the rule RHS is
  read O(1) from this slot (`{classid}` if `atomic`, else `min_monomial`'s monomial), maintained
  on merge (`fold_min_monomial`), rolled back for free via the existing `SparseSetToken`. The
  **read-time orientation guard** (`monomial_cmp(M, rhs) == Greater`) makes the best-effort
  merge-time `min_monomial` safe (design §9b axis-2a). [S1, S3a]
- **Partner search via use-lists**: (B) finds partners through `iter_uses` (the
  `by_contains` use-list), not an O(rules²) all-pairs scan; partner→rule lookup is a binary
  search of the node-id-sorted `rules`. [S3b]
- **Safety backstop**: `rebuild` aborts completion (debug_assert) if it adds >50k nodes,
  so a divergence bug fails fast instead of OOMing.

Worked-example tests, all under **both** naive and semi-naive (the egg harness runs both),
all green: `ac_complete_containment` (§4a), `ac_complete_superposition` (§4b),
`ac_complete_cancel` (§5b). Unit tests: the `multiset` primitives, `mset_ops`, the
`CcSnapshot`, `ac_collapsed_leaves_completion_set_but_stays_matchable` (flag
separation), `ac_min_tracks_least_monomial_and_rolls_back` (slot maintenance + rollback).

### The gate: completion is OFF by default

`EGraph::cc` defaults `false`; `rebuild` runs only ordinary atom-congruence unless
opted in via `set_cc(true)` (egg directive `;; DERIVE_AC_EQS: on`). The gate has moved
twice: (1) believed to be flattening, (2) found to be a matcher bug (§0.3, now **fixed**),
(3) now a **convergence/performance blowup on large or deep graphs** (§0.4). Build-side
flattening (F2) and the matcher fix are done; completion is **correct** with-it-on across the
whole suite (446 tests pass on-by-default, zero failures), but **diverges in runtime** on the
proof stress tests, so it stays off by default.

### Known limitations and gaps (what completion does NOT do today)

These are the leftover gaps as of this branch. Each is a real limitation of the shipped
code, not a doc abstraction. They are safe because completion is off by default and because
an unsupported case is either rejected outright or simply derives fewer equalities, never a
wrong one (design §14: only "same e-class" is a trustworthy verdict).

1. **Multiple AC symbols: rejected.** Completion stores one `min_monomial`/`atomic` per class,
   which holds one AC operator's minimal monomial. With two `OpKind::MSet` operators a class
   could hold monomials of both (e.g. `a+b = a*b`), and the single slot would conflate their
   minima. `rebuild` enforces `OpRegistry::mset_op_count() <= 1` when completion is on and
   panics otherwise (tests `ac_complete_rejects_two_ac_symbols`,
   `ac_complete_allows_one_ac_symbol`). Lifting it is the per-op `min_monomial` slice (a pool of
   `nb_ac_op`-wide rows behind the same accessor, design §9b axis-1 option 3); the completion
   algorithm already runs per-op, only the slot widens. Until then, multi-AC is a hard
   precondition failure, not a silent miscompute.

2. **ACI operators: no completion at all.** Completion's round gates on `OpRegistry::is_mset`,
   which is `OpKind::MSet` only and excludes ACI. So an ACI operator canonicalizes (set
   semantics, dedup of duplicate children) but gets **no** superposition or inter-reduction:
   its congruence closure is incomplete exactly as un-completed AC is. Kapur FSCD 2021 §4
   gives the extra idempotence critical pair ACI needs (`f(M ∪ {a}) `vs` f(M)` for each
   `a ∈ M`); we do not generate it. **Consequence:** ACI is sound but AC-incomplete. The
   `mset_op_count` guard does **not** cover ACI (it counts only `OpKind::MSet`), so two ACI
   operators are not rejected; they are simply each left un-completed, which is sound. Adding
   ACI completion is: drive the round over ACI ops too, add the idempotence critical pair,
   and (for multi-symbol) the same per-op slot. No ACI completion test exists yet
   (`extract_aci` / `extract_ac_aci` exercise extraction, not completion).

3. **A (associative-only) operators: no completion, and believed not to need it.** A-nodes
   canonicalize by flattening into a sequence; the design claims associativity is decided by
   that alone (no commutativity, so no sub-multiset overlap to superpose). This is asserted,
   not tested: there is no A-operator completion test and no proof that flattening is
   complete for the ground associative word problem in our encoding. Treat "A is complete on
   its own" as a conjecture pending a test or a citation.

4. **The AC-matching / AC-unification residue.** Completion closes the *congruence* gap, and
   most apparent matching failures with it (the §5b cancellation example, a passing test).
   The truly residual case is a sub-sum that is equal to no named class and occurs as no
   node's child, referenced only by a pattern: binding a scalar pattern variable to it is AC
   unification, outside the e-matching relation, and would require materializing every
   sub-sum (the `O(3ⁿ)` blowup the multiset representation avoids). Kapur and Conchon both
   leave this open; we do not claim it (design §5b, §11). It is a matcher-relation boundary,
   not a congruence-closure defect.

5. **On-by-default is blocked on a scoping mechanism.** Completion is correct but diverges on
   one pathological input class (§0.4, §0.5); flipping it on needs a growth guard / on-demand
   scoping / degree bound first. Until then it is opt-in.

### Next steps, in priority order

1. ~~Recanonicalize-side flattening~~ **Not needed: flattening is complete at build alone.**
   Build-side flattening is done (`flatten_ac_children`, called from `add`, keyed on the class
   `summand_form`: atomic ⇒ keep `{class}`, else splice `min_monomial`; §0.2 resolution, design §6c).
   There is **no** recanon-side flattening to implement, and earlier drafts of this plan were
   wrong to list one. The flatten predicate keys on `atomic`, and `atomic` is monotone and is
   set the moment a class is used as an AC child (`add_use`). So every class *stored* as a
   child of an AC node is atomic from creation onward, recanon's `find(child)` only ever yields
   an atomic class, and `summand_form` of an atomic class is `{class}`: recanon-flatten would
   splice nothing. Design §6c proves this as a lemma with a worked trace. (Flattening was never
   the on-by-default gate either; that is §0.4/§0.5 divergence, narrative in §0.3.)

2. **S3b-worklist (deferred completion-driver rewrite).** Replace the batch
   round-to-fixpoint in `rebuild` with a completion worklist interleaved with the congruence
   worklist: a node enters when materialized or its class changes; draining it runs its two
   chores (§5d) for that node only. This removes the remaining per-round full `node_count()`
   scans that rebuild `rules`/`targets`. **Risk:** it changes the driver and can reintroduce
   divergence/non-termination; the batch round is currently correct and documented as a
   correctness-equivalent stand-in (design §9a). Keep the §4a/§4b/§5b differential tests as
   the oracle and the 50k backstop on. This is performance, not correctness, and not a gate.

3. **Verification (Verus soundness, then Lean completeness).** Per §7 staging: (a) the Verus
   soundness invariant on `rebuild` (every rule/merge ⊆ ACCC(S)), extended to cover (A)/(B);
   (b) the Lean abstract completeness theorem (Newman + Dickson + critical-pair lemma).
   Independent of (1)/(2); can start once the algorithm shape is final.

4. **Multi-AC-op support (later).** Single-op only today (one `min_monomial`/`atomic` slot per
   class). Multi-op is the same algorithm per-op; the storage upgrade is the pool of
   `nb_ac_op`-wide rows behind the same accessor (design §9b axis-1 option 3). Not needed
   until a multi-AC-symbol e-graph is required.

### 0.1 Flattening analysis (F1 dead-ends; resolved in §0.2)

> **Superseded by §0.2 and the §6c lemma.** Findings 1 and 3 below were reasoned from F1's
> flatten predicate ("splice a child whose union-find *representative* is a same-op node"),
> which is itself the bug (§0.2 "representative trap"). Under the correct `summand_form`
> predicate two of those conclusions are overturned: Finding 1's "recanonicalize gap" is
> **not real** (recanon-flatten is provably vacuous, because a stored AC child is always
> atomic; design §6c lemma), and Finding 2/3's §5b loss is **reversed** (§5b is preserved,
> its `c` is atomic). Kept as a record of what not to do and why the representative-keyed
> predicate misleads.

Attempt F1 tried the obvious "flatten nested same-op AC children in `add`": before the AC
arm sorts/coalesces, splice any child whose class representative is a same-op AC node. It
built and fired correctly (`+(+(a,b),c) → +(a,b,c)` confirmed by trace), but it is **not a
correct/complete fix**. Three findings, in the order they surfaced:

**Finding 1: `add`-flattening does not fix the matcher crash (`ac_complete_nested_match`).**
With flattening in `add`, the test still panics at the same `ematch.rs` `ByRepr` unbound-var
site. Reason: completion materializes flat nodes (its `materialize` goes through `add`), but
the `WF_flat` invariant is re-broken at **recanonicalization after a merge**. When a merge
makes some child's class representative an AC node, `rebuild_congruence` recanonicalizes the
parent via `MSetCanon::canonize`, which does `find` + sort + coalesce and **cannot flatten**:
it has only a `find: Fn(G)->G` closure (no node-structure access) and the variadic
`recanonize_node` span can only shrink, never grow. So a node flat at creation becomes
nested after a merge, and the matcher meets it. Flattening must therefore happen where
recanonicalization runs, not (only) in `add`.

**Finding 2: `add`-flattening regresses §5b (cancellation).** It un-reduces completion's
deliberate class-as-atom substitution. §5b builds `a + b + neg(a+b)`; `+{a,b}` is its own
class `c` (no leaf, no union). Completion's inter-reduction materializes `+{c, neg(c)}` so
the rule `(+ ?x (neg ?x)) ⇒ 0` can bind `?x = c`. But `c`'s class representative *is* the
`+{a,b}` node, so `add`-flattening splices `c` back to `{a,b}`, producing `+{a,b,neg(c)}`
again, exactly undoing the inter-reduction. The materialized `+{c,neg(c)}` never persists,
and `t = 0` is lost.

**Finding 3: §5b and eager flattening are in genuine tension (a design question, not a
bug).** `+{c, neg(c)}` and `+{a, b, neg(c)}` are the *same* AC term when `c = a+b`. The
2-summand rule `(+ ?x (neg ?x))` can match only the *un-flattened* `+{c, neg(c)}` form (two
summands `c`, `neg(c)`); against the flat form (`a, b, neg(c)`, three summands) it cannot,
short of AC-unification (`?x` binding to the sub-sum `a+b`), which the design **explicitly
leaves out of scope** (§11). So under `WF_flat`, §5b's outcome may not be derivable by
congruence completion alone. The design already half-predicts this: §5b says completion
makes the match work *given the non-flattened representation*.

**What this leaves open (resolve before implementing flattening):**
- *Where* to flatten so recanonicalization is covered (Finding 1). Candidates: a flatten
  step inside the variadic recanonicalize path (needs node access there, currently absent),
  or a post-`rebuild_congruence` repair pass that re-`add`s the AC nodes in `touched` whose
  reps went nested. The repair pass reuses `add`'s flatten but must not run *during*
  completion in a way that re-triggers Finding 2.
- *Whether* to flatten an `atomic` class's representative at all (Finding 2/3). The flatten
  criterion likely must exempt classes used as a deliberate atom, which collides with the
  current `atomic`-on-any-parent rule (§9a): a class that is *only* a child of a same-op AC
  parent gets `atomic=true` too, so "atomic" alone does not separate the §5b `c` (atom we
  must keep) from the §4b nested inner sum (must flatten). A finer distinction is needed
  (e.g. atomic-via-non-AC-parent vs atomic-via-same-op-AC-parent-only).
- *Whether* §5b is achievable under flattening at all, or whether its expected `t = 0` is
  reclassified as requiring AC-unification (§11, out of scope) and the test is re-scoped.

This is a design decision with user-facing scope implications (does completion + flattening
still derive §5b?), so it is deliberately left for review rather than guessed at. The
completion algorithm itself (gated off) is unaffected and remains correct on the
non-flattened representation it currently runs against.

### 0.2 Resolution (flatten on the class summand-form; §5b is preserved)

> This supersedes an earlier draft of §0.2 that recommended re-scoping §5b. That draft
> reasoned from F1's *representative-keyed* flatten predicate, which is itself the bug. The
> correct predicate keys on a representative-independent per-class property, and under it §5b
> **survives**. Full derivation in design **§6c**; summary here.

**The representative trap (the crux).** During recanonicalization of `+{a, b, c}`, the
elements are **e-class ids**, not terms. A class is equivalent to many syntactic forms at
once (a class may hold a `+`-node *and* a leaf *and* an `h(...)` node). "Is this child a sum
to splice?" keyed on `find(child)` being a `+`-node answers by whichever representative the
union-find picked, which depends on merge order. A flatten that depends on merge order is
**not canonical**. F1 used exactly this wrong predicate.

**The fix: flatten on the class's canonical *summand form*, which is the per-class slot we
already maintain (§9a), not the representative.**

```
summand_form(class) = if atomic(class) { {class} }        // a single atom, keep it
                      else              { min_monomial(class) }  // a pure sum, splice it
```

`atomic`/`min_monomial` are merge-folded class properties, representative-independent. To
canonicalize an `f`-node: replace each child `c` by `summand_form(c)`; splice the
multi-element (non-`atomic`) ones recursively; keep the atomic ones as summands. This is a
function of the e-graph state, so the result is genuinely canonical.

Consequences:

1. **Flattening is mandatory** (unchanged from the earlier draft, still right): a flattened
   multiset is *the* canonical AC-class representative (§2/§3); tolerating nested nodes makes
   `+(+(a,b),c)` and `+(a,b,c)` distinct e-nodes congruence never merges, reintroducing the
   §3 incompleteness this project removes. Tolerating nested nodes is self-defeating.
2. **§5b is PRESERVED, not lost.** `c = +{a,b}` is a child of `neg(c)`, so its class is
   `atomic`; `summand_form(c) = {c}`, so recanonicalizing `+{c, neg(c)}` keeps `c` as one
   summand. The node stays two-summand and the rule `(+ ?x (neg ?x))` fires; `t = 0` holds.
   The earlier "§5b needs AC-matching" worry was an artifact of the representative-keyed
   predicate (which splices `c` because *a* rep of its class is `+{a,b}`). The correct
   predicate does not, because the class is atomic.
3. **§4b's pure intermediate sum is flattened**: a critical-pair reduct's inner sum that is
   not referenced as a standalone atom is non-`atomic`, so `summand_form` returns its
   monomial and it is spliced; the matcher never meets it.

So `atomic` is decisive in *both* directions (completion RHS *and* flatten), and they
agree by construction. There is no "exempt atomic from flattening" hack; flattening just
reads `summand_form`, which is atomic-aware. Conchon (AC(X)) is the precedent: §3 flattens in
the canonizer, §4.1 Def 4.1 re-applies it after every rewrite. Our twist: a child is a
*class*, so "head symbol" becomes "the class's atomic-determined summand form." Conchon §8's
open instantiation issue (a rule needing a variable to bind an *un-materialized* sub-sum) is
a genuine AC-matching gap (§11) that does **not** include §5b (whose sub-sum `c` is
materialized and atomic).

**Implementation, smallest steps in order (no user-facing scope change; §5b stays green):**

1. **Add `summand_form(class)` into a buffer** (`class_rhs_into` already computes exactly
   this; reuse or rename it) as the flatten primitive.
2. **Build-side flatten in `add`**: replace each child by `summand_form` and splice the
   non-atomic ones to a fixpoint, before the AC arm sorts/coalesces. (Replaces F1's
   `flatten_ac_children`, which keyed on the rep; rekey on `summand_form`.)
3. **Recanonicalize-side flatten** (the real gate, design §6c): post-`rebuild_congruence`
   repair pass: for each AC node in `touched` whose canonical summand form changed, re-`add`
   it (flattens), merge the canonical node in, mark the non-canonical original
   `FLAG_SUBSUMED`. Same materialize/merge/retire shape as completion's (A).
4. `ac_complete_nested_match` flips to `EXPECT: ok`; `ac_complete_cancel` (§5b) stays green;
   matcher never meets a nested node; `set_cc(true)` can become the default.

### 0.3 The real gate is a matcher bug, not flattening (finding from F3 diagnosis)

Building F3 (recanonicalize flattening) started with a diagnostic: scan for any live AC node
with a non-flat child while `ac_complete_nested_match` runs. **It found none**: the matcher
panics with no nested AC node present. So the F1/§6b premise ("the crash is a nested node the
matcher can't decompose") is **wrong**.

The panic (`ematch.rs:132`, `env.get(repr).unwrap()` on a `ByRepr` cursor) is a **pre-existing
matcher / query-plan bug, independent of flattening and of completion**: matching a rule with
**two same-op AC atoms + rest-vars** (`(f (add x ..r1) (add y ..r2))`) drives two nested
`decompose_ac` passes, and the variadic re-join (`ByRepr`, the semi-naive variadic-mode
machinery) reads a query variable not yet bound in that branch ordering. Reproduced with
**completion OFF** in `ac_two_same_op_atoms.egg` (two overlapping `f(add, add)` terms, plain
saturation, same panic). Completion only *surfaced* it by creating more `add` nodes for the
rule to match.

Consequences:

- **Flattening was misdiagnosed as the gate.** F2 (build-side flattening) is still correct
  and worth having (it closes the canonicalization claim, `ac_flatten_build.egg`), but it was
  never going to fix `ac_complete_nested_match`. F3 (recanonicalize flattening) is **not
  needed** at all, and not merely "deferred": the diagnostic finding no non-flat node is not a
  coincidence but a theorem (design §6c lemma) — a stored AC child is always atomic, so
  recanon-flatten is provably vacuous. `flatten_ac_children` stays wired in `add` (F2); there
  is no F3 to schedule.
- **The real gate is the matcher bug.** It lives in `ematch.rs` `decompose_ac` / the `ByRepr`
  variadic re-join for the two-same-op-atoms case (related to the variadic-mode work). It is
  matcher territory, not AC-completion territory. Two `panic`-pinned tests track it:
  `ac_two_same_op_atoms` (completion off, the minimal repro) and `ac_complete_nested_match`
  (completion on); both flip to normal `egg_test!` when it is fixed.
- **Completion stays off by default** until the matcher bug is fixed, but for a *different and
  smaller* reason than believed: it is a bounded query-plan fix in the matcher, not the
  global `WF_flat` invariant. This likely makes enabling completion **closer**, not farther.

Next step on the gate is therefore **diagnose and fix the two-same-op-atoms matcher bug**
(its own task, in `ematch.rs`), not more flattening.

**Update:** fixed (commit `2501b32`). Root cause: `leapfrog_join` unconditionally
`env.clear(target)` after its loop; for a bound-node re-join (`ByRepr ∩ ByOp`) the target was
bound upstream by `ExtractChild`, so clearing it left a sibling's node var unbound on
re-entry. Fix: save/restore the target's prior binding instead of clear. Both panic-tests
(`ac_two_same_op_atoms`, `ac_complete_nested_match`) flipped to `EXPECT: ok`. The gate then
moved to §0.4.

### 0.4 With the matcher fixed, completion is correct but diverges on large graphs

Experiment (this session): forced `cc` on by default and ran the full suite. Result:
**446 tests pass, zero failures, zero panics** with completion globally on. So the algorithm
is *correct* engine-wide, not just on the worked examples. **But** the two
`egraph_proof_test::stress_proof_test` cases (`stress_medium`, `stress_large`) go from ~0.01s
(completion off) to **not finishing** (completion on). Tracing `stress_large` shows a genuine
divergence, not mere slowness:

```
round 0: active=68   reducible_rules=4   antichain_core=64   crit(B)=91     nodes 908  -> 1054
round 1: active=133  reducible_rules=0   antichain_core=133  crit(B)=378    nodes 1054 -> 1416
round 2: active=222  reducible_rules=0   antichain_core=222  crit(B)=1804   nodes 1416 -> 2792
round 3: active=517  reducible_rules=63  antichain_core=454  crit(B)=25285  nodes 2792 -> 19646
round 4: active=1579 reducible_rules=719 antichain_core=860  crit(B)=532896 ...
```

`crit(B)` (critical pairs) grows ~10x/round and `active` keeps climbing, the same shape as
the original §6b divergence the collapse machinery is supposed to prevent. The stress graph
is the trigger: it builds **deep** layers of AC nodes (sums whose children are themselves
compound/AC nodes) and then does many random merges, producing many overlapping non-atomic
(pure-sum) classes. A shallow probe (all-distinct 2-element `plus` sums over 8 leaves + a
couple leaf merges) does **not** diverge (`active(rules)=0`, the sums are over atomic
leaves), so the trigger is specifically **nesting + post-merge non-atomic sums that
overlap**.

**Resolved (instrumented, this session): it is a collapse-timing bug, not an inherent
basis.** The executable invariant checker (`ac_invariants.rs`, run via
`AC_BASIS_DUMP=1 cargo test investigate_completion -- --ignored --nocapture`) reports, at
the **start** of each round (after `rebuild_congruence`, before `cc_round`),
`reducible_rules` = active rules whose LHS strictly contains another active rule's LHS, and
`antichain_core` = `active - reducible_rules`. Two facts settle the question:

1. **The active set fed to superposition is not an antichain.** From round 3 on,
   `reducible_rules` is non-zero and grows (4, 0, 0, **63**, **719**). A correctly
   inter-reduced rule set is a Dickson antichain by construction; reducible rules surviving
   means collapse did not retire them before they were used as superposition sources. The
   collapse `(A′)` pass scans the rule set captured at round start, but superposition `(B)`
   and the `(A′)` materialize **mint new nodes within the same round**, and those new
   reducible nodes are not collapsed until the *next* round. By then `(B)` has already
   superposed against them, and the critical-pair count explodes.
2. **The blowup is driven by the reducible tail, not the core.** `crit(B)` tracks `active`
   (which includes the reducible rules), not `antichain_core`. The core does grow (64 → 860)
   but sub-quadratically relative to `crit(B)` (91 → 532896); the extra critical pairs come
   from superposing against rules that should already have been collapsed.

So the gate is a **within-round collapse-before-superpose ordering bug**, not correctness,
not flattening, and not an inherently large canonical basis. Completion stays off by default.
The fix: a round must reach a collapse fixpoint **before** it superposes, so `(B)` ranges
only over the inter-reduced antichain. The batch round violates this (it snapshots rules
once, then collapses and superposes against the same stale snapshot). This is exactly the
**S3b worklist rewrite**: collapse to fixpoint, recompute the antichain rule set, then
superpose only over that antichain, normalizing each critical pair against the full
antichain and merging only non-trivial reducts. The 50k-node backstop does **not** fire here
within the timeout because growth, while exponential, is gradual; a per-round `crit(B)` or
`active` growth-rate guard would catch it sooner.

### 0.5 Three fixes applied; the residual divergence is genuine basis growth

Acting on the §0.4 diagnosis, three correctness-preserving fixes landed (commits `981f96e`,
`fb32864`), each measured on `investigate_completion` (seed 42, 30 leaves, 4 layers, 20
merges) via `AC_BASIS_DUMP=1 AC_COMPLETE_TRACE=1`:

1. **Reducible-rule exclusion.** Precompute a per-rule `reducible` flag (LHS strictly
   contains another active rule's LHS, same op) and skip reducible rules as both `(B)`
   sources and partners. Superposition now ranges only over the within-round antichain.
2. **Trivial critical-pair filter.** Normalize *both* reducts to multisets before
   materializing; if they coincide the pair is already joinable, so skip it (no node, no
   merge). Previously each trivial pair minted two spurious nodes that became fresh rules.
   This was the biggest single win: node growth at rounds 3-4 dropped from `+9094/+30155`
   to `+1316/+2880`. The trace showed why: **12785 of 13645** critical pairs at round 3 were
   trivial.
3. **Incremental superposition (S3b).** `(B)` is now semi-naive over the `touched` delta: a
   pair is new only when ≥1 endpoint changed since the previous round. A full confirmation
   round certifies convergence (the node-touch delta can miss a pair whose RHS shifted via
   the rule's *own* class merging). Modest further reduction (round 3 `crit(B)`
   13645 → 12168, round 4 52869 → 39224); the delta is most of the rule set each round here,
   so old×old removal is limited.

**New finding: the stress graph still diverges, and the cause is now isolated to real
canonical-basis growth, not algorithmic waste.** With trivial pairs filtered, `antichain_core`
(active rules minus reducible = the true reduced basis after one collapse pass) grows
**~1.6×/round**: 64, 121, 204, 398, 654, 1046. `nontrivial` critical pairs track it (75, 105,
337, 860, 1952). So on this graph the ground AC-canonical rewrite system is genuinely large:
many overlapping non-atomic (pure-sum) classes, each pair of overlapping sums a legitimate
superposition that yields a *new* irreducible rule. Dickson's lemma bounds it, but the bound
is large here. This is no longer a bug to fix in the round; it is the **cost of full AC
congruence closure on a dense, deeply-nested, heavily-merged graph**.

Implication for the default: completion stays **off by default**, and the open work is no
longer "make this graph converge fast" but **bounding/scoping when completion runs** so a
pathological graph cannot blow up. Options (not yet chosen): (a) a hard `active`/`crit(B)`
growth-rate guard that disables completion for the current `rebuild` and logs it, rather than
the blunt 50k-node backstop; (b) completion only on demand (a query/extract that needs AC
congruence closure triggers it on the relevant sub-graph, not globally on every `rebuild`);
(c) a degree bound on materialized monomials (refuse to mint rules above size *k*), trading
completeness for termination. The instrumentation (`cc_basis_dump`) is the tool to evaluate
any of these.

[ac-flattening TODO]: ../design/09-pattern-matching.md

---

## 1. Goal and non-goals

**Goal.** Make `rebuild()` produce an AC-**congruence-closed** e-graph, by adding
Kapur's two missing completion steps (FSCD 2021) to our AC handling:

- **(A) Inter-reduction** — for AC nodes `+M = d` and `+A = a` with `A ⊆ M`,
  substitute `a` for the sub-multiset `A`, materialize `+((M−A) ⊎ {a})`, merge with `d`.
- **(B) Superposition / critical pairs** — for overlapping `+A = a`, `+B = b`
  (sharing ≥1 element, neither containing the other), materialize the lcm
  `+AB` where `AB = (A ⊎ B) − (A ∩ B)`, reduce it both ways, merge the reducts.

**Required (do not skip — divergence finding, design §6b):**

- **Collapse / inter-reduction** — Kapur Algo 1 step 4 / Conchon Collapse. On `A ⊊ M`,
  after the (A) merge, mark `+M` `FLAG_SUBSUMED` so it leaves the active rule set. This
  is what keeps the active LHSs a Dickson antichain and makes completion terminate.
  Omitting it diverges (≈5× nodes/round; see §4 finding). **In scope, mandatory.**
- **Kapur's monomial ordering `≫_f`** — degree-lexicographic (multiset size, ties by
  class id). Needed to orient *which* of two containment-comparable rules collapses
  (the larger). NOTE: a prior draft listed this as a non-goal ("union-find is our
  canonical layer"); that was wrong — the union-find orients each rule's RHS, not the
  choice *between* two rules' LHSs (design §9 correction). **In scope.**

**Non-goals (explicitly out of scope, do not attempt):**

- AC unification in the matcher — binding a *scalar* pattern variable to an
  un-materialized sub-sum (`?x = a+b` against `+{a,b,c}`). Spec §11. Open problem.
- Kapur's *unique reduced canonical presentation* across AC symbols (canonical
  signatures). We need the monomial order to orient collapse, but not the full
  machinery for a canonical normal-form presentation — deriving equalities is enough.
- AC **flattening** of nested same-op terms (e.g. `+(a, +(b,c))` → `+{a,b,c}`) is a
  separate workstream ([ac-flattening TODO]), but it turned out to be a **hard
  prerequisite**, not an optional aside: without it completion crashes the matcher on
  the nested nodes it materializes (see §0 step 1 and §6). It is the gate that keeps
  completion off by default. So: out of scope for the *completion* code, but required
  before completion can be enabled.
- Saturation-loop termination. We only claim each single completion pass over the
  current finite AC-node set terminates (spec §10, Dickson). Productive user rules
  can still diverge; that is the rule set's concern.

[ac-flattening TODO]: ../design/09-pattern-matching.md

---

## 2. The architectural decision the spec left open  ✅ DECIDED: Option A, implemented

**Resolved.** Completion is owned by `rebuild()` (Option A below); this is how
`cc_round` is implemented. The rest of this section records why, for the
record. The partner search ended up driven by the class **use-lists** (`iter_uses`)
rather than the matcher's `IndexStore`, which §0/S3b describe.

The spec §9 writes the pass as living "in `rebuild()`… for x in M.distinct() { for
partner in index.by_contains[x] ∩ index.by_op[f] }", and §9's "Index maintenance"
note says it runs "against a frozen snapshot of `by_contains`, … refreshes the
index and iterates."

**But in the real code, `by_contains`/`by_op` are not live during `rebuild()`.**
The `IndexStore` (`src/index.rs:66`, fields `by_op`/`by_repr`/`by_contains`/`by_child_pos`)
is a **transient, matching-side** structure, bulk-built by `IndexStore::build(eg)`
*after* `eg.rebuild()` returns, once per saturation round
(`src/saturate.rs:56-57`):

```rust
eg.rebuild();                       // worklist/use-list driven; does NOT touch IndexStore
let index = IndexStore::build(eg);  // by_op / by_contains / … built here, post-rebuild
```

`rebuild()` itself (`src/egraph.rs:532-571`) is purely union-find-worklist driven
(`while let Some((absorbed_uses, survivor)) = self.worklist.pop()`), recanonicalizes
each parent via `self.nodes.recanonize_node(...)`, and has **no per-op iteration and
no access to `by_contains`**. So §9's loop cannot be dropped in as written.

Two ways to reconcile, and I recommend the first:

### Option A (recommended) — AC-CC completion as a self-contained fixpoint that `rebuild()` owns

Keep the external contract **"after `rebuild()` returns, the e-graph is
AC-congruence-closed."** Package the completion as its own loop that `rebuild()`
calls after the existing worklist drains:

```
fn rebuild():
    loop:
        run existing worklist closure (atom-level congruence)   # egraph.rs:532 body
        snapshot := build AC-only partner index over live AC nodes  # see §5
        changed  := cc_round(snapshot)   # (A)+(B): materialize nodes, push merges to worklist
        if not changed: break
        # new merges/nodes re-enter the worklist; loop re-closes atom congruence
```

Why recommended:
- Preserves the proof target. A3 says soundness is proved **on the real Rust
  `rebuild`** and "Provable today on the current recanonize-only rebuild; extend
  the invariant when the substitution steps land." That invariant is *"after
  rebuild, union-find ⊆ ACCC(S)"* — it only stays a `rebuild` postcondition if the
  completion lives inside `rebuild`.
- Matches the spec's "frozen snapshot … refresh … iterate" round structure (§9)
  literally: the pass owns its snapshot, independent of the matcher's `IndexStore`.
- The matcher's `IndexStore` stays what it is today — a post-rebuild, matching-side
  artifact — with no new lifecycle coupling.

Cost: the partner index is rebuilt per completion round. Acceptable for a first
correct cut; the spec explicitly says incremental maintenance is "a performance
option, not a correctness requirement" (§9). See §5 for what the snapshot must
contain (only AC nodes, not the full four-index `IndexStore`).

### Option B (not recommended) — separate saturation phase after `IndexStore::build`

Run (A)/(B) in `saturate()` after `IndexStore::build`, reusing the existing
`by_contains`/`by_op` directly. Lower code volume, but: it moves
congruence-completeness out of `rebuild` into the saturate loop (so `rebuild` alone
is no longer congruence-closed); new nodes/merges dirty the graph and force another
`rebuild` + `IndexStore::build`, i.e. an inner fixpoint in the driver; and it
fractures the soundness proof target (the invariant is no longer a `rebuild`
postcondition). It also wouldn't help callers that use `rebuild` outside `saturate`.

**Decision requested at review:** confirm Option A (completion owned by `rebuild`,
own AC-node snapshot) before any code is written. Everything downstream (proof
target, where primitives live, test placement) keys off this.

---

## 2b. Interaction with naive and semi-naive evaluation

This is the question that most easily produces a silent completeness bug, so it is
worth being exact. **Option A makes the interaction clean** — this is the strongest
argument for it — but it imposes two requirements that the implementation must meet.

Both drivers call `rebuild()` identically and are otherwise unaware completion runs:

```rust
// saturate (naive), saturate.rs:56-57
eg.rebuild();
let index = IndexStore::build(eg);                 // full index over a closed graph

// saturate_semi, saturate.rs:233-242
eg.rebuild();
let full  = IndexStore::build(eg);
let delta = (i > 0).then(|| IndexStore::build_delta(eg, eg.touched()));  // delta = touched
eg.clear_touched();
```

The whole interaction reduces to two requirements:

- **(R1) Completion mutates only through the standard logged paths.** Materialize
  nodes via `add`/`add_ac` → `register_if_fresh` (which pushes the fresh id to
  `touched` and adds the singleton class, `src/egraph.rs:599-605`) and equate via
  `merge` (which pushes to the worklist; the worklist then recanonicalizes parents,
  logging *them* to `touched` too). No lower-level insertion that bypasses `touched`.
  Given R1, completion's products are **indistinguishable from user-rule products**
  in both the full index and the delta log.
- **(R2) `rebuild()` returns only at the joint fixpoint** of atom-congruence ⋈
  completion (plan §4), so the graph it hands back is fully AC-congruence-closed.

### Naive (`saturate`)

Correct given R2 alone. `rebuild()` does strictly more work and emits more
nodes/merges; `IndexStore::build` then indexes an already-closed graph; every rule
matches against everything each round. The only new obligation versus today is that
`rebuild` reaches its *own* fixpoint before returning (R2).

### Semi-naive (`saturate_semi`)

Correct given R1 + R2. The delta a round presents to the matcher is
`build_delta(eg, eg.touched())`, read **after** `rebuild()` returns and **before**
`clear_touched()`. So:

- From the matcher's view, `rebuild` is **atomic**: the graph went `S → S′`, and the
  delta is exactly `S′ − S`. Completion's *internal* fixpoint rounds are invisible —
  every node and merge it produced across all of them folds into the single `touched`
  log presented when `rebuild` returns. There is no "completion happened between
  rounds the matcher didn't see" hole, because completion happens *inside* the
  `rebuild` the matcher already brackets.
- Completion-created AC nodes are **ordinary AC nodes**, so the existing semi-naive
  variant decomposition handles them with no change — including the `by_op ∩
  by_contains` delta-mode path that the variadic-mode and `by_contains` fixes
  established (these were the two prior semi-naive AC defects; completion rides their
  machinery, it does not re-open it).

### The one subtle obligation: merge-only deltas

Completion can equate two **pre-existing** AC nodes (the §4b case: `+{c,d}` and
`+{a,e}`, where *neither reduct is new*). No fresh node is created, yet a rule keyed
on the now-merged class must be able to re-fire under semi-naive. That equality
reaches the delta through the **existing** merge path: `merge` → worklist →
recanonicalize the parents of the absorbed class → those parents land in `touched`
and their `by_repr` bucket changes. This is the *same* obligation every merge has
today (it is how ordinary congruence merges propagate under semi-naive); completion
introduces no new mechanism, only new merges. But because a merge with **zero** new
nodes is the easy case to under-test, the semi-naive **differential test is a hard
requirement** (T6): every completion-derived equality must be found under *both*
`saturate` and `saturate_semi`.

### Efficiency (not correctness) — the partner search is the unmatched cost

One asymmetry to call out honestly. Completion's *own* partner search (plan §5) is
naive in v1: it re-scans AC-node pairs over a freshly built per-round snapshot every
`rebuild`, `O(AC pairs)`, regardless of saturation strategy. So under semi-naive,
completion is the one component that does **not** inherit the "touch only the delta"
speedup — the rest of the round is delta-scoped, but completion re-examines all AC
pairs. This is purely a performance gap, not a correctness one (spec §9: incremental
maintenance is "a performance option, not a correctness requirement"). Closing it —
pairing a node only when it or a partner is in `touched` — is the **P1** follow-up.
v1 should ship the naive search and the differential test that proves it correct.

---

## 3. What we reuse vs. what is net-new

Grounded in the code map. Reuse:

| Need | Existing mechanism | Location |
|---|---|---|
| Per-element child→node lookup | `by_contains` *concept* (keyed by child class repr) | `src/index.rs:74`, build at `:135-153` |
| AC child multiset of a node | `ac_children(id, &mut Vec<(G, Multiplicity)>)` | `src/egraph.rs:829-842` |
| Canonicalize a fresh multiset (find+sort+sum-mult) | `MSetCanon::canonize` | `src/canon.rs:87-115` |
| Insert/probe an AC node, get its class | the `add`/`add_ac` path | `src/egraph.rs:320-336`, `src/node_store.rs:241` |
| Merge two classes, schedule rebuild | `EGraph::merge` / `merge_justified` | `src/egraph.rs:374-392` |
| AC op identification | `match OpKind::MSet { .. }` via `ops.info(op).kind` | `src/registry.rs:29-63`, `:256` |

Net-new (none of these exist today — confirmed by the code map):

1. **Multiset algebra primitives** over `&[(G, Multiplicity)]` (sorted-by-`G`, the
   canonical AC child form): `multiset_disjoint`, `multiset_intersect` (or just a
   `⊆` test for (A)), `multiset_subtract` (`msub`), `multiset_union`,
   `multiset_lcm`. Today the only subtract is inline multiplicity-mutation in the
   matcher (`src/ematch.rs:742,788`); it is **not** a reusable helper. Write these
   as standalone functions on the canonical pair-slice form, unit-tested in isolation.
2. **An AC-op iterator / filter.** There is no `is_mset()` and no iterator over
   registered AC ops; `OpRegistry` exposes `len()`/`info(id)` only (`src/registry.rs:131,256`).
   Add a small helper that yields op ids whose `info(op).kind` is `OpKind::MSet{..}`.
3. **The AC-node partner snapshot** (§5) and **the completion round** itself
   (`cc_round`), per Option A.

The matcher's `DecomposeAC` is **not** reused for the search (it enumerates sub-sums
transiently for user rules; spec §7 "the `rest` machinery is the arithmetic, not the
search"). We only borrow the *idea* of multiset subtract — and we implement it fresh
as a clean primitive rather than threading through `decompose_ac_elem`.

---

## 4. The completion round (Option A internals)

> ⚠️ **DIVERGENCE FINDING (implementation, 2026-06-18).** A first cut of (B) that
> materialized both reducts and merged them with **no collapse and no
> normalize-before-merge** diverged: node count ≈4–5×/round, critical pairs
> ≈10×/round on the five-constant §4a example — OOM within ~15 rounds. The fix is the
> **Collapse / inter-reduction** step (Kapur Algo 1 step 4 / Conchon Collapse), now in
> design doc **§6b**, plus **normalize-each-reduct-to-normal-form before comparing**.
> `rebuild()` carries a `>50k`-node-growth `debug_assert` backstop meanwhile. The
> pseudocode below is the **corrected** version; the earlier draft here was the buggy
> one. See [[ac-completion-needs-orientation]] memory.

Per spec §6b/§7/§9, rule-driven (every *non-subsumed* AC node `+A → a` is a rule):

```
cc_round(snapshot) -> changed:
  changed = false
  for each AC op f:
    for each ACTIVE (non-subsumed) AC node  +M = d   of op f:
      partners = ⋃_{x ∈ distinct(M)} snapshot.by_contains_ac[f][x]   # active only
      for each partner  +A = a   in partners (dedup; skip self):
        if multiset_disjoint(M, A):        continue          # trivial CP (spec §6)
        if A ⊊ M:                                            # (A) + COLLAPSE
          M' = normalize_ac(f, (M − A) ⊎ {a})                # to fixpoint, ALL rules
          if find(M'.class) != find(d): merge(M'.class, d); changed = true
          mark FLAG_SUBSUMED on +M       # collapse: retire the reducible source (§6b)
        else if A ∩ M ≠ ∅ and not (M ⊆ A):                   # (B) superposition
          AB = lcm(M, A)
          c1 = normalize_ac(f, (AB − M) ⊎ {d})               # normalize BOTH reducts
          c2 = normalize_ac(f, (AB − A) ⊎ {a})               # before comparing
          if find(c1) != find(c2): merge(c1, c2); changed = true
  return changed

normalize_ac(f, M):   # Kapur Def 3 rewriting to normal form
  repeat until no rule applies:
    find an ACTIVE rule +A→a with A ⊊ M (a by_contains query), M := (M − A) ⊎ {a}
  return probe_or_insert_ac(f, M)        # materialize the NORMAL FORM only
```

The two non-optional corrections over the naïve version (design §6b):
- **Collapse**: on `A ⊊ M`, after merging, mark `+M` `FLAG_SUBSUMED` so it leaves the
  active set. This keeps the active rule LHSs a Dickson antichain — the entire basis
  of termination. Without it, completion diverges.
- **Normalize before merge**: never materialize a raw reduct; reduce it to normal form
  against *all* current rules first (a reduct can be a superset of an existing LHS, so
  it is itself reducible and must shrink). Only a genuinely-new normal form persists.

Notes / invariants to preserve:
- `probe_or_insert_ac` must **canonicalize then probe-or-insert** (find each child,
  sort, sum multiplicities — `MSetCanon::canonize`), so we never create a
  non-canonical duplicate. New nodes land on `touched`/worklist via the normal `add`
  path so the next atom-closure pass and the next round see them.
- The materialized multiset for (B) can be **larger** than `M` — so it **cannot**
  go through the in-place `recanonize_node` span rewrite, which can only shrink
  (`src/caches.rs:449`, `new_len <= end-start`). It must be a fresh `add_ac` + merge.
  Calling this out because it's the easiest way to introduce a corruption bug.
- (A) is the degenerate case of (B) where `A ⊆ M` (then `AB = M`, one reduct is `M`
  itself). Implementing (B) correctly subsumes (A); we keep the explicit `A ⊆ M`
  branch only because substituting into the existing node `d` is cheaper than the
  general two-reduct form. Confirm this equivalence in a test.
- Self-pairing (`partner == the node itself`) and symmetric double-processing
  (pair `(M,A)` then `(A,M)`) must be guarded, else redundant work / churn.

---

## 5. The AC-node snapshot

What the round needs is narrower than the matcher's `IndexStore`: only
`by_contains` and `by_op` **restricted to AC ops**, keyed by child class repr.
Build it by walking live AC nodes once per round (mirror the relevant slice of
`IndexStore::build_from`, `src/index.rs:110-174`, specifically the variadic
`by_contains` population at `:135-153`, but skip `by_repr`/`by_child_pos` and all
non-AC ops). Skip `FLAG_SUBSUMED` nodes, as `build_from` does.

Open perf question (defer): per-round full rebuild of this snapshot is `O(total AC
child slots)` each round. Fine for correctness and for the test sizes we care about.
Incremental maintenance keyed on `touched` is the optimization, explicitly deferred
by spec §9. Do **not** build it in the first cut.

---

## 6. ⚠️ Flattening interaction — a soundness-adjacent caveat

The search's completeness rests on the index contract "`by_contains[x]` lists every
node containing child class `x`" and on `A ⊆ M` being decidable as multiset
containment over **flattened** multisets. Today we do **not** flatten nested
same-op terms ([ac-flattening TODO]): `+(a, +(b,c))` is stored as `+{a, n}` where
`n` is the class of `+(b,c)`, not as `+{a,b,c}`. So a partner `+{b,c}` is *not* a
sub-multiset of `+{a, n}` at the representation level, even though it is one
semantically.

Implication: without flattening, (A)/(B) operate on the *unflattened* multisets and
will still be **sound** (we only ever assert consequences of real `+A=a` rules), but
their **completeness claim is relative to the flattened term universe**. The
completeness proof (spec §10, §12) assumes flattened multisets. So either:
- (a) land flattening first (separate work, not this branch), or
- (b) scope the completeness claim of this branch to "complete for already-flat AC
  node sets," and note flattening as a prerequisite for the full claim.

This must be stated explicitly in the doc when we update status, and it's worth a
decision at review. It does **not** block starting the implementation (soundness
holds either way), but it bounds what we can claim.

---

## 7. Verification staging (from A3, unchanged — recorded here for sequencing)

1. **Verus soundness invariant on today's rebuild** — the invariant *"every AC rule
   `+M→c` and every merge `c~d` is `⊆ ACCC(S)`"* holds on the current
   recanonize-only `rebuild` (provable before any new code). Establish it first as
   the baseline.
2. **Extend that invariant as (A)/(B) land** — each completion step must preserve it
   (both reducts equal `+AB`, Kapur Lemma 5 ⇒ `ACCC(S)`-equal; spec §12). This is
   the soundness deliverable for the shipping Rust.
3. **Lean abstract completeness theorem** — Newman + Dickson + critical-pair lemma on
   the abstract `(P, R)` model (spec §12), parameterized to transfer by refinement.
   Out of scope for the *coding* milestones below; tracked separately.

Why split (Verus soundness / Lean completeness): A3 §"Why split." Do not attempt the
confluence metatheory in Verus.

---

## 8. Commit sequencing (historical — the original T-series staging)

Steps 1–6 below are **done** (commits in git log, T1/T2/T4/T5 + T5b for the convergence
fix). Step 7 (Verus) and step 8 (docs, ongoing) plus the S-series refactor (S1 slot, S2
DPS primitives, S3a/S3b) are the actual implementation history; the live "what's left" is
§0, not this list. Kept for traceability. Each step built and tested green before the next.

1. **Multiset primitives + tests** — `multiset_disjoint/subtract/union/lcm` (and `⊆`)
   on canonical `&[(G, Multiplicity)]`, with unit tests. Pure, no e-graph state. (T1)
2. **AC-op iterator helper** + tests. (T2)
3. **AC-node snapshot builder** (`by_contains_ac`/`by_op_ac`), factored to share the
   variadic-population logic with `IndexStore::build_from` where clean. Tested
   against the existing `by_contains_variadic` fixture (`src/index.rs:406`). (T3)
4. **(A) inter-reduction only**, wired into `rebuild` per Option A, behind the
   simplest correct loop. Add the §4a trace as a test (`+(a,b)=c`, `+(a,b,d)=e` ⇒
   `e = +(c,d)`). (T4)
5. **(B) superposition**, completing the round. Add the §4b trace as a test
   (`+(a,b)=c`, `+(b,d)=e` ⇒ `+(c,d)=+(a,e)`) and the §5b cancellation example. (T5)
6. **Fixpoint + snapshot-refresh loop** hardening: multi-round convergence test,
   semi-persistent rollback interaction (`rebuild_after_restore`,
   `src/egraph.rs:1055`), PROOFS-path justification for the new merges. (T6)
7. **Verus soundness invariant** baseline + extension (steps 1–2 of §7). (T7)
8. **Docs**: flip A3 status, fold the flattening caveat (§6) and the Option-A
   decision into the design doc, link this plan. (T8)

Lean completeness (§7 step 3) is tracked as a follow-up milestone, not gated on the
coding commits.

---

## 9. Test strategy

Use the existing hand-rolled fixture idiom (no new DSL): the `Th` struct +
`eg::<T,P>()` helper (`src/egraph.rs:905-931`) that pre-registers `plus` (AC), `and`
(ACI), `sub` (A); assert via `eg.find(n1) == eg.find(n2)`. New worked-example tests
(§4a, §4b, §5b) go alongside `ac_congruence` (`src/egraph.rs:984`). Multiset
primitives get their own `#[cfg(test)] mod`. The differential AC tests in
`src/saturate.rs:1373-1908` are the integration backstop. Run the PROOFS-path
(`src/egraph_proof_test.rs`) for the new merges' justifications.

---

## 10. Resolved questions (kept for the record)

These were the open questions; all are now decided. Current open work is in §0.

1. **Option A vs B** (§2): **Option A** — completion owned by `rebuild`. Implemented.
2. **Flattening** (§6): not a "scoped claim" choice — flattening is a **hard prerequisite**.
   Completion is implemented but **gated off** until flattening lands (§0 step 1). The
   matcher crashes on the nested nodes completion materializes without it.
3. **Snapshot cost** (§5): moot — the partner search uses the class **use-lists**
   (`iter_uses`), not a rebuilt `IndexStore` snapshot at all (§0 / S3b).
4. **Worked-example test set**: §4a/§4b/§5b cover the three cases; `ac_complete_nested_match`
   pins the flattening blocker. Add more once flattening lands and completion is on by default
   (then the full `saturate.rs` differential suite applies with completion enabled).
