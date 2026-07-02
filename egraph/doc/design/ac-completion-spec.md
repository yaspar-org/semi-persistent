# AC Completion: `min_monomial`, the matcher bug, and a compliance review

A focused companion to [ac-congruence-completeness.md](ac-congruence-completeness.md) (the
full specification: e-graph as a rule set §0b, the fix §6, collapse §6b, per-class data §9a,
proof sketch §12). This does not restate it. It adds three things that document leaves
implicit, and fact-checks them against Kapur 2023 (the LMCS journal version of the FSCD'21
algorithm; §, Def, Lemma, Thm numbers below are Kapur's):

1. the `min_monomial` invariants the engine must keep (§9a defines `min_monomial`; this states the
   checkable properties and the one maintenance gap from Kapur's "reduced") (§1);
2. the `(f (add x ..r1) (add y ..r2))` matcher bug, over concrete nodes (§2);
3. a clause-by-clause check that the code matches Kapur's algorithm, with the observed
   growth explained (§3).

Read every e-graph fact as a rewrite rule (main-doc §0b, Kapur §2.2): an AC node with
operator `+` and child multiset `M` in class `c` is the rule `+M → r(c)`; the union-find is
the constant-rule layer, where a class merge is a constant rule `d → e` rewriting one class
representative to the other. "Classes `c`, `d` are equal" means `find(c) = find(d)`: one
rewrites to the other under those constant rules.

---

## 1. `min_monomial`: the properties the engine must keep

The main doc §9a defines the per-class data: a class carries `find(c)` (the union-find tag,
not necessarily an AC monomial) and `min_monomial(c)` (the `≫_f`-least `+`-monomial of the class,
the rule RHS), and the rule RHS is `{c}` if `atomic(c)` else `monomial_of(min_monomial(c))`. This
section does not re-derive that. It states the four invariants `min_monomial` must satisfy *as
checkable properties* (the ground-truth checkers of §3 verify them), and the one place
maintenance is weaker than Kapur's "reduced".

### 1.1 Properties (`c` has a `+`-node; `mono(g)` is `g`'s canonical child multiset)

- **(P1) Membership.** `min_monomial(c)` is a real AC node `g` with `find(g)=find(c)`, never a
  synthetic monomial.
- **(P2) Leximin (quality).** At the fixpoint,
  `mono(min_monomial(c)) = min_{≫_f}{ mono(g) : g a +-node in c }`. Because rewriting strictly
  decreases `≫_f` and a canonical system gives every class member one shared normal form,
  that normal form is the `≫_f`-minimum, so this matches Kapur's canonical signature.
- **(P3) Orientation safety.** For any `+`-node `+M` in `c`, `M ≫_f mono(min_monomial(c))` or
  equal, never `M ≺_f`. So `+M → r` with `r = min_monomial` is always correctly oriented, which is
  why normalization terminates.
- **(P4) Existing-constant closure.** `mono(min_monomial(c))` is a multiset over existing class
  ids, never a fresh constant, so reading it as a RHS cannot grow the constant pool. Its
  violation (class-as-atom) is the one unbounded divergence (§6b).

### 1.2 Maintenance, and the gap from Kapur's "reduced"

`min_monomial` is updated O(1) on merge: the survivor's `min_monomial` is the `monomial_cmp`-smaller of
the two minima (`fold_min_monomial`), no search, no allocation. This is **best-effort on (P2)
only**: `monomial_cmp` reads `find` of children, which is mid-cascade during a merge, so the
stored min can be a non-minimal but valid sum until a later merge refreshes it. (P1), (P3),
(P4) always hold, so a stale min is never a soundness, orientation, or divergence risk; the
read-time **orientation guard** (emit `+M → r` only if `monomial_cmp(M,r)=Greater`) runs
where finds are settled and is exact regardless of staleness.

This is precisely where we are weaker than Kapur. Kapur's **reduced** system (§3) requires
that **neither the left nor the right side** of any rule be reducible by the others; his
SingleACCompletion step 4(ii) fully normalizes each RHS. Our option (a) guarantees the LHS
half (the antichain, the termination measure) and the orientation of the RHS, but the RHS
need not be the global minimum. So our basis is "reduced in the LHS, best-effort in the RHS":
larger than Kapur's unique reduced system, but a correct decision procedure for the same
closure. Tightening the RHS toward (P2) shortens reducts, makes more critical pairs join
trivially, and lets collapse retire more rules, so it is the lever on basis *size*. §3.3
measures how much that lever actually moves (none, on the stress graph, for a structural
reason).

---

## 2. The `(f (add x ..r1) (add y ..r2))` matcher bug, over concrete nodes

Pattern: `(rewrite (f (add x ..r1) (add y ..r2)) (g x))`. The scalar/rest vars may repeat or
differ; the bug is about node-var binding, not var identity. Regression inputs:
`ac_two_same_op_atoms.egg` (completion off), `ac_complete_nested_match.egg` (completion on).
This is our own e-matching machinery, not from the papers.

### 2.1 The nodes and the plan

`(let t1 (f (add (a) (b)) (add (b) (c))))` builds (class ids bracketed):

```
a,b,c   leaves           add1 = +{a,b} [A1]   add2 = +{b,c} [A2]   f1 = f(add1, add2) [F]
```

`add1`, `add2` are both `add` (same AC op) and both children of one `f`. The planner
schedules `f` first; because its two children are unbound it emits `ExtractChild` steps that
**bind the `add` node-vars** `n1`, `n2`, *before* the two `add` atoms are processed. So each
`add` atom finds its node-var already bound and emits a bound-node **re-join**
`ByRepr{nX} ∩ ByOp{add}` carrying an `atom_id` (keeping the semi-naive variant machinery,
which lives only on `Step::Join`), then a `DecomposeAC`:

```
1 Join nf <- ByOp f             2 ExtractChild n1=child(nf,0)   3 ExtractChild n2=child(nf,1)
4 Join n1 <- ByRepr{n1}∩ByOp{add}   5 DecomposeAC n1,[x],r1
6 Join n2 <- ByRepr{n2}∩ByOp{add}   7 DecomposeAC n2,[y],r2     8 end
```

Steps 2–3 bind `n1`, `n2` in enclosing frames; those bindings must live until subtree 4–8 is
fully enumerated.

### 2.2 The crash and the fix

`leapfrog_join` (old) did `env.set(target, key)` per key and an unconditional
`env.clear(target)` on exit. Step 5 enumerates sibling splits of `+{a,b}` (`x=a`, then
`x=b`), calling `run_step(6)` each time. On the first split, step 6's re-join on `n2` runs,
then clears `n2` on exit (the bug: `n2` was bound upstream by step 3, not by this join). On
the second split, step 6 reads `env.get(n2)` → `Match::get` → `unwrap()` on `None` → panic.
`n1`'s premature clear at step 4 is harmless (nothing re-reads it before step 1 re-extracts
it), which is why it takes *two* same-op AC atoms under one parent to surface; AC completion
exposed it by minting enough `add` nodes for the planner to choose this schedule.

Fix (`leapfrog_join`): save and restore the prior binding instead of clearing.

```rust
let prev = env.get_opt(target);   // Some(add2) for the re-join; None for a plain join
while join.is_valid() { env.set(target, join.key()); run_step(/* +1 */); join.next(); }
env.set_opt(target, prev);        // restore, not clear
```

Plain join: `prev == None`, reduces to the old set/clear. Re-join: the upstream binding
survives. Matcher-soundness fix, independent of completion. Committed `2501b32`.

---

## 3. Compliance with Kapur's algorithm

### 3.1 Correspondence table (our code ↔ Kapur 2023)

| Our code | Kapur 2023 | Match |
|---|---|---|
| AC node `+M` in class `c` = rule `+M → r(c)` | f-monomial rule `f(A₁) → f(A₂)` (§3) | ✓ |
| `monomial_cmp` (degree-lex), orientation guard | admissible ordering `≫_f`, orient `f(A₁) ≫ f(A₂)` (§3) | ✓ |
| `ab = multiset_lcm(m,a)`; reducts `(ab−m)⊎rhs_m`, `(ab−a)⊎rhs_a` | `AB = (A₁∪B₁)−(A₁∩B₁)`; critical pair `(f((AB−A₁)∪A₂), f((AB−B₁)∪B₂))` (Def 3.2) | ✓ (lcm = componentwise max = his `AB`) |
| disjoint partners skipped | "if A₁,B₁ disjoint, their critical pair is trivial" (§3) | ✓ |
| trivial-pair filter (normal forms equal ⟹ skip) | "nontrivial iff normal forms ... not the same" (§3) | ✓ |
| close pair = merge both normalized reducts | Lemma 3.3 (joinable critical pairs ⟺ locally confluent) | ✓ |
| `FLAG_AC_COLLAPSED` on LHS reducible by another rule | step 4(i): remove `l→r` whose LHS is reduced by new rule | ✓ (flag, not delete; equality preserved via the merged reduct) |
| dedup reducer/superposition set by (op, LHS) | step 2: "if equal, discard the equation" (keep one) | ✓ (duplicate *nodes* stay in `targets`, so their merges are not lost) |
| incremental (B): superpose only delta rules | step 3 + fn 3: CPs of the new rule vs existing, "incrementally ... instead of all critical pairs" | ✓ |
| termination backstop / antichain | Thm 3.4 (Dickson's Lemma on noncomparable LHSs) | ✓ |
| `min_monomial` best-effort RHS | step 4(ii) fully normalizes RHS (reduced) | **partial: §1.2 gap** |

### 3.2 The two deviations from "fully reduced", checked against ground truth

Kapur's output is the *unique reduced* canonical system (Thm 3.6): no rule's LHS or RHS is
reducible by the others. Two ground-truth checkers (`ac_invariants.rs`) measure how far we
are from that, brute-forcing the true values rather than the cheap proxies:

- `ac_min_used_nonminimal`: per (class, op), the true `monomial_cmp`-least same-op monomial,
  compared to the RHS completion actually uses.
- `ac_not_kapur_reduced`: rules whose LHS / RHS is `normalize_ms`-reducible by the *others*
  (multi-step), not merely by direct sub-multiset containment.

Both brute-force superlinearly, so they run only when the per-rebuild **basis-checks switch**
is on: `EGraph::set_basis_checks(true)` (or the `AC_BASIS_DUMP` env var, which seeds it at
construction). Default off; never on the production hot path.

The three features have matching control surfaces at each layer:

| feature | CLI flag | `.egg` directive |
|---|---|---|
| eval algorithm | `--use-semi-naive` / `--use-naive` (default naive) | `;; EVAL: naive\|semi\|both` (default both) |
| derive AC consequences | `--derive-ac-eqs` | `;; DERIVE_AC_EQS: on` |
| check basis properties | `--check-ac-basis` | `;; CHECK_AC_BASIS: on` |

`--derive-ac-eqs` off leaves sub-multiset enumeration in leapfrog matching intact but
skips completion. `--check-ac-basis` needs derive on to have anything to check; in
the egg harness `;; CHECK_AC_BASIS: on` additionally **asserts** the post-run basis is fully
reduced (`ac_min_used_nonminimal == 0`, `kapur_lhs_reducible == 0`), turning the diagnostic
into a test. `;; EVAL: both` runs the file under naive and semi-naive and asserts the same
outcome (the historical cross-check, now an explicit default).

**Deviation 1 (RHS minimality, §1.2): best-effort, measured a no-op here.** `min_monomial` is
maintained on merge only, so the RHS is oriented but not guaranteed the global minimum.
Measured: `ac_min_used_nonminimal = 0` at every round. Refreshing `min_monomial` at
recanonicalization (the natural fix) was implemented and lowered a stored min **zero times**,
because `monomial_cmp` is degree-first and a *child* merge preserves degree (`+{a,b,c}` with
`b~c` becomes `+{a,b:2}`, still degree 3). So recanonicalization can never lower a node's
degree, hence never produce a new degree-minimum that merge-time folding missed; the
degree-minimum is fixed entirely by class merges, which `fold_min_monomial` already captures. The
refresh was reverted (cost on the default `rebuild` path, zero benefit). Under a degree-first
order, `min_monomial`-on-merge already *is* the exact degree-minimum.

**Deviation 2 (duplicate-LHS rules): found by the ground-truth checker, now fixed.** The
weaker `reducible_pairs` proxy (direct strict containment) reported a clean antichain while
the true `kapur_lhs_reducible` was larger (round 0: 4 vs 9). The gap was *exact-LHS
duplicates*: congruent AC nodes that recanonicalized to the same monomial without being
hash-consed into one node, so the same rule `+M → r` appeared as several nodes (round 0 had
five nodes for `{9,22}→{75}`). The `reducible_pairs` check skipped them (it required
`lhs_i != lhs_j`); Kapur's step 2 discards them. Fix: dedup the reducer/superposition set by
(op, LHS), keeping the lowest node id. The duplicate *nodes* stay in `targets`, so their
collapses and any differing-RHS merges still fire; only the redundant *rules* (reducers and
superposition sources) are dropped. After the fix, rounds that reach a collapse fixpoint show
`kapur_lhs_reducible = 0` (§3.4).

Everything else (orientation, the superposition formula, the collapse trigger, disjoint and
trivial skipping, incremental CP generation, Dickson termination) matches Kapur exactly.

### 3.3 The observed growth on the diverging graph

On `investigate_completion` (seed 42, 30 leaves, 4 layers, 20 merges), trivial-pair filter,
incremental (B), and LHS dedup all on:

```
round:                 0    1    2    3    4     5
antichain_core:       64  122  204  392  642  1033    (≈1.6×/round)
nontrivial CP:        59  104  325  810 1915           (tracks the core)
trivial CP:            0  147  832 10878 35655         (the bulk, filtered out)
kapur_lhs_reducible:   9    0    0   57  370  1017     (see below)
```

- `trivial CP` is the bulk and is discarded; before the trivial-pair filter each minted
  spurious rule-nodes (node growth at rounds 3–4 was `+9094/+30155`, now `+1240/+2816`).
- Dedup shaved the duplicates (round 0 `active(rules)` for (B) 68→64, `crit(B)` 75→59) but
  the overall growth is essentially unchanged: duplicates were a *small* contributor. The
  bulk of `antichain_core` is genuinely distinct, irreducible rules. The stress graph makes
  many overlapping pure-sum classes; each overlapping pair is a legitimate Kapur
  superposition (Def 3.2) yielding a new irreducible rule. Dickson (Thm 3.4) bounds the
  antichain, but over a dense, deeply-merged constant pool the bound is large. This is the
  inherent cost of full AC congruence closure.
- The non-zero `kapur_lhs_reducible` at rounds 3+ is **not** a collapse defect; it is the
  documented within-round lag. Round N's congruence step recanonicalizes nodes into newly
  reducible forms *after* round N−1's collapse ran; they are collapsed in round N's own
  `(A′)`, not before round N's "pre" snapshot is taken. On a graph that actually reaches a
  fixpoint, this lag clears (§3.4). The earlier hypothesis that this residual was a collapse
  bug driving the growth is **not** supported: the growth is unchanged after the dedup fix,
  and the residual is transient per-round churn, not surviving reducible rules.

**Divergence is input-specific, not size-specific.** A sweep over a grid of stress configs
(`investigate_completion_sweep`) shows **10 of 11 converge**, including three at the diverging
config's size or larger (seeds 6, 123 at 30 leaves / 4 layers / 20 merges, seed 999 at
40/3/30), each in well under a second to a few seconds:

```
seed 1..8  (6..30 leaves):  CONVERGED   41 .. 1746 nodes
seed 6   (30,4,20):         CONVERGED   1746 nodes
seed 123 (30,4,20):         CONVERGED   2670 nodes
seed 999 (40,3,30):         CONVERGED   2003 nodes
seed 42  (30,4,20):         DIVERGED    (the only one; witnessed by investigate_completion)
```

So the blow-up is **not** a property of large or deep graphs in general; it is one
particular random instance (seed 42) whose AC equation set has a genuinely large canonical
basis. Most graphs of the same shape complete fine. This sharpens the §0.5 conclusion: a
scoping mechanism (growth guard / on-demand / degree bound) only needs to fence off the rare
pathological instance, not the common case.

### 3.4 The basis is fully reduced at a real fixpoint

The diverging graph never lets a round's recanonicalization settle, so its "pre" snapshots
always show in-flight churn. On a *converging* graph (`investigate_completion_small`, seed 7,
12 leaves, 2 layers, 5 merges), completion reaches a fixpoint in 3 rounds, and the
ground-truth checker reports, at **every** round and in the final dump:

```
ac_min_used_nonminimal = 0   kapur_lhs_reducible = 0   kapur_rhs_reducible = 0
```

So when collapse is allowed to run to a fixpoint, the active set is fully Kapur-reduced (both
sides irreducible) and every used `min_monomial` is the true minimum. The deviations of §3.2 are
the only ones, and both are accounted for: RHS minimality is a no-op under the degree-first
order, and duplicate LHSs are now deduped.

**Conclusion.** The code matches Kapur's algorithm on every essential point. Both
deviations from "fully reduced" are now accounted for by ground-truth measurement: RHS
minimality is best-effort but a no-op under the degree-first order (§3.2), and duplicate-LHS
rules are deduped (§3.2). At a real fixpoint the basis is fully Kapur-reduced (§3.4). The
per-round growth on the diverging graph is therefore the genuine size of the reduced
canonical basis on a dense, deeply-merged graph, not a collapse defect: the dedup fix did not
change it, and the residual `kapur_lhs_reducible` is within-round churn that clears at a
fixpoint. The open work is scoping *when* completion runs (growth guard, on-demand, or a
degree bound; plan §0.5), not strengthening collapse or `min_monomial` further. Completion stays
off by default until a scoping mechanism lands.
