# AC Congruence Completeness — Implementation Plan

Status: **draft for review.** Nothing in this plan has been implemented yet. It
turns the design spec into a concrete, code-grounded implementation strategy for
this branch (`feature/ac-congruence-completeness`).

- **What/why** (problem, fix, proof sketch): [AC Congruence Completeness](../design/ac-congruence-completeness.md).
- **Status & verification staging** (the canonical summary): [A3 Future Work](../design/A3-future-work.md#ac-congruence-completeness-via-critical-pairs).
- **Task breakdown** (the checklist this plan feeds): [tasks](ac-congruence-completeness-tasks.md).

This plan does **not** restate the theory. It records (1) where the new code
lands, (2) the one architectural decision that the spec leaves open against the
real code, (3) the net-new primitives, and (4) the commit sequencing and test
strategy. Read the spec §6–§9 first.

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
- AC **flattening** of nested same-op terms (e.g. `+(a, +(b,c))` → `+{a,b,c}`).
  This is a known separate gap ([ac-flattening TODO]) and is *not* part of this
  fix. **Caveat below in §6** — it interacts with correctness of the partner search.
- Saturation-loop termination. We only claim each single completion pass over the
  current finite AC-node set terminates (spec §10, Dickson). Productive user rules
  can still diverge; that is the rule set's concern.

[ac-flattening TODO]: ../design/09-pattern-matching.md

---

## 2. The architectural decision the spec leaves open  ⚠️ NEEDS SIGN-OFF

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
        changed  := ac_complete_round(snapshot)   # (A)+(B): materialize nodes, push merges to worklist
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
| Canonicalize a fresh multiset (find+sort+sum-mult) | `ACCanon::canonize` | `src/canon.rs:87-115` |
| Insert/probe an AC node, get its class | the `add`/`add_ac` path | `src/egraph.rs:320-336`, `src/node_store.rs:241` |
| Merge two classes, schedule rebuild | `EGraph::merge` / `merge_justified` | `src/egraph.rs:374-392` |
| AC op identification | `match OpKind::AC { .. }` via `ops.info(op).kind` | `src/registry.rs:29-63`, `:256` |

Net-new (none of these exist today — confirmed by the code map):

1. **Multiset algebra primitives** over `&[(G, Multiplicity)]` (sorted-by-`G`, the
   canonical AC child form): `multiset_disjoint`, `multiset_intersect` (or just a
   `⊆` test for (A)), `multiset_subtract` (`msub`), `multiset_union`,
   `multiset_lcm`. Today the only subtract is inline multiplicity-mutation in the
   matcher (`src/ematch.rs:742,788`); it is **not** a reusable helper. Write these
   as standalone functions on the canonical pair-slice form, unit-tested in isolation.
2. **An AC-op iterator / filter.** There is no `is_ac()` and no iterator over
   registered AC ops; `OpRegistry` exposes `len()`/`info(id)` only (`src/registry.rs:131,256`).
   Add a small helper that yields op ids whose `info(op).kind` is `OpKind::AC{..}`.
3. **The AC-node partner snapshot** (§5) and **the completion round** itself
   (`ac_complete_round`), per Option A.

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
ac_complete_round(snapshot) -> changed:
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
  sort, sum multiplicities — `ACCanon::canonize`), so we never create a
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

## 8. Commit sequencing

Each step builds and tests green before the next. Maps to [tasks](ac-congruence-completeness-tasks.md).

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

## 10. Open questions for review

1. **Option A vs B** (§2) — confirm A.
2. **Flattening** (§6) — land flattening first, or ship with the scoped completeness
   claim? Recommend: ship scoped, flatten as a separate follow-up, state the bound.
3. **Snapshot cost** (§5) — accept per-round full snapshot rebuild for v1? Recommend yes.
4. Anything to add to the worked-example test set beyond §4a/§4b/§5b?
