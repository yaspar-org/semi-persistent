# AC Congruence Completeness — Task Breakdown

Status: **draft for review.** Companion checklist to the
[implementation plan](ac-congruence-completeness-plan.md); theory in the
[design spec](../design/ac-congruence-completeness.md); status summary in
[A3](../design/A3-future-work.md#ac-congruence-completeness-via-critical-pairs).

Each task is one reviewable commit (or a tight cluster), builds and tests green
before the next. **Blocked on the two review decisions in plan §2 (Option A) and §6
(flattening).** Do not start T4+ until those are signed off.

Legend: ☐ not started · ⊘ blocked on review · → depends on.

---

## Foundations (no e-graph state — safe to start once Option A is confirmed)

### T1 — Multiset algebra primitives  ☐
Add pure helpers over canonical AC child slices `&[(G, Multiplicity)]` (sorted by
`G`, multiplicities summed — the form `ACCanon::canonize` produces, `src/canon.rs:87`):
- `multiset_disjoint(a, b) -> bool`
- `multiset_subset(a, b) -> bool`  (is `a ⊆ b`, for the (A) branch)
- `multiset_subtract(a, b)` → `a − b` (clamp at 0; assumes `b ⊆ a` for the substitution use)
- `multiset_union(a, b)` → `a ⊎ b` (sum multiplicities)
- `multiset_lcm(a, b)` → `(a ⊎ b) − (a ∩ b)` = per-element max multiplicity

**Tests:** disjoint/overlap/containment cases; lcm of `{a,b}` & `{b,d}` = `{a,b,d}`;
`subtract` then `union` round-trips; multiplicity > 1 cases. Pure unit tests, own module.
**Acceptance:** `cargo test` green; no e-graph dependency.

### T2 — AC-op iterator helper  → none  ☐
Add a helper yielding registered op ids with `OpKind::AC{..}` (`src/registry.rs:29-63`;
registry exposes only `len()`/`info(id)` at `:131,256` today — no `is_ac`, no iter).
**Tests:** a fixture registering AC + ACI + A + Normal ops returns exactly the AC ids.
**Acceptance:** green; does not misclassify ACI as AC.

---

## Search infrastructure

### T3 — AC-node partner snapshot  → T2  ☐
Build a per-round snapshot: `by_contains_ac` (child class repr → AC nodes of op `f`
containing it) and `by_op_ac`, restricted to AC ops, skipping `FLAG_SUBSUMED`.
Mirror the variadic `by_contains` slice of `IndexStore::build_from`
(`src/index.rs:135-153`) but drop `by_repr`/`by_child_pos` and non-AC ops (plan §5).
**Tests:** reuse/extend the `by_contains_variadic` fixture (`src/index.rs:406`);
assert a node with children `{a,b}` appears under both `a` and `b` and not under a
disjoint class.
**Acceptance:** green; snapshot contents match a brute-force reference over `ac_children`.

---

## The completion steps (⊘ blocked on plan §2 Option-A sign-off)

### T4 — (A) inter-reduction in `rebuild`  → T1, T3  ⊘
Wire the completion round into `rebuild()` per Option A (plan §2, §4): after the
existing worklist closure drains, build the snapshot (T3), and for each AC node
`+M=d` and partner `+A=a` with `A ⊆ M`, materialize `+((M−A) ⊎ {a})` via the
`add_ac` path (NOT in-place recanonize — span can't grow, `src/caches.rs:449`),
`merge` with `d`. Push changes back through the worklist; loop to fixpoint.
**Tests:** spec §4a — assert `+(a,b)=c`, `+(a,b,d)=e` ⇒ after `rebuild`,
`find(e) == find(+(c,d))`. Negative: disjoint sums derive nothing.
**Acceptance:** green; the §4a equality is derived; no spurious merges in existing
`ac_congruence`/`ac_multiplicity_no_false_collision` tests.

### T5 — (B) superposition / critical pairs  → T4  ⊘  ⚠️ NEEDS collapse+ordering (T5b)
Add the overlap branch: for partners that overlap but neither contains the other,
build `AB = lcm(M, A)`, **normalize** both reducts `(AB−M)⊎{rm}` and `(AB−A)⊎{ra}` to
normal form (where `rm`/`ra` are the partners' **minimal-monomial** RHSs, NOT bare
class ids), merge if distinct. Guard self-pairs and symmetric double-processing.
**Tests:** spec §4b — `+(a,b)=c`, `+(b,d)=e` ⇒ `find(+(c,d)) == find(+(a,e))`.
Spec §5b cancellation (already green from T4 — it is an (A) case). Confirm (A) is the
`A⊊M` special case.
**Acceptance:** green; §4b derives **and converges** (no node-count blowup — see T5b);
existing AC differential tests (`src/saturate.rs:1373-1908`) still pass.
**NOTE:** the naive form of this (merge both raw reducts, no collapse/normalize)
**diverges** (~5x nodes/round) — see T5b and design §6b. T5 is not complete without T5b.

### T5b — Collapse + orientation to make (B) converge  → T5  ⊘
The three load-bearing corrections from design §6b, without which (B) diverges:
1. **Collapse:** on `A ⊊ M`, after the (A) merge, mark `+M` `FLAG_SUBSUMED`
   (`EGraph::subsume`) so it leaves the active set → active LHSs stay a Dickson
   antichain → termination. "Retire" = subsume, never delete (nodes immutable + needed
   for rollback).
2. **Normalize-before-materialize:** `normalize_ms` reduces every reduct to normal form
   against ALL current rules (incl. same-round) before it becomes a node.
3. **Orient + minimal-monomial RHS:** degree-lex monomial order (`monomial_cmp`); each
   rule is `larger-monomial → its-class-minimal-monomial`; substitute the minimal
   monomial over existing constants, NEVER a bare class id as a fresh atom (that grows
   the constant pool every round — the actual explosion).
**Tests:** §4b converges with bounded node growth; a multi-rule input where `|active|`
plateaus near input size (instrument via `AC_COMPLETE_TRACE`); the two-rule
hand-checkable example from design §6b (`{a,b,c}→s, {a,b}→t` ⇒ canonical 2-rule system).
**Acceptance:** all completion egg tests green under both strategies; no `>50k`-growth
backstop tripped; `|active|` does not grow unboundedly on any test input.

### T6 — Fixpoint, eval-strategy, rollback, and proof-path hardening  → T5  ⊘
Harden the round loop and prove the evaluation-strategy interaction (plan §2b):

- **Joint fixpoint (R2):** multi-round convergence (a merge in round k creates a node
  that pairs in k+1), exit only when a whole round adds nothing (plan §4).
- **Logged-paths invariant (R1):** assert completion only mutates via `add`/`add_ac`
  → `register_if_fresh` and `merge`, so every product lands in `touched`. No path
  that inserts a node or unions classes while bypassing the `touched` log.
- **Semi-naive differential (HARD REQUIREMENT, plan §2b):** every completion-derived
  equality must be found under *both* `saturate` and `saturate_semi`. Include the
  **merge-only delta** case explicitly — the §4b example where completion merges two
  *pre-existing* nodes (`+{c,d}`, `+{a,e}`) and creates no fresh node; assert a rule
  keyed on the merged class still fires under semi-naive. Use the differential idiom
  in `src/saturate.rs:1373-1908`.
- **Subsumed-non-matchable (design §6b):** a node collapsed by completion
  (`FLAG_SUBSUMED`) must not be bound by any user pattern thereafter. The matcher reads
  only through `IndexStore`, which skips subsumed — but add an explicit test: subsume a
  node via completion, then a rule whose LHS would match the subsumed multiset must NOT
  fire (mirror of `subsume.egg`). Guards against any future matching path that bypasses
  the index. Also assert the collapsed node's *equality* still holds (class unchanged).
- **Rollback:** semi-persistent restore interaction (`rebuild_after_restore`,
  `src/egraph.rs:1055`) — completion-created nodes restore correctly; `touched`
  cleared on restore (`src/egraph.rs:596`); `FLAG_SUBSUMED` set by collapse is rolled
  back with the node store (a node subsumed after a `mark` is un-subsumed on `restore`).
- **PROOFS path:** new merges carry a justification (`merge_justified`,
  `src/egraph.rs:394`); a PROOFS-on run explains a completion-derived equality.

**Acceptance:** green incl. PROOFS build; **naive and semi-naive agree on every
completion-derived equality, including the merge-only case**; rollback round-trips;
loop provably halts on the test inputs.

---

## Verification (Verus — soundness only; Lean completeness is a separate milestone)

### T7 — Verus soundness invariant  → T6 (extension); baseline can precede  ☐
(1) Establish baseline invariant on today's recanonize-only `rebuild`: union-find ⊆
ACCC(S) (A3: provable now). (2) Extend it to cover (A)/(B): each materialize+merge
preserves the invariant (both reducts equal `+AB`; spec §12 soundness bullet).
Reuse the workspace `vstd::multiset` + union-find modeling (A3).
**Acceptance:** Verus verifies the extended invariant on the real `rebuild`.
**Note:** do NOT attempt confluence/termination metatheory in Verus (A3 "why split").

---

## Docs

### T8 — Status & caveat updates  → T6  ☐
- Flip A3 status from "Planned / not implemented" to reflect what landed.
- Fold the **flattening caveat** (plan §6) into the design doc — state whether the
  completeness claim is scoped to already-flat node sets or flattening landed first.
- Record the **Option-A decision** (plan §2) in the design doc §9 (reconcile the
  "in rebuild()" wording with the snapshot-owned-by-rebuild reality).
- Link this plan + tasks from A3 and the design doc.
**Acceptance:** docs match shipped behavior; no stale "not implemented" claims;
the §9 pseudocode and the real architecture agree.

---

## Follow-up milestone (not gated on T1–T8)

### L1 — Lean abstract completeness theorem  ☐
Newman's Lemma + Dickson WQO + critical-pair lemma on the abstract `(P,R)` model
(spec §10, §12), parameterized to transfer to the implementation by refinement.
Tracked separately; A3 verification staging step 3.

### P1 — Incremental / delta-scoped completion search  ☐
Replace per-round full snapshot rebuild (plan §5) with `touched`-keyed incremental
maintenance: pair an AC node only when it or a partner is in the round's delta.
This is the component that does **not** inherit semi-naive's delta speedup in v1
(plan §2b "Efficiency") — completion re-scans all AC pairs every `rebuild`
regardless of strategy. Pure performance; spec §9 says explicitly not a correctness
requirement. Gate on the T6 differential test staying green.

---

## Dependency graph

```
T1 ─┐
    ├─► T4 ─► T5 ─► T5b ─► T6 ─► T7(extend), T8 ─► L1
T2 ─► T3 ─┘                                  └─► P1
```

T5b (collapse + orientation) is mandatory: T5's (B) does not converge without it.

T7 baseline and L1 design can proceed in parallel with the coding tasks; their
*extension/transfer* halves depend on T6.
