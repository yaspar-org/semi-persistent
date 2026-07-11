# AC completion: pre-merge review debt (divergence budget + test debt)

Status: open, written 2026-07-09 for the PR #41 reviewer. These are the two reservations
from the merge assessment that are **not** fixed on the branch — stated here with current
state, why they matter, the concrete task, and acceptance criteria, so each can be tracked
to closure independently of the merge decision. Everything here is *debt on an opt-in
feature*: completion is off by default (`set_cc`), so none of it regresses mainline users;
all of it matters the day someone turns completion on in anger. Companion docs:
the Kapur-correspondence table in [../design/ac-completion-spec.md](../design/ac-completion-spec.md) §3 (what WAS fixed; the retired conformance plan is in git history),
[ac-completion-performance.md](ac-completion-performance.md) (the measurements cited here).

---

## 1. In-round divergence budget (the backstop granularity hole)

### Current state

`rebuild()` guards against a diverging completion with `MAX_COMPLETION_NODE_GROWTH`
(50 000 added nodes), checked **between** completion rounds (`egraph.rs::rebuild`, the
round loop). Inside one round, `cc_round` first *collects* every critical pair into the
`crit` vector — the (B) superposition scan, the Kapur §4 axiom pairs — and then closes
them all; nothing bounds the work of a single round.

### Why it matters (measured, not hypothetical)

Ground AC congruence closure is doubly exponential in the worst case (Kapur cites
Mayr–Meyer, [MM82]), and the cliff is razor-sharp: in the 2026-07-09 benchmark sweep, a
24-leaf instance with 10 random leaf-merges went from convergent-in-milliseconds shapes to
a round that minted **38 788 nodes and 19 967 rules**, whose successor round generated
**2 015 249 critical pairs** — more than ten minutes of wall time spent *inside* rounds
that the between-rounds node cap never got a chance to interrupt. So with completion on,
wall time is effectively unbounded even though the node cap suggests otherwise:
"terminates by Dickson's lemma" is a theorem about the limit, not about the bill.

### Task

Enforce the budget *inside* the round, with the same semantics the existing cap already
has (abort completion, keep the sound-but-incomplete congruence closure):

- Count nodes minted and pairs generated within `cc_round` (the `crit.push` sites and the
  `materialize` calls) against a budget; on exhaustion, stop the round and report it.
- The bail must **not** be mistaken for convergence: `rebuild` declares convergence only
  when a *full* round reports no change — a truncated round must short-circuit that (bail
  out of the completion loop entirely, as the node-cap path does today, never
  `changed = false`).
- Debug builds `debug_assert!` on the bail (as the node cap does); release builds log via
  `AC_COMPLETE_TRACE` and return. Make the budget a config knob (or env override) so tests
  can set it tiny.
- Soundness argument is unchanged: every merge made before the bail is justified; the
  loss is completeness only (Ch 14's trustworthy polarity).

### Acceptance criteria

- The measured pathological instance (24 leaves / 10 merges, seed 7 shape — regenerate
  from the perf-doc addendum's generator) terminates in seconds under the default budget,
  with a trace line reporting the truncation.
- A fixture with a deliberately tiny budget asserts: the run terminates, every *asserted*
  equality still checks (soundness), and completion reports the bail rather than
  convergence.
- The between-rounds cap remains as the outer backstop.

---

## 2. Test and verification debt (itemized)

Four items (two since closed — see the DONE markers), each documented at the point it was found (the adversarial-analysis session,
2026-07-09). All four describe **missing assertions**, not known-wrong behavior — where a
behavior could be probed, it was probed and found correct; the debt is that nothing pins
it.

### 2.1 PROOFS=true reconstruction across the new merge kinds — DONE (2026-07-10)

*(Closed by `egraph/tests/ac_matrix.rs`: every new mechanism — §4 axiom-CP merges, late
unit merges, late inverse pairs, cancelative merges — runs under all four
`(TRACK, PROOFS)` combinations, with class-level proof reconstruction asserted under
PROOFS and mark/restore round-trips under TRACK. One residual: `explain_deep` (deep
reconstruction descending into AC congruence premises) is not asserted across MSet/Set
nodes. Original text kept below.)*

**Current state.** The egg fixture harness instantiates `Interpreter<_, _, _, true,
false>` — every AC fixture, including all the new ones, runs proofs-OFF. The
`egraph_proof_test` suite (PROOFS=true, 26 tests) covers pre-existing merge paths. A CLI
`--proofs` smoke run of the late-unit-merge probe was clean, and the history-save ordering
was verified by code reading (`caches.rs::recanonize_node` copies the original span into
history *before* the shrunken, unit-dropped buffer is written back).

**Gap.** No test *reconstructs* (explains) a proof across the merge kinds this branch
added: (a) a unit-drop degeneracy merge (late `b = zero` collapsing `add(a,b)` to `a`),
(b) an axiom-critical-pair merge (`xor(a,c) = b` from `xor(a,b) = c`), (c) a
became-a-unit-sweep merge, (d) a completion materialize+merge chain ((A′) residual
substitution).

**Task.** Add `egraph_proof_test` cases building each scenario with PROOFS=true and
asserting the justification chain replays end to end. Acceptance: four tests, one per
merge kind, in the proofs suite; each `explain`-style reconstruction validates.

### 2.2 Basis checkers 1–2 scan only the MSet partition — DONE (2026-07-10)

*(Closed by the gate-test slice: `cc_basis_report` and checks 1–2 harvest both completion
partitions via `node_monomial_into`, check 2 normalizes in the op's count domain, and the
`basis_report_counts_set_completion_nodes` gate is live. Original text kept below.)*

**Current state.** `ac_invariants::cc_basis_report`, `cc_min_used_nonminimal` (check 1),
and `cc_not_kapur_reduced` (check 2) filter on `NodeRef::MSet` only, and check 2
normalizes with `normalize_ms` (the ℕ count domain) regardless of the op's clamp. Set
(ACI) rules are invisible to them, so `CHECK_AC_BASIS` under-asserts on ACI fixtures.
Check 3 (`cc_axiom_cps_nonjoinable`) already harvests rules over **both** partitions and
normalizes in the op's count domain — it is the template.

**Gap.** Kapur-reducedness and min-monomial minimality are unasserted for every Set-op
rule in the suite.

**Task.** Rebase checks 1–2 onto the check-3 rule harvest (`node_monomial_into` +
`class_rhs_into` over both partitions) and normalize in the op's count domain
(`normalize_set` / `normalize_nilpotent` / `normalize_ms` by clamp). Extend
`ac-completion-spec.md` §1 (P1–P4), which is currently stated for `+`-monomials only.
Acceptance: an ACI `CHECK_AC_BASIS` fixture demonstrably checks a nonzero Set-rule count
(assert via the report's rule tally), and the whole suite stays green.

### 2.3 No randomized differential oracle for ACI / nilpotent ops

**Current state.** `ac_vs_rules.rs` generates only plain binary `add` instances (NATIVE
`:assoc-comm` vs. a rules encoding of A+C). The Kapur §4 semantics — clamps and axiom
critical pairs — are covered by handwritten fixtures only.

**Gap.** This harness is exactly the instrument that would have caught the two §4
completeness gaps (the missing §4 axiom critical pairs, fixes W3a/W3b) mechanically, and it
currently cannot exercise them. Every future change to the axiom-pair generation or the
clamp domains lands without randomized cross-checking.

**Task.** Extend the `Instance` generator with an op-algebra parameter; per algebra, the
RULES side gets the corresponding oracle prelude (`(rewrite (Or x x) x)` for ACI;
`(rewrite (xor x x) (e))` + unit handling for nilpotent order 2; plain A+C rules in both
cases) and the NATIVE side the corresponding tags. Compare the derived equalities as the
plain-`add` harness does. Nilpotent needs a bounded saturation and care that the rules
encoding actually reaches the unit normal forms — treat oracle divergence as
inconclusive-and-investigate, not as an automatic native bug. Acceptance: N seeds × 3
algebras in the `--ignored` suite, green; a deliberately reintroduced axiom-pair
regression (e.g. skip the idempotent arm) is caught by at least one seed.

### 2.4 Determinism and uniqueness (Kapur Thm 3.6) are untested

**Current state.** With the admissible order fixed (conformance W1), Thm 3.6's hypothesis
holds and the reduced basis is unique **for a fixed constant order**. In the e-graph the
constant order is class-id assignment order, i.e. *input insertion order* — so uniqueness
across permuted inputs is **not** expected at the basis level, and that relativity is easy
to misread as nondeterminism.

**Gap.** Nothing asserts (a) *determinism*: the same program yields the identical final
basis on repeated runs (the clone-free dedup made the last order-dependent structure — a
`HashSet` — go away; nothing pins that), nor (b) *semantic invariance*: permuting input
declaration order changes ids and possibly the basis but must not change any derived
equality.

**Task.** Two tests: (a) run a rule-heavy program twice, assert the `cc_basis_report`
dumps are identical; (b) run a program and a permutation of it, assert every `(check ...)`
outcome agrees. Document the id-relativity of Thm 3.6 uniqueness in the design chapter
(one paragraph, next to the 2026-07-09 ordering correction). Acceptance: both tests in
the suite; the design note landed.

### 2.5 Housekeeping — DONE (2026-07-10): CcSnapshot kept and made representation-agnostic

*(Closed by the gate-test slice: the snapshot covers both partitions and the
`cc_snapshot_counts_set_completion_nodes_if_kept` gate is live. Original text kept below.)*

`cc.rs::CcSnapshot` is production-dead: `cc_round` finds partners through the class
use-lists, and the snapshot is built only by its own unit tests. It duplicates the
partner-search logic and can silently drift from it. Decide: wire it in (if the frozen
per-round index is wanted for the S3b worklist rewrite) or delete it. Either resolution is
a small diff; the danger is only in leaving it ambiguous.

---

## 3. Residual gaps of the cancelative/group facets (added 2026-07-10; Abelian-group work POSTPONED INDEFINITELY, decision 2026-07-10)

The §5 core landed (cancel-close, cancelative disjoint superposition, per-constant
closure; inverse-pair cancellation). Three residuals for the reviewer to track:

- **Full Abelian-group completion (Kapur §5.4)** is not implemented: no standardized
  rules, no gcd/triangular inter-reduction. Inverse handling is pair-level only — e.g.
  `2a = b ∧ 3a = c ⊢ c = a + b` needs group normalization, not pair cancellation.
  **POSTPONED INDEFINITELY** (operator decision 2026-07-10): this is recorded for
  completeness, not tracked as pending work. The gate-level `:inverse` support that
  shipped (pair cancellation) stays.
- **Inverse pairs formed by late merges, with completion OFF**: the cancellation probe
  lives in `add` and `cc_round`; the canon layer cannot probe. `add(a, x)` where `x`
  later merges into `neg(a)`'s class collapses to the unit only when completion runs.
  (Analogous to the pre-W2 unit-drop hole; the fix would be a degeneracy-style post-pass
  in `rebuild_congruence` that probes inverse pairs after recanonize.)
- **Per-constant closure is pool-relative**: §5.2(iii)(b) pairs are generated over the
  op's summand pool at round time; a constant introduced later is covered by the next
  full round that sees it (the standard delta net), but a *proof* that this incremental
  policy reaches Kapur's fixed-signature closure at every `check` boundary is an argument
  in a comment, not a test. A fixture that interleaves late constant introduction with
  checks would pin it.

---

## 4. Salvaged open item: A (associative-only) completeness is a conjecture

(Salvaged 2026-07-10 from the retired `ac-congruence-completeness-plan.md` §0 item 3.)
A-operators canonicalize by flattening into a sequence, and the design claims
associativity is decided by that alone (no commutativity ⟹ no sub-multiset overlap to
superpose). This is asserted, not tested: there is no A-operator completion test and no
proof that flattening is complete for the ground associative word problem in this
encoding. Treat "A is complete on its own" as a conjecture pending a test or a citation.
