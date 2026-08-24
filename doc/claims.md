<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Claims and evidence

This is the central inventory of live headline claims. It records the strongest
statement supported by the named proof, test, or benchmark. It is not a
mechanically complete inventory of every sentence in the repository.
[`artifact.md`](artifact.md) gives reproduction commands.

Evidence labels:

- **proved**: the stated postcondition is machine-checked, subject to the
  documented trust boundary;
- **measured**: a named finite test or benchmark supports the statement at its
  recorded inputs;
- **code-derived**: the statement follows from the current loop and
  data-structure shape, but is not a machine-checked cost theorem;
- **argued**: a prose argument exists but is not machine-checked;
- **historical**: evidence about a retired implementation or an earlier
  campaign, retained for traceability rather than cited as current behavior.

## 1. Semi-persistent containers

| claim | evidence | scope |
| --- | --- | --- |
| Restore reproduces the marked abstract state | **proved** | `containers-verus`, 1,701 verified conditions, 0 errors; trust boundary in `containers-verus/doc/design/02-trust-boundary.md` |
| The executable snapshot representation uses frame metadata plus sparse negative diffs rather than a deep copy | code + **proved protocol** | the proof models deep-copy snapshots in ghost state and proves replay equivalence; it does not prove allocator byte counts |
| `InlineStore::mark` is O(p), where p is the number of cells captured by the previous frame | code + **measured** | `prepare_mark` clears exactly the tags named by that frame's diff |
| `ParallelStore::mark` is O(w), where w is the number of materialized capture words | code + **measured** | includes high-water words retained after shrink; it is not unconditionally O(1) |
| `InlineStore::restore` is O(b + k + r + p) | code-derived | b fork-history links, k replayed diff entries, r cells regrown after pops, and p surviving-parent diff entries whose inline flags are restored; Verus proves functional refinement, not a machine-cost theorem |
| `ParallelStore::restore` is O(b + k + r + p + w) | code-derived | the same work plus clearing w materialized capture words; payload destruction and higher-level cache repair are outside this vector bound |
| Const-gated `TRACK` work is absent when `TRACK=false` | compiler-enforced + **measured** | tracking writes and branches whose condition is the const generic are eliminated; empty diff/frame/fork fields and general runtime guards remain |
| The project-local verified sources contain no executable `admit()` or `assume()` calls | **proved by gate** | all three verified crates are scanned in CI; source scanning and ordinary Verus verification are separate |
| The container trust boundary is 27 `external_body` items by default and 32 with `literal-types` | **proved by gate** | every item is enumerated in the trust ledger |
| 33 public partial functions remain and all are allowlisted | **proved by gate** | `check_partial_api.py` |
| The verified and legacy reference containers agree on the tested shared traces and selected layouts | **measured** | `containers-conformance`, including direct randomized `UnionFind`/`EClasses` differentials and proof-path reconstruction; scope and known differences are documented in `containers-conformance/BASELINE.md` and `containers-verus/doc/design/egraph-class-layer.md` |
| The e-graph runs on `containers-verus` | compiler-enforced | Cargo aliases it as `semi-persistent-containers`; the legacy `containers` crate is only a conformance/performance reference |

The semi-persistent source-of-truth structures compose from the shared vector
and diff protocol. Transient hash maps, sorted indexes, arenas used only as
scratch, and other derived caches need not be semi-persistent; they are
reconstructed from the source of truth after restore.

## 2. E-graph engine

| claim | evidence | scope |
| --- | --- | --- |
| A/AC/ACI operators use canonical sequence/set/multiset representations rather than rewrite encodings | code + **measured** | algebraic fixtures and native benchmark columns |
| Every `rebuild()` return is at least plain-congruence-closed | code + tests | this is the default guarantee |
| Eager AC/ACI completion is opt-in | code + tests | `--derive-ac-eqs`; only `CompletionOutcome::Converged` reports an unchanged joint completion round |
| Lazy AC/ACI completion is real and opt-in | code + tests | `--lazy-ac-eqs`; a failed plain equality check runs goal-directed completion in a shared mark/restore transaction |
| Completion can stop soundly without full AC closure | code + tests | `Disabled`, `GoalMet`, and `AbortedGrowthLimit` do not claim a complete AC/ACI fixpoint |
| AC matching emits only sound maximum-partition bindings | **measured** | focused fixtures and deterministic regressions; no independent generated oracle or completeness proof |
| AC decomposition avoids multiplicity sub-count and residual-submultiset enumeration | code + **measured** | with `k` unbound scalar variables and `d` distinct children, the candidate assignment tree is at most `d^k` before pruning, independent of numerical multiplicity |
| Leapfrog gives worst-case-optimal multiway intersection for the relational join component | algorithm + tests | this does not make the complete AC matcher worst-case optimal |
| Backtrack cleanup clears only variables it bound | measured | regression fixture; the defect it fixes is recorded |
| Proof-specific work is absent when `PROOFS=false` | compiler-enforced + code | the union-find retains two `None` proof options and the node store retains 13 `None` history options; no proof/history vectors are allocated and const-gated recording/history work is eliminated |
| Batch proof export uses one O(n) Euler-tour index and O(1) LCA queries | code + tests | `--proofs --dump-proofs FILE`; path output remains linear in the number of emitted proof steps |
| The proof dump emits one deterministic proof-path record per e-node | **measured** | format `semi-persistent-proof-dump v1`; records are paths to the current representative, not independently replay-checked certificates, and some algebraic labels do not yet carry sufficient premises for such a checker |
| Full AC/ACI completion completeness is conditional | **argued** | requires completion to run and converge; the proof is a paper argument, not a verified theorem |

| Across all 17 translated benchmarks, egglog/ours was 1.19x rules-naive and 1.11x rules-semi | **historical** | `final-r6`, source snapshot based on `8f041483`; geometric mean of per-benchmark process-wall ratios |
| Across the 11 native translations, egglog/ours was 2.56x native-naive and 2.69x native-semi | **historical** | `final-r6`; `acgen` is deliberately included and strongly favors native AC |
| Explicit-rule `acgen` measured 0.12x/0.05x while native AC measured 100x/111x | **historical** | same campaign and recorded binaries; descriptive evidence for that snapshot |

Campaign `final-r6` retains all 750 timed samples, aggregate dispersion and
structural metrics, exact binary hashes, source state, commands, timestamps,
and machine metadata. It predates later implementation changes, ran under
substantial background load, and reports process medians without bootstrap
confidence intervals. It is historical evidence for its recorded binaries,
not a release-performance result for the current branch. A current comparison
must rerun both engines from one source state under Criterion and retain its
bootstrap confidence intervals.

## 3. Abstract domains

| claim | evidence | scope |
| --- | --- | --- |
| The enabled `u8`, `u16`, `u32`, and `u64` abstract-domain instances satisfy their stated Verus obligations | **proved** | ordinary verification reports 994 verified conditions and 0 errors; `u128` is disabled |
| The source contains no `admit()` or `assume()` | **proved by gate** | includes the formerly admitted `ExecUnum::{add,mul,from_interval}` obligations |
| The separate Rust mirror fuzz suite passes 32 tests | **measured** | randomized and exhaustive finite evidence; it mirrors rather than executes the Verus definitions |
| `ReducedProduct::add` no longer depends on an admitted `ExecUnum::add` contract | **proved** | the dependency is now discharged transitively |

## 4. Anti-unification

### Supported claims

| claim | evidence | scope |
| --- | --- | --- |
| Pair-mode root Exact agrees with the definition of `OPT` on enumerable fixtures | **measured** | `au_oracle.rs`; small finite acyclic instances only |
| Pair-mode search admits finite derivations through e-class cycles that side-based filters reject | code + **measured** | `(8, 3)` reproducer covers root Exact, UCT, expansion hybrid, and rollout hybrid; depth-128 cyclic-chain regression covers Exact and UCT |
| Pair-mode root Exact stabilizes by bounded synchronous relaxation over reachable ordered class pairs | **argued** + measured | pair-cycle-erasure argument and runtime assertion; the `N`-state bound is not machine-checked |
| One `cycle_mode` parameter is honored by root Exact, UCT, expansion hybrid, and rollout hybrid | code + **measured** | cross-mode reproducer checks distinct side/pair terms and qualities; sessions reject a mismatched UCT mode |
| Contextual `Completion::Exact` is policy-relative, not a global-certificate bit | code + **measured** | side-mode Exact and every UCT mode close their configured contextual graph; side-mode regressions are worse than pair mode |
| The lexicographic objective order and additive monotonicity lemmas hold | **proved** | `au-verus::objective` |
| A preselected action that is in the action set and no worse than every action is a set minimum | **proved, conditional** | `lemma_preselected_action_is_min`; minimality is a precondition, not a conclusion about the solver |
| Any function satisfying the current recurrence lower-bound inequalities is below every represented positional term pair | **proved** | `lemma_recurrence_below_every_pair`, induction on combined term height |
| The model can decompose and assemble represented positional terms | **proved** | `model_wf` clauses and `lemma_structural_terms_are_represented` |
| Minimum-size represented terms give a Plotkin result no worse than hiding both terms | **proved** | `lemma_generalize_has_no_worse_witness` |
| Bounds, pruning, transport, flags, delegation, and representation independence agree with their finite oracles | **measured** | named AU property/differential suites |
| Saturation separates the tested paraphrases from the planted disagreements | **measured, pilot** | `au_formalization.rs` and `au_formalizer_pilot.rs`; not a population study |

The current Verus model is positional Plotkin anti-unification. It does not
model the finite ordered-pair graph, depth-indexed relaxation,
pair-cycle-erasure, production AC/ACI transport, identity padding, cycle
contexts, pruning, MCGS, or exact/MCGS delegation.

### Claim not established

No current theorem states or implies `D*(A, B) = OPT(A, B)`. In particular,
`satisfies_recurrence_lower_bounds` contains inequalities only. The
constant-zero quality function satisfies them but generally is not attainable.
The structural representation lemma has no quality postcondition, and the
action-minimum lemma assumes that the chosen action is already least.

The prose `D* = OPT` argument in chapter 19 is therefore an unmechanized target
theorem. The Rust pair-mode exact solver's cycle-global optimality within its
supported action domain is supported by the pair-cycle-erasure argument and
finite tests, not a universal proved claim. Side-mode Exact makes only a
policy-relative contextual claim.

### Roadmap to `D* = OPT`

1. Define the finite reachable ordered-pair action graph and the constructive
   depth-indexed recurrence `D_d`.
2. Prove that each round computes and attains the minimum over derivations of
   depth at most `d`.
3. Prove pair-cycle erasure and derive stabilization within `N` reachable pair
   states, matching `exact_fixed.rs`.
4. Strengthen structural assembly with recursive child-witness premises and a
   Plotkin-quality postcondition, and map every represented term pair to an
   action-graph derivation.
5. Combine attainability (`OPT <= D*`) with the existing lower-bound direction
   (`D* <= OPT`) in one exported theorem whose postcondition states equality.
6. Separately refine the positional theorem to AC/ACI transport and
   multiplicities, units, bounds, and certificate scopes. Side-based cycle
   filtering remains an explicitly smaller optimization domain.

The maintained theorem, refinement, and validation acceptance criteria are in
[`egraph/doc/future/au-correctness-and-validation.md`](../egraph/doc/future/au-correctness-and-validation.md).

## 5. Open and retracted claims

- Matcher completeness is open; soundness is the supported claim.
- AC/ACI completion completeness is argued only for a converged completion on
  its stated fixed-pool model.
- The actionable matcher proof and combined rules-plus-completion termination
  obligations are in
  [`ac-completion-limitations.md`](../egraph/doc/future/ac-completion-limitations.md).
- `lb_pair` admissibility and edge-count sharing are exhaustively tested only
  on the recorded small instances.
- Pair-cycle erasure and the `N`-round pair-mode Exact bound are prose arguments
  with regressions, not verified theorems.
- Transport representation pairs with a margin above `u32::MAX` are omitted
  from the certified action domain.
- Contextual closure is exact only for its configured action graph; side modes
  may be worse than the global finite-term optimum.
- The formalizer measurement is a pilot from one system under fixed policies.
- Delegation is not generally profitable. It helps when rollout error is
  concentrated in exact-solvable subproblems and loses when the error is at the
  root.
- The `dec` family is not a hardness family.
- The old sparse span-table install-cost claim is retracted. The current
  stamped-arena tradeoff is recorded in
  [the index design](../egraph/doc/design/06-index.md#the-span-arena);
  revival requires the evidence in
  [the runtime validation specification](../egraph/doc/future/performance-validation.md#6-evidence-triggered-work).

## 6. Historical documents

`doc/paper/egraphs2026.tex` is the immutable source of the already-published
short paper. Its O(1)-snapshot, zero-overhead, LCA-integration, size, and other
implementation statements describe that publication and are not current
claims. The future paper is `doc/paper/draft.md`.

Campaign records under `doc/benchmarks/records/campaigns/` are historical
evidence. Their numbers remain valid for the source snapshots and binaries they
name. No retained cross-engine campaign currently measures the branch tip.

The project-local no-admit gate does not remove dependency axioms from the
trusted base. With pinned `vstd` `0.0.0-2026-08-02-0125`, global
`--no-cheating` stops in `vstd` before checking these crates because that
dependency contains admitted specifications. The supported statement is
therefore ordinary Verus verification plus a project-source scan, subject to
the documented Verus/`vstd` trust boundary.
