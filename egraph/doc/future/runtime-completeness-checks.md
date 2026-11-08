# Runtime Completeness Checks Derived from the Lean Theorems

This note designs a check that each run of the e-graph can perform to establish that
its result is complete: that completion derived every equality the theory entails among
the classes present, and that saturation applied every match modulo the theory. It is a
design for future work, not a description of the engine; nothing here is implemented.

## 1. Principle

The Lean completeness theorems have the form "if these hypotheses hold at the final
state, the state is complete":

- `completion_complete_at_convergence` (`proofs/lean/SemperProofs/CC/Assemble.lean`) and
  its law variants take the hypotheses bundled in `CompleteHyps`
  (`CC/Bridge/Modulo.lean`): `I0Active`, `hcanon`, `RoundFixed` (`nf_present`,
  `lhs_reduced`, `cp_joinable`), `hlaw`, `hnf_ax`, `hcp_ax` (the critical pairs involving a
  law instance, `AxiomCP`; the rule-rule pairs follow from `RoundFixed` by `hcp_of_fixed`), a
  minimal-monomial history (`slots`), and for
  a cancellative operator lattice closure (`hlat`: active nodes whose count vectors differ
  by a member of the lattice the equations span are in one class).
- `saturation_modulo_complete` (`Final/Main.lean`) adds the matching hypotheses:
  `MatchersOK`, `RulesWF`, `RoundOK`, `EmitsAll`, `AChain`, and the fixpoint `A.R.Unchanged`.
  `MatchersOK` is a theorem for the adaptive scheduler (`matcherOK_engine`); for a static plan
  it is `SchedA` of the compiled plan (`matcherOK_static`), the check below.

If a run checks the hypotheses on its final state, the theorem gives completeness for
that run. This is certificate checking: the run produces a state, and a checker
confirms the conditions the proof needs, without trusting the code that produced it.

The check establishes completeness only to the extent that the Rust state corresponds to
the model's state; no theorem connects the two (`proofs/lean/STATUS.md`). Section 5
states how each tier narrows that gap.

## 2. Classification of the hypotheses

Each hypothesis falls in one of four classes, by what it constrains and what checking it
costs.

| Hypothesis | Constrains | Check | Cost |
|---|---|---|---|
| `hlaw`, `hnf_ax` | the declared laws of an operator | once per signature | constant per operator |
| `MatchersOK` (as `SchedA` of the static plan), `RulesWF` | the compiled rules | once per rule, at compilation | linear in the rule |
| `I0Active` (weakened to classes holding an `f`-node, see `feat/leaf-constants`), `I5`, `hcanon`, `FlatSound` at node level, congruence closure | the final state, node by node | every run | one pass over the nodes |
| `hlat` (lattice closure, cancellative operators) | the final state, class by class | every run | one echelon form over the rows, the cost of one `lattice_round` |
| `Converged` outcome, truncation and overflow counters | the run's outcome | every run | constant |
| `nf_present`, `lhs_reduced`, `cp_joinable`, `A.R.Unchanged` | the final state, across pairs of rules or every match | CI only | one completion round, one naive matching round |
| `hcp_ax` (`AxiomCP`) | the stored left-hand sides against the law instances | per law, as the conditions `CC/Laws/` reduces it to (`hu`, `hlhs`, `hax`, `hmatch`); for `:inverse`, the fixpoints of R1 to R5 | one pass over the rules |
| `slots`, `RoundOK`, `EmitsAll`, `AChain` | the history of the run | replaced by final-state checks | none |

The history hypotheses need no check. The audit (`13-soundness.md` §4, item H3) found that
`slots` is met by an initial state equal to the final one, so it reduces to `I5` at the
final state. The round-history hypotheses serve to prove that semi-naive matching finds
what naive matching finds (`delta_complete`); a naive round at the final state checks the
conclusion directly, and makes the history irrelevant.

## 3. Tier 1: every run, linear

These checks cost one pass over the nodes, the order of one rebuild. They detect a
corrupted state: a stored value that no longer matches the nodes it summarizes. Every
completeness defect fixed in PR #153 and PR #155 except the per-step regroup limit was of
this kind (stale minimal monomial, stale collapsed flag, stale splice).

| Check | Hypothesis | Defect it would have caught |
|---|---|---|
| No `f`-node has a non-`atomic` `f`-child | `FlatSound` (node part) | a nested spelling hiding summands from superposition |
| The `atomic` bit of a class is set iff the class is in `atomicOf`: a child of a stored node, or a class holding a node of another operator (`CC/AtomicOf.lean`; the model's clause "no `f`-node" reads as "holds another operator's node" when every node is visible) | `A = atomicOf st` (`CompleteAtomic`) | a bit left clear after `add_use` or a merge, so a class is spliced where its rule should rewrite; a bit set on a pure `f`-class, so a nested spelling is kept (`atomic_bit_*.egg`) |
| For each class and operator, the stored minimal monomial is the degree-lex least monomial among the class's active `f`-nodes, under the per-class keys | `I5` | `ac_min_slot_refresh.egg`, `ac_minmono_grow_wa.egg` |
| The stored minimal monomial is clamped by the operator's laws | `hcanon` | an unclamped idempotent or nilpotent count |
| Every class holding an `f`-node has an active node spelling its minimal monomial; a class with none is a leaf whose normal form is `{c}` | `I0Active` (weakened) | a class whose rule has no node, invisible to matching |
| No two congruent nodes lie in different classes | the Bridge's congruence premise | a missed congruence after a merge; existing `debug_check_congruent_dup_invariant` |
| For a cancellative operator, no two classes reduce to the same coset representative modulo the lattice of the final rows, recomputed by an independent echelon form | `hlat` (`LatticeClosed`) | a lattice merge the step missed; `cancel_lattice.egg` before `lattice_round` existed |
| Outcome is `Converged`; not `AbortedGrowthLimit` or `AbortedWorkLimit` | `Converged` | a budget stop reported as a fixpoint |
| `flatten_regroup_truncated == 0`, `flatten_skipped == 0` and `flatten_overflowed == 0` for every query of the last round | the bounded enumeration equals the unbounded one (`regroupBounded_query_exact`) | a match lost to a regroup bound; hitting `MAX_ELEMS` skips the whole node and is counted in `flatten_skipped`, not in `flatten_regroup_truncated` |

The result is a per-run verdict, `Complete` or `Incomplete(reason)`, where the reason
names the first failed check and the class or node it failed on. A run that skips
completion (plain mode) reports completeness of congruence closure and matching only, not
modulo the theory.

## 4. Tier 2: CI, independent

Two hypotheses quantify over pairs of rules or over every match, and checking them costs
a full round. The engine already performs both before it reports a fixpoint:

- `lhs_reduced` and `cp_joinable` are what the confirmation round checks: completion reports
  `Converged` only after a full round over every overlapping pair merges nothing
  (`06-ac-congruence-closure.md` §10); the reducibility pass of that round retires every node
  whose monomial another rule reduces (retirement alone does not count as a change), so the
  final state has no rule reducible by another. Pairs are found
  through the use lists, so the cost is proportional to the number of overlapping pairs,
  not to the square of the rule count; it is still one completion round. The round skips
  disjoint pairs and pairs where one left-hand side contains the other (`egraph.rs`,
  `cc_round`). Since commit `2e40098d` the model states the fixpoint the same way
  (`RoundFixed`: `nf_present`, `lhs_reduced`, `cp_joinable` over non-containing pairs) and
  `hcp_of_fixed` derives the rule-rule critical pairs from it: a disjoint pair is handled
  inside the critical-pair lemma, and a containing pair does not exist once the reducibility
  pass has retired the containing node. The tier 2 checker therefore decides `lhs_reduced`
  (a containment test over pairs of rules, the engine's `reducible` scan) and `cp_joinable`
  (normalize both reducts of each non-containing overlapping pair); nothing is left to check
  for the containing pairs. What `hcp` still needs beyond the fixpoint is `AxiomCP`, the
  pairs involving a law instance; `CC/Laws/` reduces it to conditions on the stored
  left-hand sides that one pass over the rules decides (no unit, counts below the order, no
  inverse pair), and for `:inverse` to the fixpoints of R1 to R5.
- `A.R.Unchanged` is what the stop test checks: saturation stops only after a round
  leaves the graph's size stamp unchanged.
- `nf_present` needs one normalization per active node.

Repeating these checks inside the run adds independence from the engine's code and no
other information, at the cost of a second round. They therefore run in CI only, outside
the engine:

1. `dump-egraph` (`egraph/src/parser.rs`) writes the final state of each program of the
   conformance corpora (`egraph/tests/egg/conform*`) and of the soundness corpus.
2. A Lean executable reads the dump into the model's `State` and decides each
   hypothesis. Each decision procedure comes with a theorem that it returns true exactly
   when the hypothesis holds. `Conform/CC/Cert.lean` already reads completion states for
   the certified sample and is the starting point.
3. CI fails when a hypothesis fails on a program whose run reported `Complete`.

This tier detects a defect in the confirmation round or the stop test themselves, which
tier 1 cannot, because tier 1 trusts both.

## 5. What each tier trusts

| Tier | Trusted |
|---|---|
| 1 | the Rust checker, the correspondence between the Rust state and the model's state, and the confirmation round and stop test |
| 2 | the dump writer and the dump reader; the checker itself is proved |

The tier 1 checker must not reuse engine code to recompute what it checks: it reads the
nodes and the stored summaries and recomputes the summaries itself. Reusing the code that
maintains a summary would let a defect in that code pass its own check.

## 6. Not covered

- The completeness theorems for matching under regrouping are laws-free, and the regroup
  bounds are modelled (`RegroupBounds.lean`), and tier 1 covers them by the three counters
  (`regroupBounded_query_exact`).
  The skipping of redundant records needs no check: `regroupSkipG_iff` proves it keeps the
  match set.
- Completion modulo A alone has no completeness theorem (the word problem for semigroups
  is undecidable), so for `:assoc` operators the checks establish matching completeness
  relative to the classes present and nothing about completion.
- Lazy mode decides one equality per transaction and restores the graph; the checks apply
  to the transaction's state before the restore, and a check failure marks the decision
  inconclusive, as a budget stop does (`interpret.rs`, `ac_lazy_budget_inconclusive.egg`).

## 7. Tasks and acceptance

1. Tier 1 checker in `egraph/src`, behind an option (`:check-complete`, and on in debug
   builds), returning the verdict of §3. Acceptance: each fixture listed in §3 fails the
   corresponding check when its fix is reverted, and the full suite passes with the
   option on; cost measured on the completion benchmarks and stated.
2. Static checks of `hlaw`, `hnf_ax` per signature and of `MatchersOK` (`SchedA` of the
   static plan), `RulesWF` per rule.
   Acceptance: a test per hypothesis with a declaration that violates it.
3. Tier 2 Lean checker with its correctness theorems, audited in a `*Check.lean` file.
   Acceptance: no sorry, standard axioms only; CI runs it over the committed corpora.
4. After `feat/leaf-constants` lands, align the `I0Active` check with the weakened
   hypothesis.
