<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Task: saturation engine for abstract values

**Status**: task specification for PR 3 of 4; nothing in it is implemented.
The design is [eclass-analysis.md](eclass-analysis.md). This document says
which code changes, in which order, and how the result is checked. It does
not restate the design; each section links the design section it executes.

The four PRs:

| PR | Branch | Delivers |
|---|---|---|
| 1 | `abs-surface-syntax` | `:interp` and `:domains` on sorts, `:interp` on functions, `(refine t v)`, abstract guards |
| 2 | `abs-class-storage` | an abs handle per class and per-sort pools in the `containers-verus` class layer; `MergeInfo` returns the absorbed handle |
| 3 | `abs-saturation-engine` | this task: the engine that runs transfers, meets and derived merges |
| 4 | `abs-domain-registry` | the transfer, meet and reduce functions in `abstract-domains`, keyed by carrier and operator |

## 1. What the PR delivers

The PR makes the e-graph keep one abstract value per class of an analysed
sort, and keep it sound under every event that changes classes. It
executes what PR 1 declares, stores values through PR 2, and computes them
with PR 4.

The first milestone is [eclass-analysis.md §10](eclass-analysis.md#10-acceptance-criteria):
one sort, `Int` with intervals, through declaration, seeding, make, merge,
backward `ite`, conflict, push and pop. Bit-vector sorts, AC transfers
([§13.4](eclass-analysis.md#134-transfers-for-flat-a-ac-and-aci-nodes)) and
disequality answers come after the milestone.

The PR delivers:

- the five events of §2 wired into `egraph.rs`, `apply.rs`, `ematch.rs` and
  `interpret.rs`;
- three work queues and a per-class change budget (§3);
- value changes in the semi-naive touched log (§4);
- derived merges and conflict reporting (§5);
- correct behaviour under push, pop and the lazy-AC check transaction (§6);
- the 15 acceptance programs of §10 passing, with `#[ignore]` removed from
  `tests/abs_engine.rs`.

## 2. Events

Each event either writes a class value or reads one. A write always goes
through one path: meet the new value into the class's entry, reduce, and
compare with `==` ([eclass-analysis.md §3](eclass-analysis.md#3-requirements),
requirement 3). An empty result is a conflict (§5). A strict change marks the
class as changed, which schedules work (§3) and enters the touched log (§4).

| Event | Trigger | Engine action | Code site |
|---|---|---|---|
| make | a fresh node `f(c1, …, cn)` of an analysed sort | allocate the class entry at top; push the node on the forward queue; a literal node starts at its singleton | `egraph.rs` `EGraph::register_if_fresh`, `EGraph::add_lit` |
| merge | `merge_in_classes` unions two classes | meet the survivor's value with `MergeInfo::absorbed_abs`, reduce, write the survivor's entry | `egraph.rs` `EGraph::merge_in_classes` |
| child refine | a class value shrinks | every parent node on the class's use list goes on the forward queue; its forward transfer is met into the parent's class | `egraph.rs` `EGraph::rebuild` drains; the use list is read after `splice_uses` in `EGraph::rebuild_congruence` |
| parent refine | a class value shrinks | every node of the class goes on the backward queue; its backward transfer is met into each child's class (`ite`, comparisons, invertible operators) | `egraph.rs` `EGraph::rebuild` drains |
| seed, command | `(refine t v)` at top level | build `t`, meet `v` into its class, rebuild as `union` does | `interpret.rs` `Interpreter::exec_checked` |
| seed, rule head | `(refine t v)` in a rule's actions | evaluate `t`, meet `v` into its class; the action counts as a change only if the value shrank | `apply.rs` `apply_action` |
| guard | `(within x lo hi)`, `(nonzero x)` in a rule body | read the class value of `x`; the guard holds if the value implies the test | `ematch.rs` `eval_guard` |

Make runs the forward transfer of the node's `:interp` operator over the
children's current values. A node of an operator without `:interp` gives
top, which changes nothing. The `ite` backward rule is the table of
[eclass-analysis.md §6](eclass-analysis.md#6-propagation-rules).

A merge is the one hook for every kind of union: direct, rule action,
congruence, completion, canonization repair and creation collisions all
call `merge_in_classes`. The six `fold_min_monomial` call sites are the
model for the shape, not six places to repeat the meet.

## 3. Queues and the budget

Rebuild drains three queues
([eclass-analysis.md §7](eclass-analysis.md#7-scheduling-and-termination)):

| Queue | Element | Drained by | Produces |
|---|---|---|---|
| merges | a class whose value changed by a meet | marking the class changed | forward and backward entries |
| forward | a node whose children changed | meeting `forward(op, children)` into the node's class | merges entries |
| backward | a node whose class changed | meeting `backward(op, class, children)` into each child | merges entries |

The drain runs after `rebuild_congruence` reaches its fixpoint. Forward work
reads the use list at drain time: the absorbed parents join the survivor's
list only at `splice_uses`. Derived merges collected during the drain apply
as one batch after it (§5). Rebuild repeats congruence, drain and batch until
none of them merges a class.

**Budget.** Each class may change its value at most `B` times per budget
epoch. A class past its budget keeps its value and schedules no further
work in that epoch. A run iteration starts an epoch, in both drivers
(`saturate_rules_naive`, `saturate_rules_semi`). A top-level command outside
a run is one epoch. Every write keeps a sound value, so the budget costs
precision only. `restore` and `pop` clear the budget counters with the
queues.

The reduction inside one value has its own fuel, passed to PR 4's `reduce`.
That fuel also costs precision only.

## 4. The semi-naive obligation

A value change that creates no node and merges no class must reach the next
semi-naive round
([eclass-analysis.md §3](eclass-analysis.md#3-requirements), requirement 5).
Without it, a rule guarded on `(within y 1 10)` misses `y` when `y` shrinks
through propagation alone. `tests/egg/abs-engine/value_only_round.egg` is
that case.

The delta index is built from the node ids in `EGraph::touched`, read by
`saturate_rules_semi` right after the round's rebuild. A strict value change
of class `c` therefore pushes:

| Pushed | Why |
|---|---|
| every member node of `c` | a guard on a variable bound at an atom's root reads `c` through that atom's node |
| every parent on `c`'s use list | a guard on a child variable reads `c` through the parent atom's node |

The push follows the same gate as `track_merge_members`: only semi-naive
saturation consumes the log. Its cost per change is the class size plus its
use count, and the budget bounds the number of changes. Changes made by
rule-head `refine` in round `i` propagate in the rebuild of round `i + 1`,
before that round's delta build, so they need no separate path.

## 5. Derived merges and conflicts

**Derived merges** follow
[eclass-analysis.md §8](eclass-analysis.md#8-merges-derived-from-abstract-values).
Only singleton values produce them:

| Source | Condition | Merge |
|---|---|---|
| constant | an `Int` class has the value `{k}` | the class and the literal node for `k` |
| decided Boolean | a `Bool` class has the value `true` or `false` | the class and that literal |
| decided `ite` | the condition class of an `ite` node is decided | the node's class and the chosen branch |

The drain collects these pairs and applies them as one batch after it,
because a merge changes the classes the drain iterates over. A derived merge
is an ordinary merge: it goes through `merge_in_classes` and enters the
touched log. Equal non-singleton values never merge. Inverse-operator
merges (`sub(a, b) = {0}`) come after the milestone.

**Conflicts.** An empty meet proves that the program's equalities and seeds
have no model. Every write path can produce one: merge, seed, forward,
backward. The engine records the first conflict in a sticky field, stops the
drain, and leaves the graph as it is. The proposed report follows the width
error (`EGraph::take_width_error`):

| Step | Site |
|---|---|
| `EGraph::take_abs_conflict` returns and clears the conflict | next to `take_width_error` in `egraph.rs` |
| a run stops with an error after the rebuild that met it | `saturate.rs` `width_check` |
| a command reports `InterpError` with a message containing `abstract conflict` | `interpret.rs` `Interpreter::run_checked` |

The acceptance programs pin the substring `abstract conflict`. A student who
chooses another report changes the programs' `MESSAGE` lines in the same PR.

After the milestone, `check-neq` can accept two classes whose meet is empty
without the lazy search (`interpret.rs` `CheckNeq` arm).

## 6. Push, pop and the lazy-AC check transaction

**Push and pop.** PR 2 marks and restores the abs pools with the classes,
so values roll back with no engine code. The engine owns three pieces of
transient state: the queues, the derived-merge batch and the budget counters.

| Operation | Engine obligation | Site |
|---|---|---|
| `mark` | the rebuild at its start drains the queues, so a snapshot holds no pending work; the token carries the conflict field next to `completion_outcome` | `EGraph::mark_with` |
| `restore` | clear queues, batch and counters; restore the conflict field from the token | `EGraph::restore_with` |
| `restore_and_pop`, `pop_scope` | the same clears | `EGraph::restore_and_pop_with`, `EGraph::pop_scope` |

**Lazy-AC check transaction.** `Interpreter::lazy_txn_open` marks the graph
and turns completion on; `lazy_txn_close` restores. Consecutive checks share
one transaction, and the first other command closes it
(`Interpreter::run_checked`).

| Situation | Behaviour |
|---|---|
| transaction opens | the mark rebuilds, so every value is propagated first |
| completion merges two classes inside it | the merge meets values as any merge does |
| completion mints a node | `register_if_fresh` runs make; AC operators have no `:interp` in the milestone and give top |
| `cc_goal` stops the closure early (`GoalMet`) | the drain runs before the goal poll in `EGraph::rebuild`, so a goal met by a derived merge stops the closure |
| a value is refined inside it | the refinement is discarded at close; a later command sees the pre-check value |
| a conflict is met inside it | completion merges are entailed by the program, so the conflict is real; the check reports it, and `run_checked` reads it before `lazy_txn_close`, because restore resets the conflict field from the token |

The completion loop in `EGraph::rebuild` therefore runs the drain and the
batch in each round, after `rebuild_congruence` and before the goal poll.
A growth-budget abort leaves the queues in place; the next rebuild or the
restore handles them.

## 7. Interfaces consumed

The signatures below are assumptions. Each one is reconciled with the PR
that provides it before this PR merges.

**From PR 1 (surface syntax).**

```rust
// Sort and operator metadata, registered by sortcheck.
fn SortRegistry::abs_carrier(&self, s: S) -> Option<(Carrier, DomainMask)>; // None: no analysis
fn OpRegistry::interp(&self, o: O) -> Option<InterpOp>;                     // None: top
// Seeds and guards.
CCommand::Refine(CTerm<O, S, L>, AbsLit)                  // top-level (refine t v)
CompiledAction::Refine(RhsOp<O, L>, AbsLit)               // rule-head (refine t v)
RAtom::AbsGuard { var: VarId, test: AbsTest }             // (within x lo hi), (nonzero x)
```

PR 1 also fixes three literal questions the acceptance programs assume:
integer literals at an `:interp int` sort (`(add x 1)`), Boolean literals
`true` and `false` at an `:interp bool` sort, and a literal operator for each
analysed sort (`OpRegistry::lit_op_for_sort`) for the constant merges of §5.

**From PR 2 (class storage).**

```rust
MergeInfo { /* existing fields */ absorbed_abs: Option<AbsRef> }
fn EClasses::abs_ref(&self, repr: K) -> Option<AbsRef>;
fn EClasses::abs_entry(&self, r: AbsRef) -> AbsEntry;            // AbsEntry: Copy, opaque bytes
fn EClasses::write_abs(&mut self, r: AbsRef, e: AbsEntry);       // tracked write, rolled back by restore
// add_singleton allocates the entry at top when the sort is analysed.
```

**From PR 4 (domain registry).**

```rust
fn top(c: Carrier, m: DomainMask) -> AbsEntry;
fn meet(c: Carrier, m: DomainMask, a: AbsEntry, b: AbsEntry) -> BotOr<AbsEntry>;
fn reduce(c: Carrier, m: DomainMask, e: AbsEntry, fuel: u8) -> BotOr<AbsEntry>;
fn forward(op: InterpOp, m: DomainMask, args: &[AbsEntry]) -> AbsEntry;
fn backward(op: InterpOp, m: DomainMask, result: AbsEntry, args: &[AbsEntry])
    -> BotOr<SmallVec<[AbsEntry; 3]>>;
fn as_constant(c: Carrier, e: AbsEntry) -> Option<Constant>;      // singleton test
fn encode_seed(c: Carrier, m: DomainMask, v: &AbsLit) -> AbsEntry; // (interval lo hi), …
fn implies(c: Carrier, e: AbsEntry, t: &AbsTest) -> bool;         // guard evaluation
```

## 8. Change sites

Each site carries a comment `TODO(abs-saturation-engine)` that names the
change and the section of this document. The comments change no behaviour.

| File:line | Function | Change | § |
|---|---|---|---|
| `egraph/src/egraph.rs:186` | `EGraph` field `touched` | value changes enter the log | §4 |
| `egraph/src/egraph.rs:439` | before `take_width_error` | add `take_abs_conflict` | §5 |
| `egraph/src/egraph.rs:1255` | `add_lit` | a literal starts at its singleton | §2 |
| `egraph/src/egraph.rs:1583` | `merge` | the meet lives in `merge_in_classes`, not per fold site | §2 |
| `egraph/src/egraph.rs:1651` | `merge_in_classes` | meet with `absorbed_abs`, reduce, write, schedule | §2, §5 |
| `egraph/src/egraph.rs:2155` | `rebuild` (plain loop) | drain the queues, apply derived merges, repeat | §3, §5 |
| `egraph/src/egraph.rs:2211` | `rebuild` (completion loop) | drain before the goal poll | §6 |
| `egraph/src/egraph.rs:2390` | `rebuild_congruence` | forward work reads the use list after the splice | §3 |
| `egraph/src/egraph.rs:3558` | `mark_with` | no pending work at mark; token carries the conflict | §6 |
| `egraph/src/egraph.rs:3621` | `restore_with` | clear queues, batch, counters | §6 |
| `egraph/src/egraph.rs:3667` | `restore_and_pop_with` | the same clears | §6 |
| `egraph/src/egraph.rs:3696` | `pop_scope` | the same clears | §6 |
| `egraph/src/egraph.rs:3842` | `register_if_fresh` | make: entry at top, node on the forward queue | §2, §3 |
| `egraph/src/saturate.rs:116` | `width_check` | stop the run on a conflict | §5 |
| `egraph/src/saturate.rs:392` | `saturate_rules_naive` | start a budget epoch per iteration | §3 |
| `egraph/src/saturate.rs:877` | `saturate_rules_semi` | start a budget epoch per iteration | §3 |
| `egraph/src/saturate.rs:894` | `saturate_rules_semi` | value changes are in `touched` before the delta build | §4 |
| `egraph/src/ematch.rs:2110` | `eval_guard` | abstract guards read class values | §2 |
| `egraph/src/apply.rs:1289` | `apply_action` | rule-head `refine` | §2 |
| `egraph/src/interpret.rs:420` | `lazy_txn_open` | values propagated before the transaction | §6 |
| `egraph/src/interpret.rs:462` | `lazy_ac_decide` | completion merges meet; conflicts are reported | §6 |
| `egraph/src/interpret.rs:823` | `run_checked` | report a conflict before `lazy_txn_close` | §5 |
| `egraph/src/interpret.rs:911` | `exec_checked` | the `Refine` command arm | §2 |
| `egraph/src/interpret.rs:964` | `exec_checked` (`CheckNeq`) | disequality from an empty meet, after the milestone | §5 |
| `egraph/src/interpret.rs:1270` | `exec_checked` (`Push`) | no engine work; checked by `push_pop_restores.egg` | §6 |
| `egraph/src/interpret.rs:1389` | `exec_checked` (`Pop`) | values and conflict roll back | §6 |

## 9. Decisions left to the student

| Decision | Options | Constraint |
|---|---|---|
| budget scope ([eclass-analysis.md §7](eclass-analysis.md#7-scheduling-and-termination), open) | per class per iteration; one global budget per rebuild; both | `x_plus_one_budget.egg` terminates; the choice is measured on the CBMC corpus |
| budget value `B` | a constant, or a `set-option` | the same; report the precision lost against `B = ∞` on programs that terminate |
| conflict report | sticky field and an `InterpError` variant (§5); `CheckFailed`; a new outcome | a conflict stops the program; the `MESSAGE` lines of the conflict programs match the report |
| explanation of derived merges ([eclass-analysis.md §8](eclass-analysis.md#8-merges-derived-from-abstract-values), open) | dependency tracking; a trusted `Justification::Analysis` | `PROOFS = true` builds and `explain` does not panic on a derived merge |
| touched granularity (§4) | members and parents; a class-level delta in the index | `value_only_round.egg` passes under `EVAL: both` |
| queue order | FIFO; priority by class size | none for soundness; report the effect on the CBMC corpus |

## 10. Acceptance criteria

**Programs.** `tests/abs_engine.rs` runs every file in
`tests/egg/abs-engine/` under naive and semi-naive evaluation. The test is
ignored on this branch; the PR removes the `#[ignore]`. `egg_tests.rs` lists
its files one by one, so it does not run these.

| Program | Checks | Expected |
|---|---|---|
| `forward_add.egg` | seed `[0, 9]`, make `(add x 1)`, exact bound `[1, 10]` | ok |
| `merge_meet.egg` | `[0, 9]` meet `[5, 20]` is `[5, 9]`; the parent becomes `[6, 10]` | ok |
| `backward_add.egg` | seeding `(add x 1)` with `[1, 5]` refines `x` to `[0, 4]` | ok |
| `backward_ite.egg` | `meet(R, e)` empty decides `c` and refines `t` to `[0, 5]` | ok |
| `conflict_merge.egg` | union of `[0, 4]` and `[10, 20]` | error, `abstract conflict` |
| `conflict_seed.egg` | two disjoint seeds on one term | error, `abstract conflict` |
| `conflict_forward.egg` | a seed disjoint from a forward value | error, `abstract conflict` |
| `rule_head_refine.egg` | a guard in the body, `refine` in the head | ok |
| `value_only_round.egg` | a value-only change re-fires a guarded rule | ok, naive and semi-naive |
| `x_plus_one_budget.egg` | `x = x + 1` over `[0, 2^62]` stops within the budget | ok |
| `push_pop_restores.egg` | a refinement inside a scope is gone after `pop` | ok |
| `derived_singleton.egg` | `{3}` merges with `3`; two `{5}` classes merge; two `[0, 9]` classes do not | ok |
| `decided_ite.egg` | `(lt x 10)` with `x` in `[0, 4]` merges with `true`; the `ite` merges with its branch | ok |
| `lazy_check_rollback.egg` | a meet inside a check transaction is discarded at close | ok |
| `lazy_check_conflict.egg` | a conflict inside a check transaction is reported | error, `abstract conflict` |

Each program observes a value through a rule guarded on `(within r lo hi)`
that unions a marker with `(Yes)`, followed by `check-eq` or `check-neq` on
the marker. This needs no observation command. A student may add one, for
example `(check-within t lo hi)`, and keep these programs as they are.

**Rust tests.**

- Naive and semi-naive evaluation reach the same values on generated
  programs, as a property test next to `saturate.rs`'s `diff_random`.
- A program without `:domains` pushes nothing on the three queues; a unit
  test asserts it on a program of `tests/egg/`.
- Every test of `egg_tests.rs` passes unchanged.

**Benchmark.** The CBMC corpus of PR #144 (`egraph/tests/egg/cbmc/` on that
PR's branch, 214 programs from 107 dumps; not on `main`) runs with an
analysed variant of its term sort, seeded by `refine` from each leaf's type
range. The PR reports, per program, the cost per merge and per rebuild
against the same program without `:domains`, and the number of conflicts and
derived merges found.

**Checks.** `cargo fmt --all --check`, `cargo clippy`, `cargo test -p
semi-persistent-egraph` and `bash scripts/check-oss-scaffold.sh` pass. The
class layer gains no `admit`, `assume` or trusted contract.

## 11. Links

- [eclass-analysis.md](eclass-analysis.md): §1 events, §3 requirements,
  §6 propagation rules, §7 scheduling, §8 derived merges, §10 acceptance,
  §13.4 AC transfers, §13.5 conflicts.
- [lattice-functions.md](lattice-functions.md): the same semi-naive
  obligation for lattice tables.
- [semi-naive-deferred-work.md](semi-naive-deferred-work.md): the scope of
  the naive and semi-naive equivalence argument this PR extends.
- [ac-completion-limitations.md](ac-completion-limitations.md): lazy
  completion and its budgets.
- `abstract-domains/doc/reduced-product.md`: the reduction and its fuel.
- `containers-verus/doc/design/egraph-class-layer.md`: the class layer PR 2
  extends.
- Sibling task documents on branches `abs-surface-syntax`,
  `abs-class-storage` and `abs-domain-registry`.
