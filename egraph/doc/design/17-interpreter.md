# Chapter 17 — Interpreter and Saturation Loop

[← Ch 16: Extraction](16-extraction.md) · [Table of Contents](00-table-of-contents.md)


## Putting It All Together

The interpreter is the top-level driver that ties every component
together. It processes a sequence of `CCommand`s (the output of
sortcheck, Chapter 11) against a live e-graph. Declaration commands
register sorts and operators. Ground terms are built bottom-up.
Rules are compiled and stored. `(run N)` triggers the saturation
loop. `(push)`/`(pop)` snapshot and restore the entire state.

The saturation loop itself is the classic equality saturation
algorithm: rebuild, index, schedule, match, apply, repeated until
fixpoint or the iteration limit.

## `Interpreter`

```rust
pub struct Interpreter<Cfg, L, M, const TRACK: bool, const PROOFS: bool> {
    pub eg: EGraph<Cfg, L, TRACK, PROOFS>,
    pub model: M,
    rules: Vec<PreparedRule<Cfg::O, Cfg::S, L>>,
    globals: GlobalCtx<Cfg::S, Cfg::G>,
    marks: Vec<Mark<Cfg, Cfg::O>>,
    shrink_policy: ShrinkPolicy,
    strategy: SaturationStrategy,          // naive or semi-naive (run N) dispatch
    ac_mode: AcMode,                       // Off, Eager, or Lazy completion
    lazy_ac_rounds: usize,                 // alternation budget for a lazy check's second phase
    lazy_txn: Option<EGraphToken>,         // the shared lazy-check transaction, Some while open
    last_sat: Option<SatResult>,           // outcome of the most recent (run …)
    last_run_time: Option<Duration>,       // wall time of the most recent (run …)
    index_scratch: IndexScratch<Cfg>,      // index build scratch, reused across runs
}

struct Mark<Cfg, O> {
    token: EGraphToken,
    rules_len: usize,
    globals_len: usize,
    _phantom: PhantomData<(Cfg, O)>,
}
```

## Command Execution

The `run_checked` method processes each `CCommand` in order. Declaration
commands are no-ops: they were already registered during sortcheck.
Ground-term commands (`Let`, `Insert`, `Union`, `Check*`, `Extract`)
build `CTerm`s bottom-up and then act on the resulting ids. Rule
commands compile the RHS and append to the rule set. `Run(n)` enters
the saturation loop for up to `n` iterations. `Push`/`Pop` snapshot
and restore the e-graph along with rule and global counts. Surface-language
declarations are static: the full program is sortchecked first, so every
declaration has already been registered before any interpreted `Push`.

| Command | Action |
|---------|--------|
| `Decl(_)` | No-op (registered during sortcheck) |
| `Let(name, ct)` | Build CTerm → bind in globals |
| `Insert(ct)` | Build CTerm |
| `Union(a, b)` | Build both → merge → rebuild |
| `Check(ct)` | Build CTerm (assert exists) |
| `CheckEq(a, b)` | Build both → verify find(a) == find(b) |
| `CheckNeq(a, b)` | Build both → verify find(a) != find(b) |
| `Extract(ct)` | Build → extract_best → print |
| `Rewrite { query, rhs, .. }` | Compile RHS → push to rules (with its ruleset) |
| `Rule { query, actions, .. }` | Compile actions → push to rules (with its ruleset) |
| `Run { ruleset, limit, until }` | Build the goal terms → saturate under a `RunSpec` |
| `PrintSize(op)` | Per-op node counts and total, or one op's count |
| `PrintStats(file)` | Last run's counters, as text or JSON |
| `Push(shrink)` | Snapshot e-graph + rules count (`:shrink` reclaims capacity) |
| `Pop` | Restore e-graph + truncate rules |

## Building a `CTerm`

```rust
fn build_cterm(&mut self, ct: &CTerm) -> (G, S) {
    match ct {
        CTerm::Lit(val, sort) => {
            let lit_op = eg.ops().lit_op_for_sort(sort);
            let vid = eg.intern_lit(val.clone());
            (eg.add_lit(lit_op, vid), sort)
        }
        CTerm::App { op, sort, children } => {
            let ids: Vec<G> = children.iter().map(|c| self.build_cterm(c).0).collect();
            (eg.add(op, &ids), sort)
        }
        CTerm::Global(name, sort) => {
            let (_, _, id) = self.globals.get(name);
            (eg.find(id), sort)
        }
    }
}
```

Applications and literals need no name lookup or sort check. The
`CTerm::Global` arm intentionally performs a `GlobalCtx` hash lookup because
checked global ground terms retain their source name.

## Saturation Loop

```rust
pub fn saturate_spec_in(rules, eg, model, spec, globals, scratch) -> SatResult {
    for i in 0..spec.limit {
        if goal_holds(spec, eg) { return goal_result(i); }
        eg.rebuild();
        let index = IndexStore::build_with(eg, scratch);
        let stats = IndexStats::from_index(&index);
        let mut changes = 0;
        for rule in rules matching spec.ruleset {
            changes += apply_rule_pooled(rule, eg, index, stats, model, globals);
        }
        index.recycle_into(scratch);
        if changes == 0 {
            return saturated_result(i + 1);
        }
    }
    budget_result(spec.limit)
}
```

Each iteration begins by rebuilding (propagating pending merges and
detecting congruences), then constructs sorted indices from scratch,
schedules each rule based on current cardinalities, executes the
plans via leapfrog triejoin, and applies the resulting actions. If
the action counter is zero, `SatResult::saturated` reports an operational
fixpoint for this driver. This is not a theorem of logical completeness.
`Union` increments only for a new merge, but `Insert` increments whenever it is
applied and `Subsume` increments whenever it is applied; those conservative
counters can keep a run from reporting saturation even when an insertion
hash-conses to an existing node.

`SatResult` also carries `match_steps`: one count per executed lowered
matching step plus one per emitted match, across all rounds. It is populated
only when match-step counting is enabled (off by default; see the
instrumentation note below). It is an implementation work proxy, not a count
of semantic matches or a machine-independent runtime measure.

## Saturation Strategy

The loop above is the **naive** strategy: every round rediscovers all
matches against the freshly-built full index. The interpreter can
instead run **semi-naive** evaluation, which matches only what changed
each round:

```rust
pub enum SaturationStrategy { Naive, SemiNaive }  // default: Naive

interp.set_strategy(SaturationStrategy::SemiNaive);
```

`(run N)` dispatches on the selected strategy: `Naive` calls
`saturate`, `SemiNaive` calls `saturate_semi`. On the CLI the strategy
is chosen with `--use-semi-naive` or `--use-naive` (mutually exclusive;
the default is naive), and match-step counting is enabled with
`--count-match-steps`, which prints the total match work at the end of
the run. Semi-naive does not switch the whole run to naive automatically.
Individual rules use a full-index match in rounds after the first when they
have no scanning atom or contain equality/global constraints whose enabling
merge is not represented by an atom delta. Its mechanism (the `touched` log, delta index,
`VariantIndex`, and the k-variant fan-out) is the subject of Chapter 18.
The intended soundness and naive-fixpoint equivalence are justified by the
delta decomposition and finite differential/regression tests; they are not
machine-checked end-to-end theorems.

## Run Control: Rulesets and Goals

`(run N)` runs the **default** ruleset: the rules with no `:ruleset`
tag. `(run name N)` runs the rules
tagged `:ruleset name` and nothing else. Both directions of that scoping
matter: a scoped experiment (an AC block, say) must not fire under the
main run, and the main run's rules must not fire under it. Ruleset ids
are assigned by sortcheck in declaration order and stored on the
`PreparedRule`, so the driver's filter is one integer comparison per
rule per round.

Rulesets are static: they are not scoped by `(push)`/`(pop)`, and the
name table lives for one `sortcheck_program` call.

`(run [ruleset] N :until (= a b))`, or `(!= a b)`, stops the run as
soon as the goal holds. The goal's terms are ground, so they are built
once, before the run; only their classes move afterwards, and the check
is two `find`s. It runs **before** every iteration, including the first,
so a goal that already holds costs zero iterations. `SatResult.goal_met`
distinguishes stopping on the goal from reaching a fixpoint: the goal
can be met with rules still firing.

Building the goal's terms adds those nodes to the e-graph, which is
observable: the same nodes a `(check …)` of the goal would add.

For `:until (!= a b)`, "holds" means the two current representatives differ.
It is not a maintained semantic disequality, and it commonly succeeds at
iteration zero when the terms begin apart.

## Statistics

`(print-size)` lists the node count of every operator that has nodes,
then the total; `(print-size Op)` prints one operator's count as a bare
integer. `(print-stats)` reports the e-graph's current size and the
counters of the most recent run: nodes, classes, iterations, match
steps, wall time, whether it saturated, and whether its goal was met.
`(print-stats :file "p.json")` writes the same numbers as a flat JSON
object for a harness to parse.

Match steps are only accumulated into the thread-local total while its counter
is armed. Each query first tallies into its `MatchPool`; the total is folded
into the thread-local once per query, not loaded once per matching step. The
interpreter arms counting when the program contains `print-stats`, so asking
for stats is enough to get a nonzero work count.

`wall_time_ms` measures the saturation call. Construction and any pre-run
rebuild of `:until` goal terms occur before the timer starts.

## AC Completion Modes

- `Off` (default): each rebuild returns after `rebuild_congruence`, including
  structural canonization and local algebraic normalization, without global
  AC completion.
- `Eager`: rebuild interleaves congruence with completion rounds. Only
  `CompletionOutcome::Converged` means the implementation reached its
  full-round operational fixpoint; it is not by itself a machine-checked
  semantic-completeness result.
- `Lazy`: ordinary saturation keeps completion off. Consecutive equality
  checks share a marked, goal-directed completion transaction, and the first
  non-equality command restores it. Goal or resource stopping can leave the
  completion search intentionally unfinished.

## Push/Pop Scoping

```rust
Push(shrink) => {
    let policy = if shrink {
        ShrinkPolicy::IfOverallocated { factor: 4, headroom: 2 }
    } else {
        self.shrink_policy  // default: Never
    };
    marks.push(Mark {
        token: eg.mark(policy),
        rules_len: rules.len(),
        globals_len: globals.len(),
    });
}

Pop => {
    let mark = marks.pop();
    eg.restore(mark.token);
    rules.truncate(mark.rules_len);
    globals.truncate(mark.globals_len);
}
```

`(push)` snapshots with the interpreter's default policy (normally
`Never`, so capacity ratchets to the high-water mark). `(push :shrink)`
forces `IfOverallocated`, reclaiming excess capacity before the
snapshot. This is useful for top-level marks after major search resets
where the previous branch was much larger than the next one will be.

Restore takes no policy; it just undoes. Shrinking at restore time
would cause unnecessary reallocations when the next branch grows back
to a similar size (see Chapter 2).

## `GlobalCtx` Synchronization

During sortcheck, `GlobalCtx<S, ()>` tracks global names and sorts
(no runtime bindings). During interpretation, `GlobalCtx<S, G>` tracks
names, sorts, and actual e-class bindings.

Both process `Let` commands in the same order, so `GlobalVarId`
indices assigned during sortcheck match those assigned at runtime.
Patterns reference globals via `PatVar::Global(GlobalVarId)`, which
indexes directly into the interpreter's `GlobalCtx`.

---
[← Ch 16: Extraction](16-extraction.md) · [Table of Contents](00-table-of-contents.md)
