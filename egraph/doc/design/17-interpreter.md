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
    model: M,
    rules: Vec<PreparedRule<Cfg::O, Cfg::S, L>>,
    globals: GlobalCtx<Cfg::S, Cfg::G>,
    marks: Vec<Mark>,
}

struct Mark {
    token: EGraphToken,
    rules_len: usize,
    globals_len: usize,
}
```

## Command Execution

The `run_checked` method processes each `CCommand` in order. Declaration
commands are no-ops: they were already registered during sortcheck.
Ground-term commands (`Let`, `Insert`, `Union`, `Check*`, `Extract`)
build `CTerm`s bottom-up and then act on the resulting ids. Rule
commands compile the RHS and append to the rule set. `Run(n)` enters
the saturation loop for up to `n` iterations. `Push`/`Pop` snapshot
and restore the e-graph along with rule and global counts so that
declarations made inside the scope are undone too.

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
| `Rewrite { query, rhs, .. }` | Compile RHS → push to rules |
| `Rule { query, actions }` | Compile actions → push to rules |
| `Run(n)` | Saturate for n iterations |
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

No string lookups. No sort checks. Just `OpId` → cache dispatch.

## Saturation Loop

```rust
pub fn saturate(rules, eg, model, limit, globals) -> SatResult {
    for i in 0..limit {
        eg.rebuild();
        let index = IndexStore::build(eg);
        let stats = IndexStats::from_index(&index);
        let mut changes = 0;
        for rule in rules {
            let plan = schedule_with_stats(&rule.query, &stats);
            let matches = run_query(&plan, eg, &index, globals);
            for m in matches {
                for action in &rule.actions {
                    changes += apply_action(action, &m, eg, model, globals);
                }
            }
        }
        if changes == 0 {
            return SatResult { iterations: i + 1, saturated: true, match_steps };
        }
    }
    SatResult { iterations: limit, saturated: false, match_steps }
}
```

Each iteration begins by rebuilding (propagating pending merges and
detecting congruences), then constructs sorted indices from scratch,
schedules each rule based on current cardinalities, executes the
plans via leapfrog triejoin, and applies the resulting actions. If
no actions produced changes, saturation is complete.

`SatResult` also carries `match_steps`: the total number of
partial-match extensions explored across all rounds. It is populated
only when match-step counting is enabled (off by default; see the
instrumentation note below), and is the direct measure used to compare
match work between strategies.

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
is chosen with `--strategy naive|semi-naive` (default `naive`), and
match-step counting is enabled with `--count-match-steps`, which prints
the total match work at the end of the run. The default is unchanged,
so existing programs behave identically. Semi-naive is sound,
fixpoint-equivalent to naive, and has no automatic fallback. Its
mechanism — the `touched` log, delta index, `VariantIndex`, and the
k-variant fan-out — is the subject of Chapter 18.

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
