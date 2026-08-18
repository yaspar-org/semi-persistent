# AU subsystem review: bugs and performance paths (2026-08-14)

*Resolution: all three defects below are fixed in the tree. P0-1: the
transport module is exact-integer only (`egraph/src/au/transport.rs`
accepts no float costs and carries a relaxation budget). P0-2: regression
test `exact_identity_class_with_ac_member_terminates` in
`egraph/src/au/exact.rs`. P1-3: the operator is part of the dedup
signature (`egraph/src/au/actions.rs`). The performance paths landed as
A0-A8 in `au-solver-plan.md`. This file is the dated review record; line
references below are to the reviewed snapshot, not the current tree.*

Second-look review of `egraph/src/au/`, run as a differential-fuzz plus
profiling pass against the shipped code on branch `egraph-wf`. Method:
2400 randomized cases (leaves, unary and binary ops, mset and set
operators with and without units, random merges, both cycle modes),
each comparing the exact solver against MCGS at 3000 playouts and
re-evaluating both projections of the exact result in a freshly rebuilt
identical e-graph; plus deterministic repro binaries and `sample`-based
profiles. The library's own au tests pass (106/106); every finding
below reproduces from a repro binary. Harness code lives outside the
repo (session scratchpad, crate `aucheck`); nothing in-tree changed.

Detailed per-defect accounts with minimal triggers and the chosen fix
directions are in `au-defects.md`.

## Bugs, ranked

**P0-1. MCGS hangs: `solve_transport_f64` loops forever.**
`egraph/src/au/transport.rs:217-268` (the SPFA relaxation loop),
reached from `recompute_transport_and_value` (`mcgs.rs:1588`) on every
backpropagation through a transport-AND node. Deterministic repro on an
ordinary acyclic e-graph (2 of 2400 fuzz cases; two independent
`sample` captures put 100% of time in the relaxation loop). Cause: the
successive-shortest-paths invariant (no negative residual cycle) holds
only under exact arithmetic; the costs are f64 Q values whose
mathematically-equal path sums differ by 1 ulp, and after one
augmentation along a not-actually-shortest path the residual graph
carries a cycle of cost about -1 ulp, which strict-less relaxation
lowers forever. The integer solver (`transport.rs:340`, exact `i128`)
is immune. Fix options: node potentials with reduced costs and an
epsilon clamp; a per-solve relaxation budget returning the previous
flow; or fixed-point costs sharing the exact-arithmetic guarantee. At
minimum a work-bound assert, so the failure is loud instead of a hang.

**P0-2. Exact solver panics when an AC identity class contains an AC
member.** `unreachable!` at `egraph/src/au/exact.rs:185` ("cycle-mode
rank invariant violated"); 13 of 2400 cases. Minimal trigger: declare
unit `e` for mset `plus`, `merge(e, plus{a,b})`, `rebuild()`, then
exact `AU(c, e)`. Cause: identity padding (`ac_repr.rs:126-157`)
injects the identity class as a transport-cell child that is not a
structural child, so `derive_child_context`'s reachability filter
(`space.rs:398-418`) never adds the ancestors to the cycle context, and
the identical OR key recurs beneath itself while `Visiting`. MCGS
tolerates the same graphs (all 64 pairs of a triggering graph
complete). Fix directions: treat a padding-injected identity as
context-relevant, or cycle-block cells pairing against an identity
class that has members of the same operator; downgrading the re-entry
panic to "no candidate" needs a minimality argument first.

**P1-3. Cross-operator action loss in `dedup_and_insert`.**
`egraph/src/au/actions.rs:455-464`: the dedup signature is
`(left, right, count)` and omits `action.op`, so
`merge(f(a), g(a)); merge(f(b), g(b))` yields one action instead of
two - the `g` action is silently dropped. Optimal quality is
unaffected (same-signature actions score identically) but the search
space is truncated and the reported generalization can never use the
dropped operator. Fix: include `action.op` in the signature.

**P2, no observed misbehavior:** `distribute_row`'s greedy and
off-diagonal branches are byte-identical and the off-diagonal order
emits worst-first matrices under `a_max` truncation (oracle path
only); identity expansion iterates per member instead of per distinct
op (deduped later; oracle path only); `ac_repr::canonize` sums
duplicate multiplicities for ACI monomials where idempotence argues
collapse (defensive-only post-rebuild); ACI identity padding with
deficit above 1 counts size per repeated copy, a minor scoring skew.
Checked clean: snapshot class ids are minted from `find_const` at
construction and the snapshot borrows the e-graph, so stale ids after
merges are a compile error; the interpreter rebuilds before
snapshotting; span and id mints are checked; mark/restore validates
all tokens before mutating.

## Performance paths, ranked (no AU benches exist; evidence is a
scratch workload plus `sample` profiles)

1. **No early exit after structural completion** (`mcgs.rs:1002-1016`):
   completion is checked once, after the full budget. Measured on a
   ~40-node workload, all runs ending `size=80, Exact`: 11.6 ms at
   1000 playouts, 29 ms at 3000, 81 ms at 10000, 240 ms at 30000,
   1.77 s at 200000; the exact solver answers the same instance in
   237 us. A geometric-schedule completion check is the single
   largest win for the exhausted-graph case.
2. **Transport solves dominate playouts**: the f64 solve per
   transport-AND per backprop step (`mcgs.rs:1559`) and the integer
   solve in `compose_and_offer` (`mcgs.rs:1674`) are the top two
   functions in the profile, and ~45% of samples are allocator/memset
   traffic, mostly the per-solve network rebuild
   (`transport.rs:165-215`). Fixes: dirty-flag skip when no child Q
   changed, skip composition when no child best improved,
   session-owned scratch network buffers. AU follows none of
   doc/perf-dps.md's destination-passing idioms today.
3. **Hot-path clones**: `action_cache.get(..).to_vec()` per
   expansion/rollout/exact frame (`mcgs.rs:1740,1954`,
   `exact.rs:212`); `expand_action` filters twice plus `.nth()`
   (`mcgs.rs:1743-1762`); `initial_rollout` recomputes
   transport-action descriptors per visited node (`mcgs.rs:1955`)
   that `ensure_or_stats` already caches per OR node (`mcgs.rs:1294`).
4. **Intern-key allocations**: `TermPool::intern` builds
   `(op.clone(), children.to_vec())` before the hit check
   (`terms.rs:91-95`); `ContextStore::intern` allocates per lookup
   (`space.rs:98-115`); `derive_child_context` allocates per child
   pair (`space.rs:398-418`).
5. **`build_best_term` unmemoized** (`terms.rs:479`): re-walked per
   generalize seed per child creation; a session-level class-to-term
   cache makes it O(1) after first use.
6. **`or_postorder` re-collects child lists per cursor step**
   (`mcgs.rs:1041-1054`), O(k^2) allocations per node, once per run.
7. **Snapshot best-term fixpoint is a full scan**
   (`egraph_api.rs:306-365`); a worklist cuts it on large e-graphs.

## Reproduction

The fuzz and repro harness is a scratch crate outside the repo; the
deterministic triggers are recorded above in full (graph shape plus
query) and reproduce from a fresh harness in minutes. The P0-1
self-contained cost-matrix search was left pending; the in-tree repro
is deterministic regardless.
