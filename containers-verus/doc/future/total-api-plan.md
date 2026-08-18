# Total public API: no partial function leaves the crate

The target property: the public surface of `containers-verus` contains only
total functions. A function with a `requires` clause is partial — Verus erases
the clause at runtime, so an unverified caller that violates it gets whatever
the body does, which today ranges from a clean panic (index bounds on `std`
vecs) through silently wrong answers (`SortedVecCursor::new` on unsorted
input) to undefined behavior (`bplus_layout`'s `get_unchecked` primitives).
The 2026-08-12 audits (PR #76 review) established that no *reachable* call
site violates a precondition today; this plan makes that a property of the
type system rather than of an audit.

The mechanism throughout: a partial verified core (`pub(crate)`), and a total
public shell. Each shell function evaluates a verified exec counterpart of the
core's precondition and branches; Verus proves the branch discharges the
core's `requires`, so the check and the contract cannot drift — the exact
failure mode that produced the `exec_tnum` divergence. Wrappers return
`Result<_, ContainerError>` for operational exhaustion; contract violations
that indicate caller bugs keep panicking guards, now unreachable from outside
except through the shell that proves them impossible.

## Phases

Each phase lands separately, workspace green (verify, tests, perf gate, count
gates) at every boundary.

**0. Gates first.** Two CI greps in `verus.yml`, in the `external_body`
count gate's style, with an allowlist file
(`containers-verus/partial-api-allowlist.txt`) naming today's exceptions:
- no `pub` exec fn with a `requires` clause outside the allowlist;
- no `pub` fn lowering to `unsafe`/`get_unchecked` outside the enumerated
  `external_body` primitives.
Phases 1–4 drain the allowlist to empty; the gates then hold unconditionally.

**1. The six audited gaps**, closed without API redesign:
`bplus_layout` primitives and the `NodeLayout` accessors over them to
`pub(crate)` (contract proptests move in-crate — the only UB-capable external
surface); `SortedVec.data` private behind sorted/sorting constructors;
`DenseId31/63::new` guarded like their `define_id*!` counterparts; inherent
`SortedVecCursor::step` renamed `step_unchecked` and `pub(crate)` (inherent
resolution silently bypassed the guarded trait impl); production
`ListArena::splice` gains the `dst != src` assert its verified counterpart has;
production `from_sorted` gains the sortedness `debug_assert` that
`containers-verus/src/bplus.rs`'s doc comment falsely claims exists.

**2. Pilot on `Vec`** — the hot-path stress case, so the open perf question
resolves first. `ContainerError` (`non_exhaustive`: `CapacityExhausted`,
`DepthLimit`, `ForkLimit`, `InvalidToken`, `NotSorted`, `SameRing`,
`IndexOutOfBounds`); exec precondition counterparts (`can_mark`, `can_push`) with
`ensures b == spec`; `try_` wrappers proved total; and the reservation
witness for hot loops — `reserve(n) -> Result<PushBudget>` checked once,
`push_within(x, &mut budget)` total and branch-free, the bound ghost-carried
by the witness. Exit criterion is a measured `perf_gate` row for the shell
path within the migration ceiling on the baseline machine; if the witness
cannot hold parity, stop and rethink here, before the sweep.

*Resolved 2026-08-12:* the pilot chose `try_extend` (one check licenses the
batch, the loop invariant carries the bound) over a borrowing
reservation-witness type: same amortization, no session-lifetime machinery,
and the row reads +1.6% against production's raw push loop (provisional,
dev machine). Revisit the witness type only if consumer profiling shows
per-element `try_push` on a path that cannot batch.

**3. Sweep** the remaining containers and cursors. Two designed items:
`splice`'s different-rings check becomes an O(1) per-list ring-id witness in
the header (candidate space: the padding the `ListHead` widening measured; if
31-bit ids have no free padding, that is a measured layout decision, not an
assumption), replacing the O(ring) debug walk; `from_sorted` pays an O(n)
sortedness check against its O(n log n) build. `step`-shaped APIs become
`next() -> Option`. The misuse suite converts container by container.

*Sweep note (2026-08-12):* `SparseSet::try_restore` is deferred: `restore`
carries a snapshot-wellformedness precondition (`sparse_set_snap_wf` over the
archived columns) that `is_valid_token` does not answer. The structural fix
is archiving snapshot-wf in `wf` as `ListArena` archives `arena_model_wf`;
until then a total restore needs an O(cap) runtime permutation check. This is
the sweep's one open item of that shape.

*Phase 4/5 mechanics (2026-08-13), from the sweep:* the 98 remaining
allowlist entries split into two conversion shapes, and the phases land
per-function-family with 5-before-4 ordering (flipping visibility before
migrating a consumer would break the e-graph build mid-history):

- *Token/allocation family* (mark, restore, new_list, prepend, append,
  add, insert, add_singleton, from_sorted, …): the `try_` sibling exists;
  the core goes `pub(crate)` and the e-graph's few, cold call sites become
  `try_*().unwrap()` with a one-line justification (the consumer asserting
  its own invariant — the audit's per-site arguments become visible code).
- *Index/capacity family* (get, set, len, push with the deferred trap, …):
  hot-path, panic-parity with production, already total-with-panic in
  behavior. These convert IN PLACE: drop the `requires`, make the check an
  explicit branch to a total diverging refuse helper (guard.rs), and the
  body's proofs pick the bound up from the branch instead of the contract.
  No consumer change, no added cost (the check already existed as the
  guard or the std bounds check), and the gate entry drains.

**4. Visibility flip.** Every `requires`-carrying and guard-panicking core fn
to `pub(crate)`; allowlist drains to empty. From here `rustc` enforces the
property; the gates only catch accidental re-`pub`s.

**5. Consumer migration and parity re-scope.** E-graph call sites move to
`?`/`unwrap`/witness forms, with the audit's per-site justifications becoming
comments at the `unwrap`s. Production grows `try_` counterparts where the
differential suite needs them, and the parity claim re-scopes to a pinned
correspondence: verus `Err(X)` exactly where production panics, asserted by
the misuse suite. Trust ledger and design docs move in the same commits.

## Drain status (2026-08-13)

The allowlist stands at 35, every entry in a named floor class with its
argument recorded in the list header: uninterp type-class obligations (no
exec counterpart is expressible), unreachable receivers (store constructors are
pub(crate) — compiler-enforced), hot sorted-input contracts (an O(n) check
would sit on the join/search hot path; debug builds assert), the
witness-pending trio (ring-id witness, snapshot-wf archival), and the
measured-decline NodeLayout calculus (refuse-branches would reinstate the
priced-out bounds checks). Everything drainable has drained: 81 → 35 across
eleven batches, each landing verified and workspace-green. The gate forbids
new entries and reports drained ones for removal.

## Drain to zero callable-partial (directive of 2026-08-14)

The standing requirement tightens: no public method with a `requires`
clause may be INVOKABLE from unverified Rust. This re-disposes two
floors that the 35-entry state treated as closed and prioritizes the
witness-pending trio. Per floor:

- **Unreachable receivers (12 diff_store entries): already satisfy the
  requirement.** No external caller can hold a receiver
  (constructors and `with_store` are pub(crate)); compiler-enforced,
  nothing to change.
- **Uninterp type-class obligations (`map.rs::new`'s key-model law,
  `tagged.rs` laws, `guard::check_precondition`,
  `capture_bits::set_true`): no exec counterpart is expressible.** These are
  trait-law trust items of the same kind as `Ord` for a sorted map:
  the requires binds the TYPE's laws, not a runtime condition a
  wrapper could test. `check_precondition` is itself the
  panic-on-violation wrapper the directive asks for. Documented in the
  key-model TCB; unchanged.
- **Hot sorted-input contracts (`bplus_search::{find_ge,find_gt}`,
  `sorted_vec_cursor::{new,seek}`): convert to requires-free
  conditional contracts. DONE.** The bodies are total already (a
  bisection or gallop on unsorted input returns some index in
  `[0, len]` without panicking); the sortedness hypothesis moved from
  `requires` into the ensures as an implication
  (`sorted(keys) ==> characterization`), with `r <= keys.len()` and
  the cursor's position bounds kept unconditional. Zero runtime cost,
  public signatures unchanged; `leaf_find_ge`/`find_child` and the
  cursor theorems discharge the hypothesis and keep the full
  contract. `key` also dropped its `cursor_wf` requires (its runtime
  refusal already covers exhaustion). This replaced the declined O(n)
  runtime check with a weakening, not a wrapper; the
  DOCUMENTED-UNCHECKED allowlist floor is empty.
- **Measured-decline NodeLayout calculus (10 bplus_layout entries):
  split visibility instead of adding refuse-branches.** The public
  `NodeLayout` name stays (consumers must name layout types as
  parameters) but becomes consts/types only; the requires-carrying
  node operations move behind pub(crate) (a crate-internal operations
  trait), which the tree consumes as today. External code loses only
  calls it could never make soundly; the priced-out bounds checks stay
  out. Interface divergence from production (whose layout methods are
  public) recorded in the parity matrix when it lands.
- **Witness-pending trio: implement, not wait.**
  `circular_list::{splice,splice_absorb}` get the O(1) ring-id witness
  (the phase-3 designed item) so a total form can refuse same-ring
  arguments at O(1); `sparse_set::restore` gets the archive clause in
  its own `wf` so restore re-establishes snapshot well-formedness the
  way the aggregate already does, and a total `try_restore` becomes
  expressible.

End state: the allowlist holds only the compiler-enforced and
type-class floors, and every entry in it is provably not invokable
from unverified Rust or not a runtime-testable condition at all.

## Out of scope, tracked

- `next_id_from`'s release-mode id-exhaustion guard stays disclosed-and-priced
  (the measured 21.8%); revisit only with a new measurement.
- The `exec_tnum` prototype retirement (same divergence disease, different
  crate) is its own branch.
- Byte-accounting verification and the key-model axiom endgame are unchanged
  (`verify-byte-accounting.md`, `key-model-tcb.md`).
