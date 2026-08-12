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
public shell. Each shell function evaluates a verified exec twin of the
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
`DenseId31/63::new` guarded like their `define_id*!` twins; inherent
`SortedVecCursor::step` renamed `step_unchecked` and `pub(crate)` (inherent
resolution silently bypassed the guarded trait impl); production
`ListArena::splice` gains the `dst != src` assert its verified twin has;
production `from_sorted` gains the sortedness `debug_assert` that
`containers-verus/src/bplus.rs`'s doc comment falsely claims exists.

**2. Pilot on `Vec`** — the hot-path stress case, so the open perf question
resolves first. `ContainerError` (`non_exhaustive`: `CapacityExhausted`,
`DepthLimit`, `ForkLimit`, `InvalidToken`, `NotSorted`, `SameRing`,
`IndexOutOfBounds`); exec precondition twins (`can_mark`, `can_push`) with
`ensures b == spec`; `try_` wrappers proved total; and the reservation
witness for hot loops — `reserve(n) -> Result<PushBudget>` checked once,
`push_within(x, &mut budget)` total and branch-free, the bound ghost-carried
by the witness. Exit criterion is a measured `perf_gate` row for the shell
path within the migration ceiling on the baseline machine; if the witness
cannot hold parity, stop and rethink here, before the sweep.

**3. Sweep** the remaining containers and cursors. Two designed items:
`splice`'s different-rings check becomes an O(1) per-list ring-id witness in
the header (candidate space: the padding the `ListHead` widening measured; if
31-bit ids have no free padding, that is a measured layout decision, not an
assumption), replacing the O(ring) debug walk; `from_sorted` pays an O(n)
sortedness check against its O(n log n) build. `step`-shaped APIs become
`next() -> Option`. The misuse suite converts container by container.

**4. Visibility flip.** Every `requires`-carrying and guard-panicking core fn
to `pub(crate)`; allowlist drains to empty. From here `rustc` enforces the
property; the gates only catch accidental re-`pub`s.

**5. Consumer migration and parity re-scope.** E-graph call sites move to
`?`/`unwrap`/witness forms, with the audit's per-site justifications becoming
comments at the `unwrap`s. Production grows `try_` twins where the
differential suite needs them, and the parity claim re-scopes to a pinned
correspondence: verus `Err(X)` exactly where production panics, asserted by
the misuse suite. Trust ledger and design docs move in the same commits.

## Out of scope, tracked

- `next_id_from`'s release-mode id-exhaustion guard stays disclosed-and-priced
  (the measured 21.8%); revisit only with a new measurement.
- The `exec_tnum` prototype retirement (same divergence disease, different
  crate) is its own branch.
- Byte-accounting verification and the key-model axiom endgame are unchanged
  (`verify-byte-accounting.md`, `key-model-tcb.md`).
