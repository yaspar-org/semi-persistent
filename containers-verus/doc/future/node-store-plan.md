# Verifying the e-graph's node tier: caches, routing, hash-consing

The plan for replacing the remaining hand-rolled e-graph state with verified
structures, continuing `egraph-wf.md` past the class layer. It is a work
plan, not a status page: what is proved is what `cargo verus verify`
accepts.

## What remains unverified, precisely

After the class-layer swap, `EGraph`'s persistent state decomposes as:

| state | storage | logic |
|---|---|---|
| `classes: EClasses` | verified | verified (W1-W6) |
| registries, `LitValStore`, `unit_node`, `inverse_op` | verified (`SpMap`, `VecI`) | verified map contracts |
| `NodeStore.routing: TypedRouting` | verified (`AppendOnlyVec`) | UNVERIFIED (reserve/finalize protocol, entry agreement) |
| `NodeStore.{plain0..3, spair, plain_n, seq, mset, set, lit}` (ten caches) | node columns and history verified (`VecI`) | UNVERIFIED (hash-cons index: raw `hashbrown` with precomputed content hashes; key-to-node agreement; recanonicalization protocol) |
| e-matching `IndexStore` | rebuilt from scratch every round | out of scope: derived, transient, never restored |

So the gap is not storage — every persistent byte already lives in a
verified container — but the LOGIC layered on it: the routing bijection,
the hash-cons agreement, and the two-phase id mint. Those are exactly the
node-tier agreement invariants, the same species W2/W3 were for classes.

## The invariant set (N-series, continuing W1-W7)

- **N1, routing totality.** Every allocated global id has exactly one
  routing entry; an entry `(kind k, local l)` satisfies
  `l < cache_k.len()`; and the reserved-id window (between `reserve` and
  `finalize`) is at most one wide and never observable through a read.
- **N2, per-kind bijection.** For each kind, `local -> global` (stored in
  the cache row) and `global -> local` (via routing) are mutually inverse;
  locals are dense `0..cache_k.len()`.
- **N3, hash-cons soundness.** If `index_k[key] == g` then `g` routes to
  kind `k` at some `l` and the STORED row at `l` has exactly `key`'s
  content. (Soundness only: the index never lies about what a hit means.)
- **N4, hash-cons coverage up to the dirty set.** Every stored row's
  CURRENT canonical key is in the index, except rows whose children were
  remapped by a merge since the last rebuild. This is the node-tier half of
  the `wf_except(dirty)` discipline (egraph-wf stage 3); rebuild's job is
  restoring `dirty = empty`.
- **N5, history archival.** Under `PROOFS`, recanonicalization history rows
  compose with mark/restore the way every Phase-7 archive does.

W7 (no two live rows congruent at the fixpoint) stays where egraph-wf put
it: the rebuild theorem, not a step invariant. N3+N4 are its
preconditions; landing them makes W7 STATEABLE, which it currently is not.

## Trust-surface consequence, stated up front

The hash-cons index keeps `hashbrown` with the passthrough hasher — that
performance shape (precomputed content hash, `raw_entry` probes, zero
allocation) is load-bearing and a verified hash table is research-scale.
The verified form wraps it the way `SpMap` wraps its index: an
`external_body` boundary whose contract is the N3 agreement, with the key
model trivial by construction (the hash IS the stored key's field, so
"equal keys hash equal" has no axiom content). This GROWS the external_body
ledger by a small, enumerated group; the trust-surface gate's pinned counts
and `doc/design/02-trust-boundary.md` update in the same commit, which is
the gate's designed procedure. Net: the trusted code does not shrink at
this tier — it becomes contracted, monitored, and enumerated instead of
implicit.

## Stages

**N0 — monitors (days).** Stage-0 pattern: debug-build asserts after
`intern`/`finalize`/recanonicalization checking N1-N3 point-wise (the
routed row round-trips, the index hit's row matches the key). Runs under
the whole suite immediately; any firing invalidates the plan's assumptions
before proofs are attempted.

**N1 — verified keyed cache (one to two weeks).** A `containers-verus`
container: verified `VecI` node column + optional history + the wrapped
index, with `wf` = N3 for one cache plus dense-local bookkeeping, and a
total API (`try_intern -> (local, fresh)`, `get`, the recanonicalization
update as one contracted operation, Phase-7 mark/restore). Generic over
the row type through a `NodeRow` trait (global id + canonical key
projection) so one container serves the fixed-arity (`[G; K]` const
generics), variable-arity (span into a verified pool), and literal shapes.
Calibration: `SpMap` plus `bplus_search` were each about this size.

**N2 — verified router (days).** `TypedRouting` moves into the kernel:
the two-phase `reserve`/`finalize` mint becomes a contracted protocol (the
reserve window in the spec state, N1's window clause), entries append into
the existing verified `AppendOnlyVec`, and the in-range clause is proved.
The kind enum stays consumer-side; the router is generic over a
`Copy + Tagged` entry the consumer interprets.

**N3 — the NodeStore aggregate (the big one; eclasses-scale).** Compose
router + ten cache instances with N1/N2/N3 as the joint `wf`, exactly the
`eg_model_wf` architecture: agreement clauses over component views, a
Phase-7 joint archive keyed on component snapshot stacks, total public
surface. The ten-field shape lives in the kernel the way `EClasses`'
five-field shape does; the consumer's `NodeIds` bundle maps onto it. The
routing-bijection preservation across `intern` is the centerpiece proof,
the analogue of merge's W3 discharge.

**N4 — the swap (days, given N3).** `node_store.rs`, `caches.rs`,
`typed_routing.rs` become adapters in the `classes.rs` pattern: production
signatures, pinned panic messages, compile-time layout asserts, zero
changes above `NodeStore`'s API. Conformance differential and layout pins
in `containers-conformance`; `saturate_bench` and `allocprobe` before and
after with the criterion baseline protocol; the acceptance bar is the
swap precedent's: inside the documented environmental band, both signs
present.

**N5 — `wf_except(dirty)` for the whole EGraph (opens stage 3).** With
W1-W6 and N1-N3 both machine-checked, state the dirty set as a spec
object: `merge` adds to it (N4's exception set), each rebuild iteration
shrinks it, empty dirty set implies full `wf`. This is the loop invariant
a verified rebuild needs and the point where W7 becomes a statable
theorem. Proving W7 itself remains postponed per egraph-wf.

**Cleanup, any time after N0:** `egraph::union_find`'s `UnionFind` struct
is dead code since the class-layer swap (the adapter owns the proof
columns; nothing constructs it outside its own tests). Retire the struct,
keep `Justification`/`ProofBuf`, and note the removal in the module doc.

## Order and what would change it

N0 first, always. N1 before N2 only because the cache is the riskier
container (const-generic rows, the wrapped index, the recanonicalization
contract) and derisking it early bounds the plan; they are independent.
N3 requires both; N4 requires N3; N5 requires N4 plus egraph-wf stages
1-2 (done). If N0's monitors fire on the existing suites, stop and fix:
a violated N2 or N3 means the informal argument is wrong and N3's proofs
would chase a falsehood. If N1's wrapped-index contract costs measurable
throughput on `saturate_bench` (the intern path is the hot path of
`add_*`), the fallback is recorded now: keep the raw index consumer-side
and land N3 with the index clauses stated over a ghost map the adapter
maintains — weaker (the agreement becomes monitored, not proved) but it
preserves the performance floor, and the difference is honest in the
ledger.
