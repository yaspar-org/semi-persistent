# Migrating the e-graph onto the verified containers

`semi-persistent-containers-verus` replaced `semi-persistent-containers` as the
e-graph's container implementation. This file records the decisions that
outlived the migration and the reasoning a future reader would otherwise have
to reconstruct. It is not a status page: the current state of the code is what
the gates in CI assert, and every number below is one a gate or a test
regenerates.

## Vocabulary used by in-code comments

Comments across `containers-verus/` and `containers-conformance/` cite
"migration plan §N", "PR 1", and "PR 2". Those refer to a working plan document
that was a process artifact and is not retained — it tracked task state, and
most of its content was either wrong by the end or is now asserted by a gate.
The vocabulary is decoded here so the references resolve to something:

- **PR 1** — build the verified crate to production's API surface, with the
  consumer untouched. Complete.
- **PR 2** — switch the e-graph onto it. Complete; that is this change.
- **"migration plan §2.x"** — the token/identity boundary work: 2.2 the
  "restorable now" `is_valid_token`, 2.4 the panic-on-misuse parity, 2.5 the
  forged-state and misuse test suites (`tests/misuse.rs` plus in-module unit
  tests), 2.6 the `u64` `ContainerId` widening.
- **"§Phase N"** — sequencing only (1.1 compat-test gates, 1.3 the canary, 4
  the flat root re-export surface, 5.x composites/SparseSet/ListArena, 6 the id
  macros, 8 B+tree, 9.x final gates). Nothing depends on the numbering.

Where a comment cites the plan for a *fact* rather than a task, the fact is
restated in this file or in `containers-verus/doc/design/`.

## Scope decisions

**Payload bounds narrowed.** The verified `Vec`/`DiffStore`/`SparseSet`/
`ListArena` require `T: Copy` (plus `Default`, wherever `restore`'s regrow must
mint a filler) where production accepted `T: Clone`. Every payload these hold in
this workspace is `Copy`; genuinely non-`Copy` payloads live in `AppendOnlyVec`,
which keeps production's unbounded `T`, and in `SpMap`, whose keys and values are
`Clone`. This is a real narrowing, accepted because nothing needed the
generality — the canary's `aov_clone_only_payload` fixture pins the Clone-only
case that must keep working.

**64-bit only**, pinned by `global size_of usize == 8`.

**`SpMap::get_mut` is gone, deliberately.** Handing out `&mut` into
semi-persistent storage lets a caller mutate a slot the diff log has already
captured, which silently breaks restore. The verified `SpMap` is append-only
with shadow-on-overwrite, so a late edit is read-clone-modify-`insert` (see
`clone_key_maps` in the canary for the shape).

The one consumer call site was `OpRegistry::set_constructor`, and it did not
migrate to `insert` — the `is_constructor` flag it set is **write-only** in the
e-graph today (set, read nowhere), so the method is now a documented no-op with
identical observable behavior. That is a latent trap: the day the flag gains a
reader, `set_constructor` will silently do nothing. The note at
`egraph/src/registry.rs` says so, and the fix is to thread the value through
registration, where it is already known.

**Token semantics are stronger than production's, not equal.** Verus
`is_valid_token` means "restorable now" — identity, frame liveness, genealogy,
and counter headroom. Production checks genealogy alone and traps reuse later,
inside `restore`, via a `frame_index < frames.len()` assert. Frame indices are
REUSED after a branch cut, so the two answers genuinely differ on a token whose
frame index has been recycled: production says valid and traps on use, verus
says invalid up front. Differential tests scope the verdict comparison to
tokens production also considers restorable.

## The one deliberate memory divergence

`ContainerId` is a `u64` where production uses `AtomicU32`. Production's
counter wraps silently after 2^32 containers, and two live containers holding
the same id means one accepts the other's tokens. The `u64` is the same
algorithm over 4 billion times the range.

The cost is 4 bytes per token, which shows up as `total_bytes` = production + 16
for `ListArena` (8 per inner vec). `tracking_bytes` is byte-identical. Both are
asserted as exact constants in
`containers-conformance/tests/list_arena_differential.rs`.

Two `u32` alternatives were measured and rejected. An *absorbing poison band*
(top 2^32 reserved, counter clamped on overflow) is sound but needs a second
atomic store to actually absorb — a plain `fetch_add` climbs through the band
and wraps to live low ids — and that second store measures 21.8% slower on
constant-count push loops. A *fail-closed* `eq` measures at parity but is
outright **unsound**: `eq` is `external_body` with
`ensures b == (self.id() == other.id())`, so returning false for `self.eq(self)`
would falsify an assumed postcondition and poison every proof downstream of it.

A runtime exhaustion trap is available behind `strict-id-exhaustion`, off by
default for the same 21.8%; `debug_assert!` covers debug builds either way. The
trap's cost is real and separately reproducible — adding the same diverging arm
to production's `token.rs` degrades production identically — but note that the
*mechanism* originally recorded for it (a basic-block split in
`Vec::with_store`) was later **retracted**: it was read off a reproducer, not
off the binary criterion ran. See the retraction in
`containers-verus/doc/design/11-layout-parity.md`, and read it before citing any
instruction-shape argument from `src/container_id.rs`'s module doc, which still
narrates the retracted bisection.

## What is trusted, and why that number is gated

27 `external_body` markers by default, 5 more under `literal-types` (32 total).
Exactly ten carry contracts; the rest are contract-free, meaning nothing can be
assumed from them. The per-item argument is
`containers-verus/doc/design/02-trust-boundary.md`.

Both counts are pinned in `.github/workflows/verus.yml`, which fails the build
on any change and names the four places in the trust doc that must be updated in
the same commit. That gate exists because the count *does* move under ordinary
work: the `ListArena` `InlineStore` port took it 18 → 21, and one of those three
was contract-carrying (`data_capacity_bits`, whose `n >= len` is what makes
capture-word truncation unobservable); the B+tree hot-path work took it 21 → 26,
all five contract-carrying bounds-elision primitives in `bplus_layout.rs`,
each buying back a measured cost (trust doc §2d) and each property-tested
against the checked std form it replaces
(`containers-verus/tests/bplus_layout_proptest.rs`). A trusted-surface count
that isn't mechanically enforced drifts.

`external_body` means "hide the body, believe the signature and its `ensures`",
which is strictly weaker than `admit`. The crate contains no `admit`/`assume`,
also gated.

The group-D key-model axioms are feature-gated and were **narrowed on review**.
Axioms for `BigRational` and `OrderedFloat<f64>` were withdrawn as FALSE
against vstd's identity-iff-`==` requirement: NaN payloads and ±0.0 share an
`==` class, and `Ratio::new_raw` makes `2/4 == 1/2` across distinct
representations. Crate-local canonical wrappers (`canonical_keys.rs`) make the
requirement true by construction; regression tests pin both withdrawn-type
violations so the exclusions survive a dependency upgrade. New key types must go
through `declare_key_model_assumption!`, which pins the CI-greppable prefix,
requires a justification, and generates the requirement fuzz. The endgame that
removes these axioms entirely is `containers-verus/doc/future/key-model-tcb.md`.

## Dropped: B+tree consumer wiring

The migration originally meant to replace the e-graph's ephemeral SortedVec
rebuild indexes with incremental B+tree maintenance.
`containers-conformance/benches/incremental_vs_rebuild.rs` (20M unique ids, 10
saturation rounds) killed that:

| strategy | random arrival | ascending arrival (the e-graph's pattern) |
|---|---|---|
| rebuild: re-sort the accumulated SortedVec each round | 1.25 s | 84 ms |
| rebuild: sort + production's O(n) `from_sorted` | 1.34 s | — |
| incremental: `std::collections::BTreeSet` | ~7.3 s | 928 ms |
| incremental: production B+tree | ~7 s | 620 ms |
| incremental: verus B+tree | 6.15 s | 8.77 s |

Rebuild wins 6–11×, and — the decisive part — *identically so for
`std::BTreeSet`*. The gap is strategy-level physics (sequential re-sort
bandwidth, with pdqsort detecting runs in nearly-sorted data, versus random DRAM
probes), not implementation quality, so no amount of node-layout work makes
incremental competitive for this access pattern.

`BPlusTreeSet` therefore stays a fully verified library component with no
consumer wiring and no performance gates. Revisit only if a future e-graph
workload is *measured* to be restore-heavy (O(diff) rollback beats full rebuild)
or query/update-interleaved — the two regimes where incremental can win.

## Reading the performance evidence

Do not trust a criterion prod-vs-verus ratio from this repo's per-group
benches. Criterion's prod-then-verus layout measures heap position: whichever
arm runs second inherits a grown, fragmented `brk` heap and reads ~+18%, and
swapping the arms moves the penalty. Two "regressions" were chased that were
entirely this artifact, and one *real* regression (a missing
`#[inline(always)]`, worth 12%) hid behind the same noise for a while.

The enforced numbers are `containers-conformance/benches/perf_gate.rs`, which
interleaves the arms per sample and reduces by min, with per-row recorded
ceilings and their measured spreads in `containers-conformance/BASELINE.md`.
The full bisection, including the disassembly, is
`containers-verus/doc/design/11-layout-parity.md` — which is also where three
overstated performance claims are explicitly retracted, and worth reading for
that alone before recording a new ratio.

## Follow-ups this migration did not do

- Package-identity cutover: the verified crate still lives in
  `containers-verus/` under its own directory and package name, aliased to
  production's name at the dependency edge. Renaming it to
  `semi-persistent-containers` and retiring the old crate is a separate change,
  gated on `cargo publish --dry-run` and on vstd clearing license/deny checks.
- `containers/` (production) is still in the workspace. It is what the
  conformance crate differentials against, so it cannot be deleted until that
  evidence is no longer wanted.
- The remaining retained-container rows (`list/append_iter`, `list/splice`,
  `vec/push_pop_untracked`, tracked_vec mark-churn) live only in the criterion
  benches. Port any whose number is disputed into `perf_gate.rs` before
  treating it as real.
- Byte-accounting is trusted (group B), not proved:
  `containers-verus/doc/future/verify-byte-accounting.md`.
- The e-graph's six `Tagged` impls (`classes.rs`, `director.rs`,
  `union_find.rs`, `node_types.rs` ×3) are trusted code with no law test. The
  fuzzer they should each be stamped from is
  `containers-verus/canary/src/lib.rs::tagged_fuzzer_template`, which currently
  only exercises a fixture. This is the largest open item in the consumer-side
  trust surface: a wrong `Tagged` impl silently corrupts capture state, and the
  verified core cannot catch it.
- `OpRegistry::set_constructor` is a no-op (above). Fix before the flag gains a
  reader.
