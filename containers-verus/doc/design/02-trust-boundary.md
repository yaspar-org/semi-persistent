# The Trust Boundary: What Is `external_body`, and Why

*The crate is verified with **no `admit`s and no `assume`s**. The only code the
verifier takes on trust is a small set of items marked
`#[verifier::external_body]` (their bodies are hidden; only their signatures /
`ensures` are believed) plus a small set of `broadcast axiom fn`s (one in the
default build — the SpMap index hasher fact — and five more behind the
`literal-types` feature). This chapter enumerates exactly what is trusted and,
for each, why it is trusted rather than proved.*

*Counts, by configuration:*

| configuration | `external_body` markers | axiom fns |
|---|---|---|
| default features | **21** (3 structs + 18 functions) | **1** (`builds_valid_hashers::<IndexHasher>` — SpMap's index hasher; mirrors vstd's shipped `RandomState` axiom) |
| `literal-types` | **26** (adds 5 opaque type registrations) | **6** (adds `obeys_key_model` for BigInt, BigUint, CanonicalF64, CanonicalRational, BitsF64) |

*Counts re-derived 2026-08-06 by grepping `#[verifier::external_body]` and
splitting on the `literal-types` gate (`external_specs.rs` is the only gated
module). They were 18/23 before the `ListArena` `InlineStore` port, which added
three: `ListArena::tracking_bytes`, `ListArena::total_bytes` (both group B, both
spec-free), and `data_capacity_bits` (group B, contract-carrying — see §2c).
Only the last of the three changes the assumed-fact inventory.*

*For the migration reviewer, the delta against the pre-migration merge
base (7 markers: `struct ContainerId` + `new` + `eq`, `check_precondition`,
`ForkHistory::heap_bytes`, `Vec::tracking_bytes` + `total_bytes`) is
**+11 default markers**: 4 byte reporters (`CaptureBits`/`ParallelStore`/
`InlineStore::heap_bytes` — spec-free — §2a), 2 shrink helpers
(`shrink_vec_capacity`, `shrink_aov_capacity` — contract-carrying, §2b),
`clone_key_exact` (§3.5 D), `values_equal` + the debug ring-walk (§3.5 E),
`ListHead::white_box_head` (contract-free test accessor, §3.5 E), and
`ExIndexHasher` + `ExFoldHasher` (contract-free opaque type registrations for
the SpMap index hasher, §3.5 D-hasher) — plus **+1 default axiom**
(`builds_valid_hashers::<IndexHasher>`). Of these, the
**load-bearing contract-carrying additions are exactly three**: the two
shrink helpers' data-preservation `ensures` and `clone_key_exact`'s
clone-identity `ensures`. Everything else added is contract-free (nothing
assumable from it) or an explicitly enumerated axiom.*

[Design Table of Contents](00-table-of-contents.md)

## 0. What `external_body` means

`#[verifier::external_body]` tells Verus: *do not look inside this function; take
its signature (and any `ensures`) as an axiom.* It is the mechanism by which
verified code meets the parts of the world the logic cannot describe: hardware
integer casts, process-global state, the allocator, opaque identity. It is
strictly weaker as a trust statement than `assume`/`admit` (which inject
arbitrary facts mid-proof); an `external_body` function still has a typed
signature its callers are checked against, and where it carries an `ensures`
that contract is the *only* thing trusted.

A healthy verified crate drives `external_body` down to the irreducible
boundary. This crate has 21 default-build markers: 3 ContainerId + 11
capacity/byte diagnostics and shrink helpers + `check_precondition` +
`clone_key_exact` + `values_equal` + the debug ring-walk +
`white_box_head` + the `ExIndexHasher` and `ExFoldHasher` registrations
(5 more behind `literal-types`, for 26). The casts that were *eliminated* (the
`IndexLike`/`DenseId` integer casts) are described in §3.

The groups differ in kind, and the distinction is the point of this chapter:

- **Group A is trusted by *design*.** It models things that are external in
  reality: a process-global atomic and an intentionally-opaque identity. Even
  in principle we do not want to "prove" them; doing so would either be
  meaningless (no spec) or would expose an abstraction we deliberately keep
  closed. These are permanent.
- **Group B is trusted by *unmodeled capacity*.** `Vec::capacity` /
  `shrink_to` / `size_of` have no vstd specs. The byte reporters are spec-free
  diagnostics; the shrink helpers carry a data-preservation contract. Partly
  provable when vstd grows capacity specs; the
  [byte-accounting feature request](../future/verify-byte-accounting.md)
  scopes the reporter half.
- **Group C is one trusted runtime-trap primitive** (`check_precondition`). It
  carries a `requires` (so it is load-bearing in the proof, not spec-free) and
  is external only because its body uses the panic-formatting machinery the
  logic does not model: the same reason `vstd`'s own `runtime_assert` is
  external. Permanent, and minimal.
- **Group D carries external key-model facts** (`clone_key_exact`, plus the
  feature-gated literal-type axioms in `external_specs.rs`). Trusted because
  the facts are about foreign deterministic value types.
- **Group E is unverified glue**: `values_equal`, the debug-only ring walk,
  and the ordinary-Rust delegation shims outside `verus!{}`.

## 1. Group A: `ContainerId` (trusted by design) — 3 items

`ContainerId` is the per-container identity used to reject a `restore` token
minted by a *different* container (`vec.rs` / `append_only_vec.rs`:
`token.container_id.id() == self.id.id()` inside `is_token_valid_spec`). It is
three trusted items.

### 1a. `struct ContainerId`: opaque identity

```rust
#[verifier::external_body]
pub struct ContainerId { raw: u64 }
//   pub uninterp spec fn id(self) -> nat;
```

(The runtime payload widened from production's `u32` to `u64` as part of the
checked-allocation decision below.) The struct is `external_body` so its `raw`
field is invisible to the verifier;
the only thing specs may say about a `ContainerId` is its abstract
`id(): nat`, declared **`uninterp`** (uninterpreted, deliberately given no
definition). **Why not proved:** there is no theorem here; a struct has no
contract. This is a *modeling choice*: we want identity to be abstract so that
no proof can accidentally depend on the concrete representation. Making
`raw` visible would buy nothing and couple proofs to the bit pattern.

### 1b. `ContainerId::new`: process-global atomic

```rust
#[verifier::external_body]
pub fn new() -> ContainerId {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    ContainerId { raw: next_id_from(&NEXT) }   // plain fetch_add, u64-wide
}
```

The allocator is a **plain `AtomicU64::fetch_add`** (`next_id_from`, outside
`verus!{}`) — production's exact algorithm, widened from production's
`AtomicU32` to `u64`. Uniqueness of live ids rests on that width: 2^64
allocations is ~584k years at a million containers per second, 4 billion times
production's own 2^32 wrap bound. A runtime exhaustion trap is available behind
the off-by-default `strict-id-exhaustion` feature; it is off by default because
branching the freshly minted id to a diverging arm costs +21.8% on
constant-count push loops (bisection in `doc/design/11-layout-parity.md`), and a
debug-build `debug_assert!` covers the boundary regardless. Exhaustion is
unit-tested by parking a counter at the boundary (`container_id.rs` in-module
tests). **Why not proved:** it
reads and mutates a **process-global `AtomicU64`**, a
side effect on mutable global state that lives entirely outside Verus's ghost
world. The functional logic reasons about pure transformations of tracked state;
a `static` atomic counter is, by construction, not tracked state. There is also
**no `ensures`** to discharge: the property one would want ("each call yields a
fresh id") is a *stateful temporal* fact about the global counter, which this
signature cannot even express. To make distinctness *provable* one would replace
the atomic with a `tracked` ghost monotone counter threaded as a linear resource
through every constructor (the upgrade sketched in
[Ch. 3 §5](03-fork-history.md)), but (i) the atomic read itself would remain
external regardless, and (ii) **nothing in the crate consumes distinctness** (see
§1d). So the upgrade proves an unused property at the cost of rippling the entire
construction API. We keep the lean encoding by deliberate decision.

### 1c. `ContainerId::eq`: the one trusted axiom

```rust
#[verifier::external_body]
pub fn eq(self, other: ContainerId) -> (b: bool)
    ensures b == (self.id() == other.id())
{ self.raw == other.raw }
```

This one *has* a contract, and it is the single load-bearing axiom in Group A:
"the runtime `==` on the hidden `raw` reflects ghost-`id()` equality." **Why not
proved:** the body compares `self.raw == other.raw`; the `ensures` speaks of
`self.id() == other.id()`. Bridging them requires knowing `id()` is a function of
`raw`, but `id()` is `uninterp` *on purpose* (§1a). So `eq` *axiomatizes* the
bridge. We could make it provable by defining `id(self) == self.raw as nat`, but
that re-exposes the representation §1a intentionally hides. The axiom is
minimal, local, and is exactly what the cross-container guard relies on.

### 1d. Why Group A is sound to trust

The container check is **not on the correctness-critical path.** The headline
`restore` theorem (`view() == snapshots[token.frame_idx]`) and all of branch-cut
safety ([Ch. 3](03-fork-history.md)) hold *without* it; the container id only
*rejects cross-container misuse*, a caller error. Concretely, no proof consumes
`new()`'s distinctness; `is_token_valid_spec` only needs the *equality
reflection* of §1c, which holds by construction for a token a container minted
from itself. The soundness-relevant direction (a token whose id matches provably
passed the check, so a foreign token is provably rejected) is exactly the §1c
axiom. Distinctness is validated at runtime instead: `container_id_new_is_distinct`
and `cross_container_token_rejected` in
[`tests/external_body_contract_fuzz.rs`](../../tests/external_body_contract_fuzz.rs)
mint thousands of ids and check end-to-end that one container rejects another's
token.

## 2. Group B: capacity introspection (trusted by unmodeled capacity) — 11 items

Verus/vstd model a `Vec`'s element sequence (`@`) but not its **allocation**:
`capacity()`, `shrink_to`, and `size_of::<T>()` have no specs. Everything that
reads or manages capacity is therefore `external_body`. Three sub-kinds:

### 2a. Byte reporters (no `ensures`; diagnostic) — 8 items

Production parity (Phase 9.2): all report the CAPACITY-based allocation
footprint using exactly production's formulas.

```rust
// vec.rs
#[verifier::external_body]
pub fn tracking_bytes(&self) -> usize {
    self.diff_log.capacity() * size_of::<(T, I)>()
        + self.frames.capacity() * size_of::<Frame<I>>()
        + self.forks.heap_bytes()
}
#[verifier::external_body]
pub fn total_bytes(&self) -> usize {
    size_of::<Self>() + self.store.heap_bytes() + self.tracking_bytes()
}
// fork_history.rs
#[verifier::external_body]
pub fn heap_bytes(&self) -> usize { self.origins.capacity() * size_of::<ForkOrigin>() }
// capture_bits.rs
#[verifier::external_body]
pub fn heap_bytes(&self) -> usize { self.words.capacity() * size_of::<u64>() }
// parallel_store.rs (DiffStore impl)
#[verifier::external_body]
fn heap_bytes(&self) -> usize {
    self.data.capacity() * size_of::<T>() + self.captured.heap_bytes()
}
// inline_store.rs (DiffStore impl)
#[verifier::external_body]
fn heap_bytes(&self) -> usize { self.data.capacity() * size_of::<T::Repr>() }
// list.rs (ListArena; added by the InlineStore port) — sums the two inner vecs
#[verifier::external_body]
pub fn tracking_bytes(&self) -> usize {
    self.heads.tracking_bytes() + self.nodes.tracking_bytes()
}
#[verifier::external_body]
pub fn total_bytes(&self) -> usize {
    self.heads.total_bytes() + self.nodes.total_bytes()
}
```

The two `ListArena` reporters are `external_body` only because the `+` would
otherwise carry an overflow obligation that is not proof content (a real footprint
never approaches `usize::MAX`) and because they forward to already-external
reporters. They are the production side of the arena memory-parity assertion:
`containers-conformance/tests/list_arena_differential.rs` compares them against
production's identical pair, `tracking_bytes` byte-for-byte and `total_bytes` up
to the constant 16-byte `u64`-`ContainerId` delta, at any size and mark depth.

**Why not proved (today):** `capacity()` and `size_of` are unspecified in
vstd, and the functions carry **no `ensures`** — they are diagnostic
instrumentation no proof reads. **Partially provable in principle** (a ghost
byte model with saturating arithmetic; the
[byte-accounting feature request](../future/verify-byte-accounting.md) scopes
it), but the capacity read itself stays external until vstd models it.
Runtime validation: the differential trace `differential_bytes`
(tests/differential.rs) checks `tracking_bytes` agrees **exactly** with
production over randomized push/set/pop/mark/restore traces (identical
element layouts + deterministic std::Vec growth make exactness meaningful
there), and `total_bytes` respects a lower-bound floor (struct + tracking +
data). The store-side reporters (`ParallelStore`/`InlineStore`/
`CaptureBits::heap_bytes`) are NOT compared exactly against production —
the u64 `ContainerId` and word-at-a-time CaptureBits growth intentionally
differ from production's representation, so only the formula shape is
parity, not the number. The smoke test `byte_counters_are_consistent`
(external_body_contract_fuzz.rs) checks total ≥ tracking, monotonicity,
no panic.

### 2b. Capacity-shrink helpers (contract-carrying) — 2 items

```rust
// parallel_store.rs — shared by InlineStore::shrink_if
#[verifier::external_body]
pub(crate) fn shrink_vec_capacity<T>(data: &mut Vec<T>, factor: usize, headroom: usize)
    ensures data@ == old(data)@,
{ if data.capacity() > factor.saturating_mul(data.len()) { data.shrink_to(headroom.saturating_mul(data.len())); } }

// append_only_vec.rs — production's AppendOnlyVec variant
// (condition cap > len*factor + headroom, target len + headroom)
#[verifier::external_body]
fn shrink_aov_capacity<T>(data: &mut Vec<T>, factor: usize, headroom: usize)
    ensures data@ == old(data)@,
```

**Why not proved:** `Vec::capacity`/`shrink_to` are unmodeled. The trusted
contract is exactly "the element sequence is unchanged" — the std-documented
behavior of `shrink_to`. Provable when vstd specs capacity ops. Runtime
validation: `shrink_preserves_vec_contents` / `shrink_preserves_aov_contents`
(external_body_contract_fuzz.rs) drive both helpers through the public
`mark(ShrinkPolicy::IfOverallocated)` surface across random contents,
overallocation levels, and `(factor, headroom)` policies, asserting the
element sequence is unchanged — so every contract-carrying trusted item in
the crate now has a contract-level runtime test.

### 2c. `data_capacity_bits` (contract-carrying) — 1 item

```rust
// parallel_store.rs
#[verifier::external_body]
pub(crate) fn data_capacity_bits<T>(data: &Vec<T>) -> (n: usize)
    ensures n >= data@.len(),
{ data.capacity() }
```

**Why not proved:** `Vec::capacity()` is unmodeled, exactly as in §2b. **Why it
is load-bearing rather than diagnostic:** the `ensures n >= data@.len()` is what
makes capture-word truncation invisible to `captured()` — every flag a caller can
still observe sits at an index below `len <= capacity`, so dropping the words
above capacity cannot change any observable answer. A proof reads this contract;
it is not instrumentation.

The trusted statement is the std-guaranteed `Vec` invariant `capacity() >= len()`,
which is about as safe as an unmodeled-capacity assumption gets — it is weaker
than §2b's, since it asserts an inequality rather than preservation of contents.
Provable when vstd specs capacity ops.

## 2.5. Group C: the runtime-guard primitive (`check_precondition`) — 1 item

```rust
#[verifier::external_body]
pub fn check_precondition(cond: bool, msg: &str)
    requires cond,
{
    if !cond { panic!("containers-verus: precondition violated: {}", msg); }
}
```

This one item (`guard.rs`) carries a `requires cond` and is **load-bearing**:
public methods whose preconditions a non-Verus caller could violate by silent
integer wrap (e.g. `restore` past the `u32` fork-history limit, `push`/`add`
past the index type, `insert` past `usize`) call it at entry. A *verified*
caller discharges `cond` from the method's own `requires`, so the branch is
provably dead for them and behavior is unchanged; an *unverified* caller who
violates the precondition gets a descriptive panic instead of corruption.

**Why not proved:** the body's `panic!` uses the format machinery Verus does not
model (`core::panicking::panic_fmt` has no spec). This is exactly why `vstd`'s
own `runtime_assert` is `external_body` too. The `requires cond` *is* checked at
every call site, so the trusted part is only "the body panics when `!cond`",
which is a one-line `if`. Nothing algorithmic hides here. (See
[Ch. 3 §5](03-fork-history.md) for the `u32` fork-history limit these guards
protect, and the `restores_remaining()` query that reports the headroom.)

## 3. What used to be here: the casts (now eliminated)

For contrast: the `IndexLike::as_usize` / `try_from_usize` casts on the primitive
integers (`u8`/`u16`/`u32`/`u64`/`usize`) and the `DenseId::as_usize` casts
*were* `external_body` (they wrap machine-integer `as` casts) and have now been
**proved**, removing 10 items from the trust surface:

- `u8`/`u16`/`u32` widening (and the guarded narrowings of `try_from_usize`)
  verify directly; Verus models these casts.
- `u64` and `DenseId63` (a `u64` payload) rely on the cast being the value
  identity on a 64-bit host: `usize::MAX == u64::MAX`. This is discharged by
  `index_like::lemma_u64_usize_64bit` over the crate-wide `global size_of
  usize == 8` pin, and the whole `u64`/`usize` index path is already
  `#[cfg(target_pointer_width = "64")]`-gated, so verifying them adds **no new
  assumption** beyond the existing target gate.

The lesson (recorded in the [proof attempts log](proof-attempts-log.md)): "wraps a cast" is not
the same as "must be trusted." A cast with a value-preserving `ensures` is
usually provable once the host-width fact is pinned; only genuine side effects
(§1b), intentional abstraction (§1a/§1c), and spec-free plumbing (§2) are the
real boundary.

## 3.5. Groups D and E: migration-parity trusted surfaces

The production-parity work (see `doc/migration/README.md`) adds two trusted
surfaces of a different kind, enumerated here so the ledger stays complete.

### Group D: external key-model facts — 1 `external_body` item + planned specs

**`clone_key_exact` (map.rs, `external_body`, contract-carrying):**

```rust
#[verifier::external_body]
fn clone_key_exact<K: Clone>(key: &K) -> (r: K)
    requires obeys_key_model::<K>(),
    ensures r == *key,
{ key.clone() }
```

This carries requirement (3) of vstd's hash-table key model — "the executable
`Key::clone` produces a result identical to its input" — which `SpMap` already
assumes for every key type via `obeys_key_model::<K>()` (`new`'s
precondition, threaded through `wf`). vstd states that requirement in prose on
the `uninterp obeys_key_model` and provides no lemma projecting it out, so
this helper carries it as its contract. **No NEW assumption** beyond what
`obeys_key_model` already asserts.

**Landed (feature `literal-types`, Phase 9.4 — `src/external_specs.rs`):**
four `broadcast axiom fn`s (mirroring vstd's own primitive-type key-model
axioms) giving `obeys_key_model::<T>()` for `num_bigint::BigInt`,
`num_bigint::BigUint`, and the two crate-local canonical wrappers
`CanonicalF64` / `CanonicalRational` (`src/canonical_keys.rs`), plus the
four opaque `external_type_specification` registrations required to name
the types in specs (contract-free — they count as `external_body` markers
but assume no semantics).

The credibility argument is NOT mere determinism — vstd's requirement (2)
demands `==` classes be singletons up to value identity. For BigInt/BigUint
the exec `eq` is STRUCTURAL (digit-vector + sign comparison) over the
crate's normalization invariant (no trailing zero limbs, `NoSign` iff zero,
`debug_assert!`ed in the impls themselves), so structural equality of a
canonical representation is value identity; the assumption reduces to
"num-bigint maintains its own documented invariant".

**Withdrawn (would have been FALSE):** `BigRational` and
`OrderedFloat<f64>` do NOT obey the key model and get no axiom.
`OrderedFloat`'s `eq` puts all NaN bit patterns (and ±0.0) in one `==`
class; `Ratio::new_raw` makes non-reduced values reachable and `eq` is
mathematical comparison, so raw `2/4 == 1/2` across distinct
representations — both violate requirement (2) outright. Regression tests
in `tests/compat_map.rs::key_model_violations` DEMONSTRATE each violation
so the exclusions stay justified against future crate upgrades.

**Replacements:** the crate-local canonical wrappers (`canonical_keys.rs`)
restore float/rational keying with requirement (2) TRUE BY CONSTRUCTION —
`CanonicalF64` is a `struct { bits: u64 }` whose only constructor folds all
NaNs to one encoding and −0.0 to +0.0, with derived `Eq`/`Hash` over the
single field (its `==` IS bit identity; no foreign code participates in
its equality at all); `CanonicalRational` holds a reduced,
positive-denominator `BigInt` pair produced only via `Ratio::new`, so one
representation per rational is reachable and derived structural equality
is value identity (resting on the same normalized-`BigInt` argument as the
BigInt axiom). Their axioms remain axioms only because `obeys_key_model`
is `uninterp` — nothing can be proved to satisfy it, not even a type where
the property holds by construction.

**The forcing function for future key types:**
`declare_key_model_assumption!` (exported from `external_specs.rs`). A
verified consumer introducing a new key type cannot discharge `SpMap::new`'s
`requires obeys_key_model::<K>()` without an axiom (the predicate is
`uninterp`); the macro makes that unavoidable act disciplined — it pins the
`axiom_key_model_` name prefix (compile-time checked, CI-greppable),
requires a justification string embedded in the generated docs, and
generates a requirement-level fuzz test (hash determinism, clone identity,
and `==`-iff-representation-identity over a caller-supplied generator and
representation observable — the exact failure mode that sank the withdrawn
axioms). Exercised end-to-end in `tests/key_model_macro.rs`.

Feature-gated — `cargo verus verify` passes with and without
`literal-types` (both **1399 verified, 0 errors** as of 2026-08-07, re-measured
for this audit; the axioms add obligations only to their users, so the two
configurations agree fact-for-fact). Runtime validation (`tests/compat_map.rs::literal_keys`): an
SpMap-vs-HashMap oracle trace, **plus fuzz tests of the key-model
requirements themselves** — eq-coherence across construction paths with
representation-agreement checks (requirement 2's falsifiable observable),
hash determinism (1), clone identity (3). The oracle trace alone cannot
detect an identity/`==` mismatch (both maps use the same `Eq`/`Hash`);
the requirement-level fuzzing is what tests the assumed facts.

**D-hasher: `axiom_index_hasher_builds_valid_hashers`
(src/hasher_spec.rs, default build — 1 axiom + the `ExIndexHasher` and
`ExFoldHasher` registrations).** `SpMap`'s transient key index is
`std::collections::HashMap<K, usize, IndexHasher>`, where `IndexHasher` is an
8-byte crate-local `BuildHasher` carrying an explicit seed and delegating to
foldhash's `fast` family — the same hash ALGORITHM production's `Map` uses
(hashbrown 0.17's `DefaultHashBuilder` is a newtype wrapping
`foldhash::fast::RandomState`). vstd models `std::HashMap<K, V, S>`
generically over any `S: BuildHasher` (gated on `builds_valid_hashers::<S>()`),
and ships exactly one instance of that predicate — an `admit()`ed axiom for
std's `RandomState`. This axiom is its mirror image: same shape, same strength,
and a *weaker* assumption, since `IndexHasher` stores its seed by value at
construction, making `build_hasher` a pure function of that seed. Owning the
type is also what makes the seed configurable (`SP_HASHER_SEED`,
`set_default_seed`, `IndexHasher::with_seed`) with no added trust: the seed
rides in `Default`, which is the constructor vstd already specs generically
over `S: Default` — vstd does not spec `HashMap::with_hasher`.
`builds_valid_hashers` asserts only that the hasher is byte-deterministic
(output depends solely on the `Hash`-fed bytes) — NOT collision-freedom or
any distribution property, neither of which a HashMap's correctness needs.
`IndexHasher` is an ordinary seeded-then-deterministic `BuildHasher`, exactly
like std's `RandomState`; they differ only in the hash function, which the model
does not observe. Under `hasher-random-seed` the entropy is drawn ONCE when the
seed is chosen, never per `build_hasher` call, so determinism-given-the-bytes
holds in both builds — and in the default build the seed is a compile-time
constant, so it holds without any appeal to process state.
**No proof can conclude `builds_valid_hashers` for ANY hasher** (the predicate
is `uninterp`), so vstd admits it for `RandomState` and we admit the identical
fact for `IndexHasher`. This is the whole
cost of closing the former SpMap performance exception (see
11-layout-parity.md). Unconditional (not `literal-types`-gated) because the
index is core to `SpMap`.

### Group E: unverified glue — 2 `external_body` items + ordinary-Rust shims

**`external_body` members:**

| Item | Contract | Why trusted |
|---|---|---|
| `values_equal<T: PartialEq>` (sparse_set.rs) | NONE — result is an unconstrained bool, so nothing unsound is derivable; `remove_value` promises the structural change, not which value matched | avoids threading vstd's `obeys_eq_spec` plumbing; scan behavior pinned by ported production proptests |
| `CircularList::debug_check_different_rings` (circular_list.rs) | `requires` the spec-side precondition; no ensures | debug-only runtime mirror of a spec-only precondition (O(ring) walk, gated to debug builds); the verified `splice` never depends on it |

**Ordinary-Rust items outside `verus!{}`** that delegate 1:1 to a verified
core; the trusted content is exactly "the delegation line calls the verified
method with the converted argument":

| Item | Delegates to | Why outside the proof |
|---|---|---|
| `Vec::get(impl Into<I>)` (vec.rs, bottom) | verified `get_index` | generic `Into` carries no Verus-visible input/output relation |
| `Vec::set(impl Into<I>, T)` | verified `set_index` | same |
| `guard::check_precondition_erased` | (panics) | callable from `external_body` diagnostics; no proof context |
| std `Iterator` impls for `VecViewIter` / `ListIter` | verified inherent `next` | trait impls for unmodeled std traits (each is one delegation line) |
| `white_box_*` read accessors (bplus.rs, list.rs, circular_list.rs) | immutable field borrows | `#[doc(hidden)]` oracle access for the runtime property tests (Phase 9.1 privacy closeout); read-only, cannot violate any invariant |
| `next_id_from` (container_id.rs) | (atomic allocator) | the trusted allocator behind Group A's `new`; plain `fetch_add`, no-reuse resting on `u64` width; optional trap behind `strict-id-exhaustion`, exhaustion unit-tested |
| consumer `Tagged` impls + macro expansions in egraph | verified witness instantiations | consumer crate is not run under Verus. Mitigated by the canary's shape fixtures; the per-type contract fuzzers this row assumes do **not** exist yet — see `doc/migration/README.md` follow-ups |

Every safety property behind the glue (bounds panics, capture protocol,
snapshot fidelity) is enforced by the verified core it calls; the glue cannot
bypass it.

## 4. Summary table

All 21 default-build `external_body` markers plus the 1 default-build axiom
(the `literal-types` additions are listed after):

| # | Item | Group | Trusted because | Provable? |
|---|---|---|---|---|
| 1 | `struct ContainerId` | A | opaque identity by design (`uninterp id()`) | n/a: no contract |
| 2 | `ContainerId::new` (+ `next_id_from` allocator) | A | process-global atomic side effect; no `ensures`; no-reuse from `u64` width (optional trap behind `strict-id-exhaustion`) | no (side effect) |
| 3 | `ContainerId::eq` | A | bridges to an intentionally-`uninterp` `id()` | only by un-abstracting; declined |
| 4 | `Vec::tracking_bytes` | B | capacity + `size_of` unmodeled; no `ensures` | partially: see feature request |
| 5 | `Vec::total_bytes` | B | same | partially |
| 6 | `ForkHistory::heap_bytes` | B | same | partially |
| 7 | `CaptureBits::heap_bytes` | B | same | partially |
| 8 | `ParallelStore::heap_bytes` | B | same | partially |
| 9 | `InlineStore::heap_bytes` | B | same | partially |
| 10 | `shrink_vec_capacity` | B | `Vec::capacity`/`shrink_to` unmodeled; contract = element sequence unchanged (std-documented) | when vstd specs capacity ops |
| 11 | `shrink_aov_capacity` | B | same (AppendOnlyVec variant formula) | same |
| 11a | `ListArena::tracking_bytes` | B | capacity + `size_of` unmodeled; no `ensures`; forwards to the two inner vecs | partially |
| 11b | `ListArena::total_bytes` | B | same | partially |
| 11c | `data_capacity_bits` | B | `Vec::capacity` unmodeled; **contract-carrying** — `n >= len` is what makes capture-word truncation unobservable (§2c) | when vstd specs capacity ops |
| 12 | `guard::check_precondition` | C | body `panic!` uses unmodeled format machinery (`requires cond` is checked) | no (same reason as `vstd::runtime_assert`) |
| 13 | `clone_key_exact` | D | projects key-model requirement (3) out of vstd's prose-stated `obeys_key_model`; no new assumption | no (vstd provides no lemma) |
| 14 | `values_equal` | E | no ensures — unconstrained bool, nothing derivable; avoids `obeys_eq_spec` plumbing | by threading vstd eq specs; declined for production shape |
| 15 | `debug_check_different_rings` | E | debug-only mirror of a spec-only precondition | n/a (diagnostic) |
| 16 | `ListHead::white_box_head` | E | contract-free read-only test accessor (unpacks the niche for the white-box walkers; inside `verus!` so it needs the marker; its node-side twin `white_box_next` sits outside `verus!` and needs none) | n/a (no contract) |
| 17 | `ExIndexHasher` registration | D | contract-free opaque registration; names `IndexHasher` in specs so the hasher axiom can trigger on it | n/a (no contract) |
| 18 | `ExFoldHasher` registration | D | same — names foldhash's `FoldHasher` (`IndexHasher`'s associated `Hasher` type) so the `BuildHasher` impl type-checks under Verus | n/a (no contract) |
| — | `axiom_index_hasher_builds_valid_hashers` | D | `broadcast axiom fn` — mirrors vstd's shipped `axiom_random_state_builds_valid_hashers`; `builds_valid_hashers` asserts only byte-determinism, which `IndexHasher` satisfies at least as strongly as std's `RandomState` (seed stored by value, so `build_hasher` is a pure function of it — §3.5 D-hasher) | no (predicate is `uninterp`; vstd `admit()`s the identical fact for `RandomState`) |

`literal-types` additions (all in `external_specs.rs` / `canonical_keys.rs`):

| # | Item | Kind | Trusted because |
|---|---|---|---|
| 19 | `ExBigInt` registration | `external_body` struct, contract-free | names the foreign type in specs; no semantics |
| 20 | `ExBigUint` registration | same | same |
| 21 | `ExCanonicalF64` registration | same | same (crate-local type) |
| 22 | `ExCanonicalRational` registration | same | same |
| 23 | `ExBitsF64` registration | same | same — **staged, still unused** (the BitsF64 key is consumed only by the not-yet-done float-semantics change; +1 registration +1 axiom of deliberate forward TCB growth, see key-model-tcb.md §float-semantics) |
| — | `axiom_bigint_obeys_hash_table_key_model` | `broadcast axiom fn` — a DIRECT assumed fact | structural eq over num-bigint's normalization invariant (§3.5 D) |
| — | `axiom_biguint_obeys_hash_table_key_model` | same | same |
| — | `axiom_canonical_f64_obeys_hash_table_key_model` | same | crate-local: `==` is bit identity by construction; axiom-shaped only because the predicate is `uninterp` |
| — | `axiom_canonical_rational_obeys_hash_table_key_model` | same | crate-local canonicalization + the BigInt argument |
| — | `axiom_bits_f64_obeys_hash_table_key_model` | same | crate-local: raw-bit injective, `==` classes singleton trivially |

(`canonical_keys.rs` itself is plain unverified Rust — group E in kind — but
its entire behavioral surface is pinned by the requirement-level proptest
fuzz in `tests/compat_map.rs::canonical_key_model`.)

Plus the Group E ordinary-Rust delegation shims tabulated in §3.5.

**Bottom line.** Default build: 3 trusted-by-design (`ContainerId`,
permanent; uniqueness by checked non-wrapping allocation, distinctness
runtime-fuzzed), 11 capacity-introspection items (8 spec-free byte reporters
— production-formula parity; `tracking_bytes` differential-tested exactly,
store reporters formula-level only — 2 contract-carrying shrink
helpers, and `data_capacity_bits`), 1 runtime-trap primitive (`check_precondition`, load-bearing,
body is a one-line panic), 1 key-model projection (`clone_key_exact`, no
new assumption beyond the `obeys_key_model` precondition SpMap already
carries), 2 glue items (`values_equal` unconstrained, the debug
ring-walk diagnostic), and 1 hasher fact + its 2 type registrations
(`axiom_index_hasher_builds_valid_hashers` + `ExIndexHasher`/`ExFoldHasher`
— mirrors vstd's shipped `RandomState` axiom so SpMap's index can use
production's hash algorithm with a configurable, deterministic-by-default seed;
§3.5 D-hasher). With `literal-types`: +5 contract-free type
registrations and +5 `obeys_key_model` axioms — BigInt/BigUint (foreign,
structural-eq argument), CanonicalF64/CanonicalRational (crate-local
wrappers replacing the WITHDRAWN-as-false BigRational/OrderedFloat axioms;
requirement (2) by construction, violation regressions pin the
exclusions), and BitsF64 (raw-bit injective — the long-term float key;
CanonicalF64's fold is a pinned production-parity decision, see
key-model-tcb.md §float-semantics). Future key types must go through
`declare_key_model_assumption!` (justified + auto-fuzzed axioms). The assumed-fact inventory of the default
crate is therefore: `ContainerId::eq`'s equality reflection, the two shrink
helpers' data preservation, `data_capacity_bits`'s `capacity >= len`, and
`clone_key_exact`'s clone identity — **five** contract-carrying trusted
statements, each one line of exec code. No
`assume`/`admit` anywhere in the verified modules. No algorithmic logic is
hidden behind any `external_body`.

**Scope note.** "No `assume`/`admit`" is a claim about *this crate*. The
sibling verified crate `abstract-domains`, verified by the same CI workflow, does
carry admits — 3 as of 2026-08-06, all soundness `ensures` on `ExecUnum`
(`add`, `mul`, `from_interval`), and `ReducedProduct::add` is proved only
relative to them. That is tracked in `abstract-domains/doc/proof-status.md`.
Nothing in `containers-verus` depends on `abstract-domains`, so the two trust
statements compose without interaction; but a reviewer told "the crate has no
admits" should know which crate is meant. The plan for shrinking this further —
including eliminating the key-model axioms entirely via canonical key types
— is `doc/future/key-model-tcb.md`.

---
[← Table of Contents](00-table-of-contents.md)
