# The Trust Boundary: What Is `external_body`, and Why

*The crate is verified with **no `admit`s and no `assume`s**. The only code the
verifier takes on trust is a small set of items marked
`#[verifier::external_body]` (their bodies are hidden; only their signatures /
`ensures` are believed) plus a small set of `broadcast axiom fn`s (one in the
default build (the SpMap index hasher fact) and five more behind the
`literal-types` feature). This chapter enumerates exactly what is trusted and,
for each, why it is trusted rather than proved.*

*Counts, by configuration:*

| configuration | `external_body` markers | axiom fns |
|---|---|---|
| default features | **27** (3 structs + 24 functions) | **1** (`builds_valid_hashers::<IndexHasher>`: SpMap's index hasher; mirrors vstd's shipped `RandomState` axiom) |
| `literal-types` | **32** (adds 5 opaque type registrations) | **6** (adds `obeys_key_model` for BigInt, BigUint, CanonicalF64, CanonicalRational, BitsF64) |

*Counts re-derived by grepping `#[verifier::external_body]` and splitting
on the `literal-types` gate (`external_specs.rs` is the only gated
module); the CI gate (`.github/workflows/verus.yml`) pins them and fails
when doc and code counts diverge. Of the `ListArena` markers,
`tracking_bytes`/`total_bytes` are group B spec-free and
`data_capacity_bits` is group B contract-carrying (see §2c); only the
last is in the assumed-fact inventory.*

*The five markers in `bplus_layout.rs` are all group B
(contract-carrying), all there to make a **proved** fact reach the
machine code:*

- *`arr_get` / `arr_set`: fixed-size-array access with the bounds check elided.
  Trusted contract is `get_unchecked`'s own (`i < N` ⟹ in bounds), and `N` is the
  array's own const-generic length, so no arithmetic relates bound to index.
  Verus checks `i < N` at every call site; the check `rustc` would emit is
  provably dead, and eliding it is the point of having proved the bound.*
- *`sel_usize`: `if c { b } else { a }` via `core::hint::select_unpredictable`,
  so the bisection's data-dependent update lowers to `cmov` rather than a
  mispredicting branch (see [Chapter 10](10-bplus-tree.md)). The body is
  a total expression containing **no `unsafe`**; `select_unpredictable` is a
  codegen hint whose documented semantics are exactly the stated postcondition.
  It is `external_body` only because the intrinsic carries no Verus spec.*
- *`arr_shift_up`: opens a hole at `pos` by moving `a[pos..cnt]` up one slot.
  Verus can only carry a loop invariant through an explicit element loop, so the
  verified leaf/internal insert walked the tail down one word at a time where
  production issues one `memmove`. The four-clause postcondition (prefix, shifted
  window, tail, length) is the whole contract; `copy_within`'s own documented
  behaviour supplies it for the long arm, and the short arm is literally the loop
  it replaces. `pos <= cnt < N` is verified at every call site. **No `unsafe`.***
- *`slice_get`: the slice analogue of `arr_get`, for the one place the index bound
  is a runtime length rather than a const-generic one: the bulk loader reads its
  input `&[K]`, having proved `at + take <= keys.len()` and `j < take` in the
  enclosing invariant. Same trusted contract (`get_unchecked`'s own), and the
  emitted `cmp/jae panic` it removes was once per key in the loader's innermost
  loop (see [10-bplus-tree §5.2.4](10-bplus-tree.md)).*

*None of the five widens the assumed-fact inventory in a way a proof could
exploit: `arr_get`/`arr_set`/`slice_get` restate indexing that vstd already specs
for the checked form, `sel_usize` restates a conditional, and `arr_shift_up`
restates a slice copy whose effect its postcondition pins element-by-element.*

[Design Table of Contents](00-table-of-contents.md)

## 0. What `external_body` means

`#[verifier::external_body]` tells Verus: *do not look inside this function; take
its signature (and any `ensures`) as an axiom.* It is the mechanism by which
verified code meets the parts of the world the logic cannot describe: hardware
integer casts, process-global state, the allocator, opaque identity. It is more
localized and auditable than a free-standing `assume`/`admit`: an
`external_body` function has a typed interface whose callers are checked, and
where it carries an `ensures`, that contract is the only fact exposed. It is
not logically weaker magic; a false postcondition would still make the
verification unsound.

A healthy verified crate drives `external_body` down to the irreducible
boundary. This crate has 27 default-build markers: 3 ContainerId + 11
capacity/byte diagnostics and shrink helpers + the 5 `bplus_layout`
bounds-elided array/slice primitives + `check_precondition` + `refuse` +
`clone_key_exact` + `values_equal` + the debug ring-walk +
`white_box_head` + the `ExIndexHasher` and `ExFoldHasher` registrations
(5 more behind `literal-types`, for 32). The casts that were *eliminated* (the
`IndexLike`/`DenseId` integer casts) are described in §3.

The groups differ in kind, and the distinction is the point of this chapter:

- **Group A is trusted by *design*.** It models things that are external in
  reality: a process-global atomic and an intentionally-opaque identity. Even
  in principle we do not want to "prove" them; doing so would either be
  meaningless (no spec) or would expose an abstraction we deliberately keep
  closed. These are permanent.
- **Group B is trusted by *unmodeled std behavior*.** `Vec::capacity` /
  `shrink_to` / `size_of` have no vstd specs, and neither do `get_unchecked`,
  `select_unpredictable`, or `copy_within` (verified against vstd
  0.0.0-2026-08-02-0125). The byte reporters are spec-free diagnostics; the
  shrink helpers, `data_capacity_bits`, and the five `bplus_layout` primitives
  carry contracts that restate the documented std behavior. Partly provable
  when vstd grows the specs; the
  [byte-accounting feature request](../future/verify-byte-accounting.md)
  scopes the reporter half.
- **Group C has two trusted runtime-trap primitives**. `check_precondition`
  carries a `requires` (so it is load-bearing in the proof, not spec-free);
  `refuse` diverges and has no post-state or contract to assume. Both are
  external only because their bodies use panic-formatting machinery the logic
  does not model. They are permanent and minimal.
- **Group D carries external key-model facts** (`clone_key_exact`, plus the
  feature-gated literal-type axioms in `external_specs.rs`). Trusted because
  the facts are about foreign deterministic value types.
- **Group E is unverified glue**: `values_equal`, the debug-only ring walk,
  `ListHead::white_box_head`, and the ordinary-Rust delegation shims outside
  `verus!{}`.

## 1. Group A: `ContainerId` (trusted by design), 3 items

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

(The runtime payload widened from production's `u32` to `u64` to increase
wraparound headroom.) The struct is `external_body` so its `raw`
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
`verus!{}`): production's algorithm widened from `AtomicU32` to `u64`. Default
release builds can wrap after 2^64 allocations; that width makes collision
impractical for ordinary executions but is not a non-wrapping guarantee.
`strict-id-exhaustion` makes exhaustion fatal, and debug builds assert the
boundary. Exhaustion is unit-tested by parking a counter at that boundary
(`container_id.rs` in-module tests). The strict-feature performance tradeoff
must be evaluated with the maintained Criterion conformance benchmark; this
chapter makes no fixed timing or percentage claim. **Why not proved:** it
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
from itself. That axiom proves that the executable check agrees with the
abstract equality used by contracts; it does not prove that separately
allocated containers have distinct identities. Global freshness remains an
environmental assumption, with finite runtime evidence from
`container_id_new_is_distinct` and `cross_container_token_rejected` in
[`tests/external_body_contract_fuzz.rs`](../../tests/external_body_contract_fuzz.rs)
mint thousands of ids and check end-to-end that one container rejects another's
token.

## 2. Group B: unmodeled std behavior, 16 items

Verus/vstd model a `Vec`'s element sequence (`@`) but not its **allocation**:
`capacity()`, `shrink_to`, and `size_of::<T>()` have no specs. Everything that
reads or manages capacity is therefore `external_body`. The B+tree hot-path
primitives (§2d) are the same kind of trust over three other unspecced std
operations (`get_unchecked`, `select_unpredictable`, `copy_within`). Four
sub-kinds:

### 2a. Byte reporters (no `ensures`; diagnostic), 8 items

Production parity: all report the capacity-based allocation
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
vstd, and the functions carry **no `ensures`**: they are diagnostic
instrumentation no proof reads. **Partially provable in principle** (a ghost
byte model with saturating arithmetic; the
[byte-accounting feature request](../future/verify-byte-accounting.md) scopes
it), but the capacity read itself stays external until vstd models it.
Runtime validation: the differential trace `differential_bytes`
(`containers-conformance/tests/differential.rs`) checks `tracking_bytes` agrees **exactly** with
production over randomized push/set/pop/mark/restore traces (identical
element layouts + deterministic std::Vec growth make exactness meaningful
there), and `total_bytes` respects a lower-bound floor (struct + tracking +
data). The store-side reporters (`ParallelStore`/`InlineStore`/
`CaptureBits::heap_bytes`) are NOT compared exactly against production:
the u64 `ContainerId` and word-at-a-time CaptureBits growth intentionally
differ from production's representation, so only the formula shape is
parity, not the number. The smoke test `byte_counters_are_consistent`
(external_body_contract_fuzz.rs) checks total ≥ tracking, monotonicity,
no panic.

### 2b. Capacity-shrink helpers (contract-carrying), 2 items

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
contract is exactly "the element sequence is unchanged", the std-documented
behavior of `shrink_to`. Provable when vstd specs capacity ops. Runtime
validation: `shrink_preserves_vec_contents` / `shrink_preserves_aov_contents`
(external_body_contract_fuzz.rs) drive both helpers through the public
`mark(ShrinkPolicy::IfOverallocated)` surface across random contents,
overallocation levels, and `(factor, headroom)` policies, asserting the
element sequence is unchanged, so every contract-carrying trusted item in
the crate now has a contract-level runtime test.

### 2c. `data_capacity_bits` (contract-carrying), 1 item

```rust
// parallel_store.rs
#[verifier::external_body]
pub(crate) fn data_capacity_bits<T>(data: &Vec<T>) -> (n: usize)
    ensures n >= data@.len(),
{ data.capacity() }
```

**Why not proved:** `Vec::capacity()` is unmodeled, exactly as in §2b. **Why it
is load-bearing rather than diagnostic:** the `ensures n >= data@.len()` is what
makes capture-word truncation invisible to `captured()`: every flag a caller can
still observe sits at an index below `len <= capacity`, so dropping the words
above capacity cannot change any observable answer. A proof reads this contract;
it is not instrumentation.

The trusted statement is the std-guaranteed `Vec` invariant `capacity() >= len()`,
which is about as safe as an unmodeled-capacity assumption gets: it is weaker
than §2b's, since it asserts an inequality rather than preservation of contents.
Provable when vstd specs capacity ops.

### 2d. Bounds-elided array/slice primitives (contract-carrying), 5 items (`bplus_layout.rs`)

`arr_get`, `arr_set`, `slice_get`, `sel_usize`, `arr_shift_up` were added by the
B+tree hot-path work so that facts Verus already **proved** at the call sites
reach the machine code: the elided bounds check (`i < N` is a verified
precondition, so the `cmp/jae panic` `rustc` emits is provably dead), the
`cmov` lowering of the bisection's data-dependent update, and one `memmove`
where Verus's invariant rules force an element loop. The per-item argument,
including why each contract adds nothing a proof could exploit, is in this
file's preamble and in each function's own doc comment; the performance each
one pays for is in [10-bplus-tree](10-bplus-tree.md).

**Why not proved:** `get_unchecked`, `select_unpredictable`, and `copy_within`
have no vstd specs (checked against the pinned vstd). Each contract restates
the operation's documented behavior: checked indexing for
`arr_get`/`arr_set`/`slice_get`, the replaced `if`/`else` for `sel_usize`,
`copy_within(pos..cnt, pos+1)` stated element-wise for `arr_shift_up`.
Provable when vstd specs those operations. The verified alternatives have
different generated-code shapes; the Criterion B+tree workloads, not a fixed
historical percentage, determine whether those shapes remain worthwhile.
Runtime validation is two-layered: hand-rolled agreement fuzzes in
`external_body_contract_fuzz.rs`, and the property suite
`src/bplus_layout_tests.rs`, which checks each contract against its
checked std form with shrinking, at the `(T, N)` instantiations the trees use,
including both sides of `arr_shift_up`'s length-18 scalar/`memmove` dispatch
at every admissible `pos`.

## 2.5. Group C: the runtime-guard primitives (`check_precondition`, `refuse`), 2 items

`refuse(msg) -> !` is the total-operation shell's panic arm: a public
total function branches on its would-be precondition and calls `refuse` in
the violating arm, so the signature carries no obligation. `external_body`
for the same reason as `check_precondition` (unmodeled panic machinery);
contract-free in the strongest sense: the `!` return type means there is no
post-state to assume anything about.


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

## 3. The integer casts are proved, not trusted

The `IndexLike::as_usize` / `try_from_usize` casts on the primitive integers
(`u8`/`u16`/`u32`/`u64`/`usize`) and the `DenseId::as_usize` casts carry
value-preserving `ensures` and verify; none is `external_body`:

- `u8`/`u16`/`u32` widening (and the guarded narrowings of `try_from_usize`)
  verify directly; Verus models these casts.
- `u64` and `DenseId63` (a `u64` payload) rely on the cast being the value
  identity on a 64-bit host: `usize::MAX == u64::MAX`. This is discharged by
  `index_like::lemma_u64_usize_64bit` over the crate-wide `global size_of
  usize == 8` pin, and the whole `u64`/`usize` index path is
  `#[cfg(target_pointer_width = "64")]`-gated, so verifying them adds no new
  assumption beyond the target pin.

The governing principle is that "wraps a cast" is not the same
as "must be trusted". A cast with a value-preserving `ensures` is provable
once the host-width fact is pinned; only genuine side effects (§1b),
intentional abstraction (§1a/§1c), and spec-free plumbing (§2) are the real
boundary.

## 3.5. Groups D and E: consumer-facing trusted surfaces

Consumer integration adds two trusted surfaces of a different kind,
enumerated here so the ledger stays complete.

### Group D: external key-model facts

**`clone_key_exact` (map.rs, `external_body`, contract-carrying):**

```rust
#[verifier::external_body]
fn clone_key_exact<K: Clone>(key: &K) -> (r: K)
    requires obeys_key_model::<K>(),
    ensures r == *key,
{ key.clone() }
```

This carries requirement (3) of vstd's hash-table key model ("the executable
`Key::clone` produces a result identical to its input"), which `SpMap` already
assumes for every key type via `obeys_key_model::<K>()` (`new`'s
precondition, threaded through `wf`). vstd states that requirement in prose on
the `uninterp obeys_key_model` and provides no lemma projecting it out, so
this helper carries it as its contract. **No NEW assumption** beyond what
`obeys_key_model` already asserts.

**Feature `literal-types` (`src/external_specs.rs`):**
five `broadcast axiom fn`s (mirroring vstd's own primitive-type key-model
axioms) giving `obeys_key_model::<T>()` for `num_bigint::BigInt`,
`num_bigint::BigUint`, and the three crate-local canonical wrappers
`CanonicalF64`, `CanonicalRational`, and `BitsF64`
(`src/canonical_keys.rs`), plus five opaque
`external_type_specification` registrations required to name the types in
specs (contract-free: they count as `external_body` markers but assume no
semantics).

The credibility argument is NOT mere determinism: vstd's requirement (2)
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
representations. Both violate requirement (2) outright. Regression tests
in `tests/compat_map.rs::key_model_violations` DEMONSTRATE each violation
so the exclusions stay justified against future crate upgrades.

**Replacements:** the crate-local canonical wrappers (`canonical_keys.rs`)
restore float/rational keying with requirement (2) TRUE BY CONSTRUCTION:
`CanonicalF64` is a `struct { bits: u64 }` whose only constructor folds all
NaNs to one encoding and −0.0 to +0.0, with derived `Eq`/`Hash` over the
single field (its `==` IS bit identity; no foreign code participates in
its equality at all); `CanonicalRational` holds a reduced,
positive-denominator `BigInt` pair produced only via `Ratio::new`, so one
representation per rational is reachable and derived structural equality
is value identity (resting on the same normalized-`BigInt` argument as the
BigInt axiom). Their axioms remain axioms only because `obeys_key_model`
is `uninterp`: nothing can be proved to satisfy it, not even a type where
the property holds by construction.

**The forcing function for future key types:**
`declare_key_model_assumption!` (exported from `external_specs.rs`). A
verified consumer introducing a new key type cannot discharge `SpMap::new`'s
`requires obeys_key_model::<K>()` without an axiom (the predicate is
`uninterp`); the macro makes that unavoidable act disciplined: it pins the
`axiom_key_model_` name prefix (compile-time checked, CI-greppable),
requires a justification string embedded in the generated docs, and
generates a requirement-level fuzz test (hash determinism, clone identity,
and `==`-iff-representation-identity over a caller-supplied generator and
representation observable, the exact failure mode that sank the withdrawn
axioms). Exercised end-to-end in `tests/key_model_macro.rs`.

Feature-gated: `cargo verus verify` passes with and without
`literal-types` (both **1701 verified, 0 errors** as of 2026-08-24; the axioms
add obligations only to their users, so the two
configurations agree fact-for-fact). Runtime validation (`tests/compat_map.rs::literal_keys`): an
SpMap-vs-HashMap oracle trace, **plus fuzz tests of the key-model
requirements themselves**: eq-coherence across construction paths with
representation-agreement checks (requirement 2's falsifiable observable),
hash determinism (1), clone identity (3). The oracle trace alone cannot
detect an identity/`==` mismatch (both maps use the same `Eq`/`Hash`);
the requirement-level fuzzing is what tests the assumed facts.

**D-hasher: `axiom_index_hasher_builds_valid_hashers`
(src/hasher_spec.rs, default build; 1 axiom + the `ExIndexHasher` and
`ExFoldHasher` registrations).** `SpMap`'s transient key index is
`std::collections::HashMap<K, usize, IndexHasher>`, where `IndexHasher` is an
8-byte crate-local `BuildHasher` carrying an explicit seed and delegating to
foldhash's `fast` family, the same hash ALGORITHM production's `Map` uses
(hashbrown 0.17's `DefaultHashBuilder` is a newtype wrapping
`foldhash::fast::RandomState`). vstd models `std::HashMap<K, V, S>`
generically over any `S: BuildHasher` (gated on `builds_valid_hashers::<S>()`),
and ships exactly one instance of that predicate: an `admit()`ed axiom for
std's `RandomState`. This axiom is its mirror image: same shape, same strength,
and a *weaker* assumption, since `IndexHasher` stores its seed by value at
construction, making `build_hasher` a pure function of that seed. Owning the
type is also what makes the seed configurable (`SP_HASHER_SEED`,
`set_default_seed`, `IndexHasher::with_seed`) with no added trust: the seed
rides in `Default`, which is the constructor vstd already specs generically
over `S: Default` (vstd does not spec `HashMap::with_hasher`).
`builds_valid_hashers` asserts only that the hasher is byte-deterministic
(output depends solely on the `Hash`-fed bytes), NOT collision-freedom or
any distribution property, neither of which a HashMap's correctness needs.
`IndexHasher` is an ordinary seeded-then-deterministic `BuildHasher`, exactly
like std's `RandomState`; they differ only in the hash function, which the model
does not observe. Under `hasher-random-seed` the entropy is drawn once when the
process default is resolved, never per `build_hasher` call. In the default
build the fallback is the constant `DEFAULT_SEED`, but `SP_HASHER_SEED` and
`set_default_seed` may replace it. Each constructed `IndexHasher` is
deterministic for its stored seed. Process-wide reproducibility additionally
requires configuring the seed during single-threaded startup, before any
container construction, and treating `SeedSealed` as fatal: a concurrent
setter can lose a race after an earlier hasher observed the old seed.
**No proof can conclude `builds_valid_hashers` for ANY hasher** (the predicate
is `uninterp`), so vstd admits it for `RandomState` and we admit the identical
fact for `IndexHasher`. This is the whole
cost of closing the former SpMap performance exception. Unconditional (not
`literal-types`-gated) because the
index is core to `SpMap`.

### Group E: unverified glue, 3 `external_body` items + ordinary-Rust shims

**`external_body` members:**

| Item | Contract | Why trusted |
|---|---|---|
| `values_equal<T: PartialEq>` (sparse_set.rs) | NONE: result is an unconstrained bool, so nothing unsound is derivable; `remove_value` promises the structural change, not which value matched | avoids threading vstd's `obeys_eq_spec` plumbing; scan behavior pinned by ported production proptests |
| `CircularList::debug_check_different_rings` (circular_list.rs) | `requires` the spec-side precondition; no ensures | debug-only runtime mirror of a spec-only precondition (O(ring) walk, gated to debug builds); the verified `splice` never depends on it |
| `ListHead::white_box_head` (list.rs) | NONE: read-only test accessor with no `ensures` | unpacks the runtime niche for white-box differential tests; no proof depends on its result |

**Ordinary-Rust items outside `verus!{}`** that delegate 1:1 to a verified
core; the trusted content is exactly "the delegation line calls the verified
method with the converted argument":

| Item | Delegates to | Why outside the proof |
|---|---|---|
| `Vec::get(impl Into<I>)` (vec.rs, bottom) | verified `get_index` | generic `Into` carries no Verus-visible input/output relation |
| `Vec::set(impl Into<I>, T)` | verified `set_index` | same |
| `guard::check_precondition_erased` | (panics) | callable from `external_body` diagnostics; no proof context |
| std `Iterator` impls for `VecViewIter` / `ListIter` | verified inherent `next` | trait impls for unmodeled std traits (each is one delegation line) |
| `white_box_*` read accessors (bplus.rs, list.rs, circular_list.rs) | immutable field borrows | `#[doc(hidden)]` oracle access for runtime property tests; read-only, cannot violate any invariant |
| `next_id_from` (container_id.rs) | (atomic allocator) | the trusted allocator behind Group A's `new`; plain wrapping `fetch_add` over `u64`, optional fatal boundary behind `strict-id-exhaustion`, exhaustion unit-tested |
| consumer `Tagged` impls + macro expansions in egraph | verified witness instantiations | consumer crate is not run under Verus. Mitigated by the canary's shape fixtures; the per-type contract fuzzers this row assumes do **not** exist yet |

Every safety property behind the glue (bounds panics, capture protocol,
snapshot fidelity) is enforced by the verified core it calls; the glue cannot
bypass it.

The e-graph consumer has a separate ordinary-Rust proof-processing boundary:
proof-forest path reversal, the naive explanation walk, Euler-tour LCA table
construction/query, deep explanation expansion, and proof serialization are
tested executable algorithms, not Verus theorems. Verified columns and
mark/restore invariants protect their storage, but do not prove forest
acyclicity or explanation correctness. See
[`egraph-class-layer.md`](egraph-class-layer.md) and the retained proof-forest
verification task in
[`../future/conformance-and-release.md`](../future/conformance-and-release.md).

## 4. Summary table

All 27 default-build `external_body` markers plus the 1 default-build axiom
(the `literal-types` additions are listed after):

| # | Item | Group | Trusted because | Provable? |
|---|---|---|---|---|
| 1 | `struct ContainerId` | A | opaque identity by design (`uninterp id()`) | n/a: no contract |
| 2 | `ContainerId::new` (+ `next_id_from` allocator) | A | process-global atomic side effect; no `ensures`; wrapping `u64` allocation with an optional fatal boundary | no (side effect) |
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
| 11c | `data_capacity_bits` | B | `Vec::capacity` unmodeled; **contract-carrying**: `n >= len` is what makes capture-word truncation unobservable (§2c) | when vstd specs capacity ops |
| 11d | `arr_get` (bplus_layout) | B | `get_unchecked` unspecced; contract = checked indexing, `i < N` verified at every call site (§2d) | when vstd specs unchecked indexing |
| 11e | `arr_set` (bplus_layout) | B | same, for the write (`update(i, v)` over the whole array) | same |
| 11f | `slice_get` (bplus_layout) | B | same, with a runtime-length bound (`i < s.len()`) | same |
| 11g | `sel_usize` (bplus_layout) | B | `select_unpredictable` unspecced (a codegen hint); contract = the `if`/`else` it replaces; **no `unsafe`** | when vstd specs the intrinsic |
| 11h | `arr_shift_up` (bplus_layout) | B | `copy_within` unspecced; four-clause shift postcondition; **no `unsafe`** (short arm is the element loop it replaces) | when vstd specs `copy_within` |
| 11i | `guard::refuse` | C | diverges (`-> !`); body is the unmodeled panic machinery; nothing assumable (no post-state) | n/a (no contract) |
| 12 | `guard::check_precondition` | C | body `panic!` uses unmodeled format machinery (`requires cond` is checked) | no (same reason as `vstd::runtime_assert`) |
| 13 | `clone_key_exact` | D | projects key-model requirement (3) out of vstd's prose-stated `obeys_key_model`; no new assumption | no (vstd provides no lemma) |
| 14 | `values_equal` | E | no ensures: unconstrained bool, nothing derivable; avoids `obeys_eq_spec` plumbing | by threading vstd eq specs; declined for production shape |
| 15 | `debug_check_different_rings` | E | debug-only mirror of a spec-only precondition | n/a (diagnostic) |
| 16 | `ListHead::white_box_head` | E | contract-free read-only test accessor (unpacks the niche for the white-box walkers; inside `verus!` so it needs the marker; its node-side counterpart `white_box_next` sits outside `verus!` and needs none) | n/a (no contract) |
| 17 | `ExIndexHasher` registration | D | contract-free opaque registration; names `IndexHasher` in specs so the hasher axiom can trigger on it | n/a (no contract) |
| 18 | `ExFoldHasher` registration | D | same: names foldhash's `FoldHasher` (`IndexHasher`'s associated `Hasher` type) so the `BuildHasher` impl type-checks under Verus | n/a (no contract) |
| — | `axiom_index_hasher_builds_valid_hashers` | D | `broadcast axiom fn`: mirrors vstd's shipped `axiom_random_state_builds_valid_hashers`; `builds_valid_hashers` asserts only byte-determinism, which `IndexHasher` satisfies at least as strongly as std's `RandomState` (seed stored by value, so `build_hasher` is a pure function of it; §3.5 D-hasher) | no (predicate is `uninterp`; vstd `admit()`s the identical fact for `RandomState`) |

`literal-types` additions (all in `external_specs.rs` / `canonical_keys.rs`):

| # | Item | Kind | Trusted because |
|---|---|---|---|
| 19 | `ExBigInt` registration | `external_body` struct, contract-free | names the foreign type in specs; no semantics |
| 20 | `ExBigUint` registration | same | same |
| 21 | `ExCanonicalF64` registration | same | same (crate-local type) |
| 22 | `ExCanonicalRational` registration | same | same |
| 23 | `ExBitsF64` registration | same | same: registered but not consumed by the current e-graph; it supports the future float-semantics design in key-model-tcb.md §float-semantics |
| — | `axiom_bigint_obeys_hash_table_key_model` | `broadcast axiom fn`: a DIRECT assumed fact | structural eq over num-bigint's normalization invariant (§3.5 D) |
| — | `axiom_biguint_obeys_hash_table_key_model` | same | same |
| — | `axiom_canonical_f64_obeys_hash_table_key_model` | same | crate-local: `==` is bit identity by construction; axiom-shaped only because the predicate is `uninterp` |
| — | `axiom_canonical_rational_obeys_hash_table_key_model` | same | crate-local canonicalization + the BigInt argument |
| — | `axiom_bits_f64_obeys_hash_table_key_model` | same | crate-local: raw-bit injective, `==` classes singleton trivially |

(`canonical_keys.rs` itself is plain unverified Rust (group E in kind), but
its entire behavioral surface is pinned by the requirement-level proptest
fuzz in `tests/compat_map.rs::canonical_key_model`.)

Plus the Group E ordinary-Rust delegation shims tabulated in §3.5.

**Bottom line.** Default build: 3 trusted-by-design `ContainerId` items
(permanent; equality reflection trusted, global freshness not proved, and
finite distinctness behavior runtime-fuzzed), 11 capacity-introspection items
(8 spec-free byte reporters
(production-formula parity; `tracking_bytes` differential-tested exactly,
store reporters formula-level only), 2 contract-carrying shrink
helpers, and `data_capacity_bits`), 5 bounds-elided array/slice primitives
(§2d: each contract restates a documented std behavior, fuzzed and
property-tested against the checked form), 2 runtime-trap primitives (`check_precondition`, load-bearing,
body is a one-line panic; `refuse`, diverging and contract-free), 1 key-model projection (`clone_key_exact`, no
new assumption beyond the `obeys_key_model` precondition SpMap already
carries), 3 glue items (`values_equal` unconstrained, the debug
ring-walk diagnostic, and the contract-free `white_box_head` accessor), and
1 hasher fact + its 2 type registrations
(`axiom_index_hasher_builds_valid_hashers` + `ExIndexHasher`/`ExFoldHasher`:
mirrors vstd's shipped `RandomState` axiom so SpMap's index can use
production's hash algorithm with a configurable, deterministic-by-default seed;
§3.5 D-hasher). With `literal-types`: +5 contract-free type
registrations and +5 `obeys_key_model` axioms: BigInt/BigUint (foreign,
structural-eq argument), CanonicalF64/CanonicalRational (crate-local
wrappers replacing the WITHDRAWN-as-false BigRational/OrderedFloat axioms;
requirement (2) by construction, violation regressions pin the
exclusions), and BitsF64 (raw-bit injective, the long-term float key;
CanonicalF64's fold is a pinned production-parity decision, see
key-model-tcb.md §float-semantics). Future key types must go through
`declare_key_model_assumption!` (justified + auto-fuzzed axioms). The assumed-fact inventory of the default
crate is therefore: `ContainerId::eq`'s equality reflection, the two shrink
helpers' data preservation, `data_capacity_bits`'s `capacity >= len`,
`clone_key_exact`'s clone identity, and the five `bplus_layout` primitives'
agreement with their checked std forms: **ten** contract-carrying trusted
statements. Each is either one line of exec code or (`arr_shift_up`) a length
dispatch between the element loop and the `copy_within` its postcondition
pins. No
`assume`/`admit` anywhere in the verified modules. Within the
`external_body` inventory, no larger algorithm is hidden:
`arr_shift_up`'s length dispatch is the largest trusted body, and both of its
arms restate the same postcondition. This statement does not cover the
ordinary-Rust shims or the consumer proof algorithms listed above.

**Scope note.** "No `assume`/`admit`" is a claim about *this crate's project
sources*. The sibling `abstract-domains` crate likewise has a project-local
source gate and its ordinary verification run discharges 994 conditions. Its
pinned `vstd` contains admitted specifications, so global `--no-cheating`
fails in that dependency; this is an explicit dependency trust boundary, not a
project theorem. Nothing in `containers-verus` depends on
`abstract-domains`, so their trust statements remain independent. The future
design for shrinking this crate's boundary, including eliminating the key-model
axioms via canonical key types, is `doc/future/key-model-tcb.md`.

---
[← Table of Contents](00-table-of-contents.md)
