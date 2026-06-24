# The Trust Boundary: What Is `external_body`, and Why

*The crate is verified with **no `admit`s and no `assume`s**. The only code the
verifier takes on trust is a small set of functions marked
`#[verifier::external_body]` (their bodies are hidden; only their signatures /
`ensures` are believed). This chapter enumerates exactly what remains trusted
and, for each, why it is trusted rather than proved. There are **7 such items**,
in three groups.*

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
boundary. This crate has 6, down from ~16; the casts that were *eliminated*
(the `IndexLike`/`DenseId` integer casts) are described in §3, the 6 that
*remain* in §1 (Group A) and §2 (Group B).

The two groups differ in kind, and the distinction is the point of this chapter:

- **Group A is trusted by *design*.** It models things that are external in
  reality: a process-global atomic and an intentionally-opaque identity. Even
  in principle we do not want to "prove" them; doing so would either be
  meaningless (no spec) or would expose an abstraction we deliberately keep
  closed. These are permanent.
- **Group B is trusted by *omission*.** It is spec-free diagnostic plumbing that
  simply has not had a contract written yet. It is provable; the
  [byte-accounting feature request](../future/verify-byte-accounting.md) scopes
  the work. These are temporary.
- **Group C is one trusted runtime-trap primitive** (`check_precondition`). It
  carries a `requires` (so it is load-bearing in the proof, not spec-free) and
  is external only because its body uses the panic-formatting machinery the
  logic does not model: the same reason `vstd`'s own `runtime_assert` is
  external. Permanent, and minimal.

## 1. Group A: `ContainerId` (trusted by design)

`ContainerId` is the per-container identity used to reject a `restore` token
minted by a *different* container (`vec.rs` / `append_only_vec.rs`:
`token.container_id.id() == self.id.id()` inside `is_token_valid_spec`). It is
three trusted items.

### 1a. `struct ContainerId`: opaque identity

```rust
#[verifier::external_body]
pub struct ContainerId { raw: u32 }
//   pub uninterp spec fn id(self) -> nat;
```

The struct is `external_body` so its `raw` field is invisible to the verifier;
the only thing specs may say about a `ContainerId` is its abstract
`id(): nat`, declared **`uninterp`** (uninterpreted, deliberately given no
definition). **Why not proved:** there is no theorem here; a struct has no
contract. This is a *modeling choice*: we want identity to be abstract so that
no proof can accidentally depend on the concrete `u32` representation. Making
`raw` visible would buy nothing and couple proofs to the bit pattern.

### 1b. `ContainerId::new`: process-global atomic

```rust
#[verifier::external_body]
pub fn new() -> ContainerId {
    static NEXT: AtomicU32 = AtomicU32::new(1);
    ContainerId { raw: NEXT.fetch_add(1, Ordering::Relaxed) }
}
```

**Why not proved:** it reads and mutates a **process-global `AtomicU32`**, a
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

## 2. Group B: byte-accounting diagnostics (trusted by omission)

Three methods report memory usage and are `external_body` with **no `ensures`**:

```rust
#[verifier::external_body]
pub fn tracking_bytes(&self) -> usize {            // vec.rs
    self.diff_log.len() * size_of::<(T, I)>()
        + self.frames.len() * size_of::<Frame<I>>()
        + self.forks.heap_bytes()
}
#[verifier::external_body]
pub fn total_bytes(&self) -> usize {               // vec.rs
    self.store.heap_bytes() + self.tracking_bytes()
}
#[verifier::external_body]
pub fn heap_bytes(&self) -> usize {                // fork_history.rs
    self.origins.len() * size_of::<ForkOrigin>()
}
```

**Why not proved (today):** two reasons, neither fundamental.

1. They call **`core::mem::size_of::<T>()`**, a target-dependent layout intrinsic
   with no Verus spec; an expression containing it cannot be reasoned about as
   written.
2. They have **no `ensures`**; there is literally nothing to prove. They are
   diagnostic instrumentation (production exposes the same introspection); no
   proof reads their result, so no contract was ever written.

**These are provable and *should* be proved.** Unlike Group A, there is no
design reason to keep them trusted; they are just spec-free plumbing. `vstd`
specifies `size_of`, and the crate already pins `global size_of usize == 8` and
reasons about `len() * k` products, so the only real obligation is `usize`
overflow. The [byte-accounting feature request](../future/verify-byte-accounting.md)
scopes the full plan (ghost byte model + `ensures`, saturating arithmetic for
overflow). Until then they are guarded by the runtime smoke test
`byte_counters_are_consistent` (total ≥ tracking, monotone, no panic) in the same
fuzz file.

## 2.5. Group C: the runtime-guard primitive (`check_precondition`)

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

## 4. Summary table

| Item | Group | Trusted because | Provable? |
|---|---|---|---|
| `struct ContainerId` | A | opaque identity by design (`uninterp id()`) | n/a: no contract |
| `ContainerId::new` | A | process-global atomic side effect; no `ensures` | no (side effect) |
| `ContainerId::eq` | A | bridges to an intentionally-`uninterp` `id()` | only by un-abstracting; declined |
| `Vec::tracking_bytes` | B | `size_of` + no `ensures` | **yes: see feature request** |
| `Vec::total_bytes` | B | `size_of` + no `ensures` | **yes** |
| `ForkHistory::heap_bytes` | B | `size_of` + no `ensures` | **yes** |
| `guard::check_precondition` | C | body `panic!` uses unmodeled format machinery (`requires cond` is checked) | no (same reason as `vstd::runtime_assert`) |

**Bottom line.** 3 trusted-by-design (`ContainerId`, permanent, runtime-fuzzed),
3 trusted-by-omission (byte counters, provable, [feature request filed](../future/verify-byte-accounting.md)),
and 1 runtime-trap primitive (`check_precondition`, load-bearing, body is a
one-line panic). No `assume`/`admit` anywhere. No algorithmic logic is hidden
behind any `external_body`; every container's actual behavior is verified down
to these boundary leaves.

---
[← Table of Contents](00-table-of-contents.md)
