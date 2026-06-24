# Feature Request: Verify the Byte-Accounting Diagnostics (Group B)

*Bring the three memory-accounting methods that are currently
`#[verifier::external_body]` under a verified spec, so the crate's last
spec-free trusted exec code is eliminated. Companion to the trust-boundary
reference, [Design Ch. 2](../design/02-trust-boundary.md).*

[Design Table of Contents](../design/00-table-of-contents.md)

## Summary

Three functions report how many bytes a container is using and are currently
trusted (`external_body`) with **no `ensures` clause at all**:

| Function | File | Body (essentially) |
|---|---|---|
| `Vec::tracking_bytes` | `vec.rs` | `diff_log.len()*size_of::<(T,I)>() + frames.len()*size_of::<Frame<I>>() + forks.heap_bytes()` |
| `Vec::total_bytes` | `vec.rs` | `store.heap_bytes() + tracking_bytes()` |
| `ForkHistory::heap_bytes` | `fork_history.rs` | `origins.len()*size_of::<ForkOrigin>()` |

They are honest diagnostics (production parity: the production crate exposes the
same `total_bytes`/`tracking_bytes` introspection), but today they are pure
exec plumbing the verifier knows nothing about. This request is to give them a
**ghost byte model** and a verified `ensures`, so their results are
machine-checked rather than trusted.

## Why they are `external_body` today

Two independent reasons, both currently blocking (see
[Ch. 2 §2](../design/02-trust-boundary.md) for the full account):

1. **`core::mem::size_of::<T>()`** has no Verus spec. Its value is a
   target-dependent layout fact the verifier does not model, so an expression
   containing it cannot be reasoned about.
2. **No `ensures`.** There is currently nothing *to* prove: the methods return
   a `usize` with no stated relationship to the container's ghost state. Even if
   `size_of` were modeled, a bare `external_body` with no contract contributes
   nothing until a spec is written.

Neither is fundamental; both are addressable (below). This contrasts with
**Group A** (`ContainerId`), whose `external_body` is a *deliberate* abstraction
(opaque identity, process-global atomic) that we do **not** plan to remove (see
[Ch. 2 §1](../design/02-trust-boundary.md)).

## Proposed design

### Step 1: model `size_of` via `vstd`

`vstd` exposes `vstd::layout::size_of::<T>()` as a spec function and
`core::mem::size_of` is given a `vstd` exec spec relating the two (the same
machinery the crate already uses for `global size_of usize == 8` in
`bplus_layout.rs`). Replacing the raw `core::mem::size_of` calls with the
`vstd`-specified form makes the multiplications first-class spec terms.

For the element/frame/origin types whose size matters, pin the relevant
`size_of` to a concrete value with a `global layout` directive (as the crate
already does for `usize`), or keep it symbolic, either way the value becomes a
spec quantity rather than an opaque intrinsic.

### Step 2: give each method a ghost byte model + `ensures`

Add an open spec function, e.g.

```rust
pub open spec fn tracking_bytes_spec(&self) -> nat {
    self.diff_log@.len() * size_of::<(T, I)>()
        + self.frames@.len() * size_of::<Frame<I>>()
        + self.forks.heap_bytes_spec()
}

pub fn tracking_bytes(&self) -> (b: usize)
    requires self.wf(), /* + a no-overflow bound, see Step 3 */
    ensures b as nat == self.tracking_bytes_spec(),
{ ... }   // no longer external_body
```

and likewise `total_bytes_spec` / `heap_bytes_spec`. The `ensures` is then
provable: each term is `len() * size_of` where `len()` already has a spec
(`diff_log@.len()` etc.) and `size_of` is now spec-modeled.

### Step 3: handle `usize` overflow

The one real proof obligation that appears: the products and sums must not
overflow `usize`. This needs a precondition bounding the lengths (e.g.
`diff_log.len() * size_of::<(T,I)>() <= usize::MAX`), or saturating arithmetic
with a weaker `ensures` (`b as nat <= spec` / `b == min(spec, usize::MAX)`).
Production silently wraps; we would make the bound explicit. This is the only
part requiring judgment (see "Open questions").

## Verification effort

**Low-to-moderate.** No new proof *infrastructure* is needed: the crate already
pins `size_of usize` and reasons about `len() * k` products elsewhere. The work
is: write three `*_spec` functions, swap `core::mem::size_of` for the `vstd`
form, add the overflow precondition (or saturate), and discharge three
`len * size_of`-shaped `ensures` (likely `nonlinear_arith` for the products).
Estimate: a single focused session, comparable to the primitive-cast
verification that took the crate from 16 to 6 `external_body`.

## Impact

Removes the last **spec-free** `external_body` from the crate. Afterward the
only remaining trusted exec code is **Group A** (`ContainerId`: the opaque
identity type, its atomic `new`, and the `eq` axiom), all of which is
*deliberately* external (a real-world side effect and an intentionally abstract
identity), not unproven plumbing. The trust surface would then be:

- exactly **3 items**, all in `ContainerId`, all by design; and
- **0** functions trusted merely because a spec was never written.

The byte counters are today guarded only by the runtime smoke test
`byte_counters_are_consistent` in `tests/external_body_contract_fuzz.rs`
(total ≥ tracking, monotone non-decreasing, no panic); a verified `ensures`
would subsume and strengthen that.

## Open questions

1. **Overflow policy.** Precondition (caller proves no overflow) vs saturating
   return (weaker but total). Production wraps; saturating is the safest faithful
   choice and keeps the methods total. Recommend saturating with
   `ensures b == min(spec, usize::MAX) as usize`.
2. **`size_of` symbolic vs pinned.** Pinning every element type's `size_of` is
   heavy and target-specific; keeping it symbolic (just `vstd`-specified) is
   enough for the `ensures` and avoids per-type `global layout` directives.
   Recommend symbolic.
3. **Scope.** `heap_bytes` on the inner stores (`ParallelStore`/`InlineStore`)
   would also need specs for `total_bytes` to be fully end-to-end; that is a
   slightly larger surface (the store backends). Could be staged: do
   `tracking_bytes` + `ForkHistory::heap_bytes` first (self-contained), then the
   store `heap_bytes`.

## Non-goals

- This does **not** touch Group A (`ContainerId`). That stays `external_body` by
  design; see [Ch. 2 §1](../design/02-trust-boundary.md). Distinctness is left
  fuzz-checked, not proved, for the reasons recorded there and in
  [Ch. 3 §5](../design/03-fork-history.md).
