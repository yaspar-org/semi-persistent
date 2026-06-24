# Default implementations for container element types

Why every value type stored in a semi-persistent container needs `Default`, why
a fabricated default is *sound* (never observable), and, the subtle part, how a
`Tagged` type's niche (stolen bit) stays safe when a default filler is created.
Ends with a per-type recipe for the production codebase.

## 0. Why `Default` is required

`restore` regrows a popped/shrunk region with `resize_default(saved_len)`
BEFORE replaying the diff log (see `04-pop.md`, `restore-regrow-
alternatives.md`). Growing the backing store needs *some* value to put in the
new slots, and we use `T::default()`:

- `ParallelStore::resize_default` → `self.data.push(T::default())`
  (`parallel_store.rs`).
- `InlineStore::resize_default` → `self.data.push(T::default().into_repr())`
  (`inline_store.rs`): note the filler is `default()` **passed through
  `into_repr`**. This routing is the whole story for niche safety (§3).

So every `T` that can be the element type of a semi-persistent `Vec` (directly,
or transitively via `Map`/`SparseSet`/`ListArena`/`BPlusTreeSet`, which are
built on `Vec`) must implement `Default`. The crate models the `Copy` subset of
`Clone`, so concretely the bound is `T: Copy + Default`.

## 1. Filler soundness: a default is never observable

The headline restore theorem is `view() == snapshots[token.frame_idx]`. A
filler written by `resize_default` lives at a position that the backward replay
then **overwrites** with the captured diff value (coverage guarantees every
regrown cell has a diff, `01-verification-design.md` §8). Therefore:

> The fabricated `T::default()` value is *entailed-away* by the theorem: no
> observation of `view()` after `restore` can ever return a filler, so the
> *value* `T::default()` produces is unconstrained.

Consequence for implementors: **`default()` may return any in-domain value of
the type.** It does not have to be a "meaningful" element (e.g. a real id, a
real node). It only has to (a) type-check and (b) for `Tagged` types, be a
*clean-domain* value so its encoding is well-formed (§3). Pick the cheapest
zero-ish value.

## 2. Three kinds of element type

Element types fall into three buckets, each with a different recipe:

1. **Plain data**: structs/tuples of already-`Default` fields, no niche.
   *Recipe:* `#[derive(Default)]`. Zero risk.
2. **Enums**: no natural zero.
   *Recipe:* add an explicit filler variant marked `#[default]`.
3. **`Tagged` (bit-stealing) types**: a niche bit is stolen from the value's
   representation for the capture flag (and, for `Opt`, the option bit).
   *Recipe:* `default()` returns a clean-domain value; `into_repr` makes the
   niche safe automatically (§3). This is the subtle one.

## 3. Niche safety for `Tagged` types: the key theorem

A `Tagged` type packs a value + a tag bit into `Repr`. Its contract
(`tagged.rs`) gives, for the encoder:

```
into_repr(t)  ensures  repr_wf(r) ∧ value_of(r) == t ∧ tag_of(r) == false
```

i.e. **for ANY value `t`, `t.into_repr()` is a well-formed repr with the tag
clear.** The filler path is `T::default().into_repr()`. Composing:

> **Niche-safety theorem.** For every `Tagged` type, the regrow filler
> `T::default().into_repr()` is `repr_wf` and has `tag_of == false`,
> *regardless of what `default()` returns*, because `into_repr`'s
> postcondition holds for all inputs. So a `Default` impl introduces **no new
> niche obligation**: it cannot corrupt the stolen bit, because the stolen bit
> is (re)established by `into_repr`, not by `default()`.

What `default()` *does* still owe: it must return a value in the type's
**clean domain**, the value space that excludes the stolen-bit states, so
that `value_of(into_repr(default()))` round-trips. In practice this is free:

- **Bit-stealing ids** (`define_id*!`: MSB stolen): `default() == Self(0)`.
  `0` has the MSB clear, so it is a clean-domain value; `into_repr` keeps it
  clear. (The macro already emits exactly this, see §5.)
- **`BPlusNode`** (steals `FLAG_TAG`, a flag-byte bit): a default node must
  have `FLAG_TAG` clear. `into_repr` clears it anyway, so even
  `#[derive(Default)]` (all-zero flags) is safe, and all-zero clears
  `FLAG_LEAF` too, yielding a (degenerate but well-formed) internal node; since
  it is overwritten on restore, the degeneracy is never observed.
- **`Opt<T>`** (steals the option bit = "None"): `Opt::none()` is the natural
  default; it is `T::default().into_repr()` with the tag set. But note `Opt`
  is *not itself stored*; it lives inside a node struct that owns a *separate*
  capture bit. The node's `Default` defaults its `Opt` field to `none()` (a
  valid clean encoding for the enclosing struct's repr).

### Why composite `Tagged` reprs are also safe

Some types use a tuple/struct `Repr` and delegate the tag to one field
(`Justification<G>`: `Repr = (bool, Justification<G>)`, tag = the `bool`;
`ListNode`/`ListHead`: nested tuple reprs delegating to a sub-field). The same
theorem applies field-locally: the delegated-to field's `into_repr` clears its
bit for any value, and the other fields carry data verbatim. So a default for
the composite is safe as long as each field's default is (recursively) a
clean-domain value, which the field types' own `Default` impls already
guarantee.

## 4. The extensionality caveat (for would-be `Default`-of-repr shortcuts)

Do **not** implement a default by fabricating a raw `Repr` directly (e.g.
`MyRepr::default()` then storing it without `into_repr`). The niche-injectivity
axiom (`lemma_repr_extensional`) only relates `repr_wf` reprs; an arbitrary
all-zero `Repr` might or might not be `repr_wf` depending on the stolen-bit
state. The safe contract is always: **default the VALUE, let `into_repr`
produce the repr.** The store's `resize_default` already does this, so as long
as you implement `Default for T` (the value type), you are safe. Never add a
`Default for T::Repr` shortcut into the regrow path.

## 5. Per-type recipe table (production codebase)

Element types that flow through semi-persistent containers
(`VecI`/`VecP`/`Map`/`SparseSet`/`ListArena`/`BPlusTreeSet`) and the `Default`
each needs:

| Type | Kind | Recipe |
|---|---|---|
| `*Id`, `*Id64` (all `define_id*!`) | bit-steal (MSB) | macro emits `impl Default { Self(0) }`; `0` is clean-domain |
| `u8`, `usize`, `u32`, … | primitive | std `Default` |
| `VariableArityNode<G,O>` | plain data (`Repr`, `usize`, `u8` fields) | `#[derive(Default)]`: all fields `Default` |
| `LitNode<G,O,V>` | plain data | `#[derive(Default)]` |
| `EClassEntry<T>` | `{next: T, repr_stored}` | `Default { next: T::default(), repr_stored: T::Index::default().into_repr() }` (route the id through `into_repr`, per §4) |
| `PoolDirector` | newtype `(u64)` | `#[derive(Default)]` |
| `Justification<G>` | enum | explicit filler: `#[derive(Default)] … #[default] Filler` (or a no-op variant); never observed (§1) |
| `BPlusNode` | `Tagged`, bit-steal `FLAG_TAG` | `#[derive(Default)]` (all-zero is repr-safe via §3) or `default() = new_leaf()` for a non-degenerate filler |
| `BPlusHeader` | plain data (`u32`,`u32`,`usize`) | `#[derive(Default)]` |
| `ListNode<T,N>` | `Tagged`, composite repr | `Default { payload: T::default(), next: Opt::none() }` (needs `T: Default`) |
| `ListHead<N>` | `Tagged`, composite repr | `Default = ListHead::empty()` |
| `Opt<T>` | niche option | `default() = Opt::none()` when `T: Default` (none is the clean filler) |

Notes:
- Types parameterized by a `DenseId`/`Tagged` `T` must add `T: Default` to
  their `Default` impl bound (e.g. `EClassEntry<T> where T: DenseId + Default`).
  Since the `define_id*!` ids are already `Default`, every concrete
  instantiation in the egraph satisfies this.
- `Justification<G>` is the only enum among stored payloads, the only one
  needing a fabricated variant rather than a mechanical derive.

## 6. Verus-side correspondence

In `containers-verus` the same split holds:
- `Vec::restore` carries `where T: core::default::Default`; the `DiffStore`
  `resize_default` is `where T: core::default::Default` and the filler is
  `T::default()` (ParallelStore) / `T::default().into_repr()` (InlineStore).
- The niche-safety theorem (§3) is exactly `Tagged::into_repr`'s ensures
  (`repr_wf(r) ∧ tag_of(r) == false`), and it is discharged for a *real*
  bit-stealing identifier: `DenseId31` (`dense_id.rs`) packs the capture bit in
  the stolen MSB of a `u32`, and its niche-injectivity / value-preservation
  obligations are proved by the bit-vector solver, not left vacuous as in the
  `BoolTagged` fallback (`repr_wf := true`). Since every concrete `Tagged` impl
  owes the same ensures, a verified `Default` impl needs **no new proof** about
  the niche; `into_repr`'s postcondition discharges it at the regrow site.
- Filler soundness (§1) is not an assumed axiom: it is a *consequence* of the
  proved `view() == snapshots[token]` theorem, so no `Default` impl can weaken
  correctness regardless of the value it returns.

---
[← Table of Contents](00-table-of-contents.md)
