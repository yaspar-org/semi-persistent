# Default implementations for container element types — design

Status: DESIGN / guidance. Explains why every value type stored in a
semi-persistent container now needs `Default`, why a fabricated default is
*sound* (never observable), and — the subtle part — how a `Tagged` type's
niche (stolen bit) stays safe when a default filler is created. Ends with a
per-type recipe table for the whole production codebase.

## 0. Why `Default` is now required

`restore` regrows a popped/shrunk region with `resize_default(saved_len)`
BEFORE replaying the diff log (see `03-pop.md`, `restore-regrow-
alternatives.md`). Growing the backing store needs *some* value to put in the
new slots, and we use `T::default()`:

- `ParallelStore::resize_default` → `self.data.push(T::default())`
  (`parallel_store.rs`).
- `InlineStore::resize_default` → `self.data.push(T::default().into_repr())`
  (`inline_store.rs`) — note the filler is `default()` **passed through
  `into_repr`**. This routing is the whole story for niche safety (§3).

So every `T` that can be the element type of a semi-persistent `Vec` (directly,
or transitively via `Map`/`SparseSet`/`ListArena`/`BPlusTreeSet`, which are
built on `Vec`) must implement `Default`. The crate models the `Copy` subset of
`Clone`, so concretely the bound is `T: Copy + Default`.

## 1. Filler soundness — a default is never observable

The headline restore theorem is `view() == snapshots[token.frame_idx]`. A
filler written by `resize_default` lives at a position that the backward replay
then **overwrites** with the captured diff value (coverage guarantees every
regrown cell has a diff — `01-verification-design.md` §8). Therefore:

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

1. **Plain data** — structs/tuples of already-`Default` fields, no niche.
   *Recipe:* `#[derive(Default)]`. Zero risk.
2. **Enums** — no natural zero.
   *Recipe:* add an explicit filler variant marked `#[default]`.
3. **`Tagged` (bit-stealing) types** — a niche bit is stolen from the value's
   representation for the capture flag (and, for `Opt`, the option bit).
   *Recipe:* `default()` returns a clean-domain value; `into_repr` makes the
   niche safe automatically (§3). This is the subtle one.

## 3. Niche safety for `Tagged` types — the key theorem

A `Tagged` type packs a value + a tag bit into `Repr`. Its contract
(`tagged.rs`) gives, for the encoder:

```
into_repr(t)  ensures  repr_wf(r) ∧ value_of(r) == t ∧ tag_of(r) == false
```

i.e. **for ANY value `t`, `t.into_repr()` is a well-formed repr with the tag
clear.** The filler path is `T::default().into_repr()`. Composing:

> **Niche-safety theorem.** For every `Tagged` type, the regrow filler
> `T::default().into_repr()` is `repr_wf` and has `tag_of == false`,
> *regardless of what `default()` returns* — because `into_repr`'s
> postcondition holds for all inputs. So a `Default` impl introduces **no new
> niche obligation**: it cannot corrupt the stolen bit, because the stolen bit
> is (re)established by `into_repr`, not by `default()`.

What `default()` *does* still owe: it must return a value in the type's
**clean domain** — the value space that excludes the stolen-bit states — so
that `value_of(into_repr(default()))` round-trips. In practice this is free:

- **Bit-stealing ids** (`define_id*!`: MSB stolen): `default() == Self(0)`.
  `0` has the MSB clear, so it is a clean-domain value; `into_repr` keeps it
  clear. (The macro already emits exactly this — see §5.)
- **`BPlusNode`** (steals `FLAG_TAG`, a flag-byte bit): a default node must
  have `FLAG_TAG` clear. `into_repr` clears it anyway, so even
  `#[derive(Default)]` (all-zero flags) is safe — and all-zero clears
  `FLAG_LEAF` too, yielding a (degenerate but well-formed) internal node; since
  it is overwritten on restore, the degeneracy is never observed.
- **`Opt<T>`** (steals the option bit = "None"): `Opt::none()` is the natural
  default — it is `T::default().into_repr()` with the tag set. But note `Opt`
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
clean-domain value — which the field types' own `Default` impls already
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

## 5. Per-type recipe table (production codebase) — LANDED

> **Status: all landed in production.** The recipes below were applied on the
> `feature/production-bounded-pop` branch. Statuses now read **DONE**; the
> "as-landed" column records what actually shipped, including a few deviations
> from the original predictions (called out under Notes).

Audited element types that flow through semi-persistent containers
(`VecI`/`VecP`/`Map`/`SparseSet`/`ListArena`/`BPlusTreeSet`):

| Type | Where | Kind | As landed |
|---|---|---|---|
| `*Id`, `*Id64` (all `define_id*!`) | `id.rs`, `egraph/nodes.rs`, … | bit-steal (MSB) | **DONE** — macro emits `impl Default { Self(0) }` (`id.rs:176`). `0` is clean-domain. |
| `u8`, `usize`, `u32`, … | union-find `rank`, indices | primitive | **DONE** — std `Default`. |
| `FixedArityNode<G,O,K>` | `node_types.rs:29` | plain data, raw `Repr` fields | **DONE** — hand impl via `new(G::default(), O::default(), [G::default(); K])` (not in original audit; routes ids through `into_repr`). |
| `VariableArityNode<G,O>` | `node_types.rs:121` | plain data, raw `Repr` fields | **DONE** — hand impl via `make(...)`, not a derive: the struct stores `G::Repr`, so `#[derive(Default)]` would demand `G::Repr: Default`. |
| `LitNode<G,O,V>` | `node_types.rs:207` | plain data, raw `Repr` fields | **DONE** — hand impl via `new(...)` (same raw-`Repr` reason as above). |
| `EClassEntry<T>` | `classes.rs:21` | `{next: T, repr_stored}` | **DONE** — `Default { Self::new(T::default(), T::Index::default()) }` (id routed through `into_repr`, per §4). |
| `PoolDirector` | `director.rs:464` | newtype `(u64)`, bit-steal (MSB) | **DONE** — hand impl `PoolDirector::new(0)` (clears the MSB tag), not a derive. |
| `Justification<G>` | `union_find.rs:52` | enum | **DONE** — `#[derive(... Default)]` + explicit `#[default] Filler`; `make_set` now pushes `Filler`. Never observed (§1). |
| six `define_node!` structs | `bplus.rs:46` | `Tagged`, bit-steal `FLAG_TAG` | **DONE** — macro emits a manual all-zero `Default` (`flags: 0` clears the tag); `data` array can exceed `[T; N]: Default`'s 32-element limit, so not a derive. Covers `BPlusNode{64,128,256}U32` + `{128,256,512}U64`. |
| `BPlusHeader<I>` | `bplus.rs:387` | plain data (`I`,`I`,`usize`) | **DONE** — `#[derive(Default)]` (`I: Copy`, default via `ArenaIdx: Default`). |
| `ListNode<T,N>` | `list.rs:23` | `Tagged`, composite repr | **DONE** — `Default = Self::new(T::default(), Opt::none())` (needs `T: Default`). |
| `ListHead<N>` | `list.rs:71` | `Tagged`, composite repr | **DONE** — `Default = ListHead::empty()`. |
| `Opt<T>` | `tagged.rs:57` | niche option | **DONE** — `default() = Opt::none()` when `T: Tagged + Default`. |
| `Multiplicity` | `egraph/multiplicity.rs:7` | newtype `(u32)` | **DONE** — `#[derive(Default)]`; needed so the `(A, B): Tagged` impl (with `B = Multiplicity`) satisfies the `Tagged: Default` floor, hence `EGraphConfig::C = (G, Multiplicity)` is `Default`. |

Notes:
- Types parameterized by a `DenseId`/`Tagged` `T` get `T: Default` for free:
  `DenseId` already lists `Default` as a supertrait, and `Tagged` now does too
  (see Bound propagation below), so their `Default` impls need no extra bound.
- `Justification<G>` is the **only** enum among stored payloads — the only one
  needing a fabricated variant rather than a mechanical derive.
- **Deviation — raw-`Repr` node structs.** The three node types
  (`Fixed`/`Variable`/`Lit`Node) store *raw reprs* (`G::Repr`), not values, so a
  `#[derive(Default)]` would generate the wrong bound (`G::Repr: Default`). They
  use hand impls that default the id *values* and route through `into_repr`,
  which is also the §4-correct (niche-safe) recipe. `FixedArityNode` was missing
  from the original audit and was added during the landing.
- **Deviation — `BPlusNode` count.** The merged `NodeLayout` B+tree stamps
  **six** layout structs via `define_node!`, not one. The `Default` is emitted
  once inside the macro.
- **Bound propagation — `Default` belongs on `Tagged`, the value facet.** The
  store-level requirement is "every *stored value* has a throwaway default for
  the restore filler." A stored value enters an inline store iff it is `Tagged`
  (the `Copy`, tag-bit-packed value facet), so `Tagged: Copy + Default` is the
  minimal, correctly-placed home for the bound. It is *not* placed on
  `IndexLike`: that trait is the *indexing* facet (the `I` in `Vec<T, I, S>`),
  orthogonal to whether a type is stored — and `IndexLike` is public, so
  widening it would force `Default` on every downstream custom index. (Index
  types that *are* also stored as values — `SparseSet`'s `Idx`, `EClassEntry`'s
  `T::Index` — are bounded `IndexLike + Tagged`, so they pick up `Default`
  through `Tagged`, not `IndexLike`.)
  With `Tagged: Default` (and `DenseId: Default`, pre-existing), the only
  `Default` bounds that remain in the source are the irreducible ones:
  - `DiffStore::resize_default` — `where T: Default` (the method that *produces*
    the filler; the origin of the whole requirement);
  - `Vec::restore` and `SparseSet::restore` — `where T: Default`, because their
    element is bounded only `T: Clone` (the `ParallelStore` / foreign-value path
    that does not go through `Tagged`).
  Everything else (`ListArena`, `BPlusTreeSet`, the caches, `NodeStore`,
  `EGraph`, and `EGraphConfig::C`) stores `Tagged` values, so it carries **no**
  `Default` bound at all. Note `NodeLayout::ArenaIdx` was already declared
  `IndexLike + Default` independently — evidence the design always treated
  `Default` as orthogonal to `IndexLike`.

## 6. Verus-side correspondence

In `containers-verus` the same split holds:
- `Vec::restore` carries `where T: core::default::Default`; the `DiffStore`
  `resize_default` is `where T: core::default::Default` and the filler is
  `T::default()` (ParallelStore) / `T::default().into_repr()` (InlineStore).
- The niche-safety theorem (§3) is exactly `Tagged::into_repr`'s ensures
  (`repr_wf(r) ∧ tag_of(r) == false`), and it is discharged for a *real*
  bit-stealing identifier: `DenseId31` (`dense_id.rs`) packs the capture bit in
  the stolen MSB of a `u32`, and its niche-injectivity / value-preservation
  obligations are proved by the bit-vector solver — not left vacuous as in the
  `BoolTagged` fallback (`repr_wf := true`). Since every concrete `Tagged` impl
  owes the same ensures, a verified `Default` impl needs **no new proof** about
  the niche — `into_repr`'s postcondition discharges it at the regrow site.
- Filler soundness (§1) is not an assumed axiom: it is a *consequence* of the
  proved `view() == snapshots[token]` theorem, so no `Default` impl can weaken
  correctness regardless of the value it returns.

## 7. Landing order (as executed)

Landed on `feature/production-bounded-pop` in this order:

1. `DiffStore` trait + backends: `mark_captured` + `resize_default`; removed the
   dead `force_capture`.
2. `Vec` algorithm: `pop` → first-write-wins `capture`; `push` → `mark_captured`
   re-entry branch; `restore` → `resize_default` + overwrite replay, `where T:
   Default`.
3. `Default` impls for the stored types (§5 table) — hand impls for the
   raw-`Repr` node structs and bit-steal newtypes (route through `into_repr`),
   the `#[default] Filler` enum variant, the macro-emitted B+tree node default.
4. Bound propagation: `Default` on the `Tagged` supertrait (the value facet),
   leaving explicit `where T: Default` only on `DiffStore::resize_default` and
   the two `Clone`-floor restores (`Vec`, `SparseSet`).
5. Tests: the bounded-pop DoS regression (`containers/tests/bounded_pop_test.rs`)
   + restore round-trip + set-after-reentry.

The gate noted in the original plan (the semi-naive→main merge changing
`BPlusNode` into multiple layout structs) did land first, and the re-audit
confirmed **six** `define_node!` structs plus the extra `FixedArityNode` — both
handled above.

---
[← Table of Contents](00-table-of-contents.md)
