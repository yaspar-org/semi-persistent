# Chapter 1: Dense Identifiers and the `Tagged` Trait

[← Table of Contents](00-table-of-contents.md) · [Ch 2: Semi-Persistent Vectors →](02-semi-persistent-vectors.md)


## Motivation

Many high-performance systems (e-graph engines, SAT solvers, constraint
propagators, game-tree searchers) allocate objects in dense pools indexed
by small integers. These ids are used as array indices into flat vectors,
with no pointer chasing and no hash lookups on the hot path.

Applications that use pool-allocated data structures need three things
from their id-indexed storage:

1. Optional values. Many slots are nullable: a parent pointer may be
   absent, a list head may be empty. `Option` around these ordinary 4-byte
   id newtypes has no invalid-value niche and therefore occupies 8 bytes on
   the supported layouts. A tagged representation keeps it at 4 bytes.

2. Lookup structures. Ids serve as keys into hash maps and sorted
   indices. They must implement `Eq`, `Ord`, and `Hash` cheaply.

3. Semi-persistence. Backtracking search requires snapshotting the
   entire state and restoring it later. The implementation is a
   diff log: on `mark()`, start recording; on each mutation, log the
   old value before overwriting; on `restore()`, replay the log in
   reverse. The critical cost is *detecting first writes*; each slot
   must track whether it has already been captured since the last
   mark. A naive approach adds a `bool` per slot (1 byte + padding),
   or a parallel `BitSet` (1 bit per slot in a separate allocation).

All three problems share a solution: bit-packing into the id
itself. This design deliberately limits a 32-bit id to 31 payload bits,
still addressing about 2.1 billion entries. The reserved MSB becomes a tag bit that different
consumers can repurpose:

| Consumer | Tag meaning |
|----------|-------------|
| `InlineStore` | "captured since last mark": no extra per-cell capture storage |
| `Opt<T>` | "none": no extra discriminant storage |
| `ListHead` | "empty list" |

The `Tagged` trait abstracts over this: any value type that defines a stored
representation with a readable and writable tag. For dense ids, the tag is
the MSB. Primitive integer implementations use an out-of-band `(bool, T)`
representation; `BoolTagged<T>` is the named representation helper used for
the same purpose by explicit implementations.

## The `DenseId` Type

The ID types are called *dense* because their integer payload can be used
directly as a vector index. The type itself does not allocate IDs or guarantee
contiguity. When an arena or `IdFactory` allocates sequentially from zero
without deletion or recycling, its allocated IDs form `[0, n)`, and a `Vec<T>`
indexed by that ID type is a perfect map: O(1) lookup, no hashing, and no holes.
Recycling structures such as `SparseSet` use the same ID types but need not have
a contiguous set of currently live IDs.

Where the owning allocator establishes the dense-allocation invariant,
pool-based systems can store per-object metadata in flat `Vec`s rather than
`HashMap`s: the vector index *is* the ID.

## `define_id31!`

The `define_id31!` macro stamps out a `#[repr(transparent)]` newtype
around `u32` with bit 31 reserved:

| Surface | Repr | Purpose |
|---------|------|---------|
| `NodeId` | `u32` | Clean user-facing id. MSB always 0. |
| `<NodeId as Tagged>::Repr` | `u32` | Stored word. MSB = capture flag. |

Trait impls on the clean `NodeId` all mask out the MSB: `PartialEq`
compares `(self.0 & 0x7FFF_FFFF)`, and `Ord` and `Hash` apply the
same mask. `Debug` prints `e42` (prefix + raw value).

The macro syntax still accepts `StoredNodeId` and the plain crate retains that
legacy companion symbol for existing users. It is not the portable storage
type: the verified macro uses that identifier for a hidden implementation
module. Code intended to swap between crates must use
`<NodeId as Tagged>::Repr`, which is the backing integer in both
implementations. `Tagged::from_repr` masks the tag before producing a clean ID,
so the tag is invisible to user-facing ID operations. Variants exist for other
widths: `define_id7!` (7-bit), `define_id15!` (15-bit), and `define_id63!`
(63-bit for large pools).

The generated runtime surface shared with `containers-verus` includes
`new`/`raw`, `index`/`to_usize`, `DenseId::to_index`,
`DenseId::try_new`, `IndexLike::min`/`max`, and the tag operations. Use
`try_new` at a capacity boundary. The plain crate deliberately panics rather
than aliases IDs when `from_usize` is out of range; portable callers must not
rely on either implementation's out-of-range `from_usize` behavior.

## The `Tagged` Trait

This trait is the abstraction for values that carry a tag bit
that can we queried, set and reset.

```rust
pub trait Tagged: Copy + Default {
    type Repr: Copy;
    fn into_repr(self) -> Self::Repr;
    fn from_repr(r: &Self::Repr) -> Self;
    fn tag(r: &Self::Repr) -> bool;
    fn set_tag(r: &mut Self::Repr);
    fn clear_tag(r: &mut Self::Repr);
}
```

For `DenseId` types, `Tagged` is implemented by the `define_id!` macro:
`into_repr` returns the raw word, `from_repr` masks out the MSB,
`set_tag` ORs in the MSB, `clear_tag` ANDs it out.

Different consumers interpret the tag differently: Semi-persistent vectors
require `Tagged<T>` so they can use that control bit to track marked versions
and capture old values on first mutation. `Opt<T>` requires `Tagged<T>`
and uses the tag bit to encode `Some`/`None`.

| Consumer | Tag semantics |
|----------|--------------|
| `InlineStore` | "captured": slot modified since last mark |
| `Opt<T>` | "none": slot is absent |
| `ListHead` | "empty list" flag |

## `Opt<T>`: Tagged Nullable

`Opt<T>` reuses `T`'s tag bit to encode `None`, wrapping a single
`T::Repr`:

`Opt::none()` creates a repr with the tag set. `Opt::some(val)` stores
the repr with tag clear. `Opt::get()` checks the tag.

`Opt<T>` does NOT implement `Tagged` itself.
If it did, storing `Opt<T>` in an `InlineStore` would try to steal the
same bit for capture tracking that `Opt` uses for None, corrupting
both. Instead, `Opt<T>` appears only as a field inside a struct that
implements `Tagged` via a *different* field.

## Out-of-Band Tags

Primitive integers implement `Tagged` with `Repr = BoolTagged<T>`, a named
`(bool, T)` shape shared with the verified crate. The representation pays
padding overhead but still supports inline semi-persistence. There is no
blanket `Tagged` implementation for arbitrary `T`.

```rust
pub struct BoolTagged<T> {
    pub tagged: bool,
    pub value: T,
}
```

For a `BoolTagged<T>` representation, `tag` reads the bool and
`set_tag`/`clear_tag` flip it. These representation strategies are distinct
from the two `DiffStore` backends for the semi-persistent vector:

| | `InlineStore<T: Tagged>` | `ParallelStore<T>` |
|---|---|---|
| Storage | `Vec<T::Repr>` | `Vec<T>` + `BitSet` |
| Tag location | Inline in each slot | Separate bit vector |
| Capture-storage overhead | No separate allocation; depends on `T::Repr` | 1 bit per materialized slot |
| Requires `Tagged` | Yes | No |
| Best for | Types whose representation already has a free bit | Arbitrary types |

Both implement the same `DiffStore` trait. The semi-persistent vector
is generic over the backend.

## Compile-Time Elision: `const TRACK: bool`

Every semi-persistent container is parameterized by `const TRACK: bool`.
When `TRACK = false`, `InlineStore::capture()` is a no-op,
`prepare_mark()` skips clearing tags, `restore_entry()` is a no-op,
and the diff log is never written. The compiler eliminates all
const-gated tracking work, which is useful for read-only configurations or
benchmarks where push/pop is not needed. The generic vector still retains its
empty diff, frame, and fork-history fields, plus general runtime guards; this
is execution elision with retained empty-state fields, not a zero-layout or
minimum-layout claim.

## Defining Your Own ID Types

The `define_id31!` macro stamps out a new id type. For example:

```rust
semi_persistent_containers::define_id31! {
    pub struct NodeId / StoredNodeId, "n";
}
```

This produces `NodeId` (clean, MSB always 0); the second identifier is a
legacy compatibility slot and must not be named by portable callers. The
string `"n"` is the debug prefix: `NodeId::new(42)` prints as `n42`. Variants
exist for other widths:
`define_id7!` (7-bit), `define_id15!` (15-bit), `define_id63!`
(63-bit for large pools).

The generated clean ID implements `DenseId`, `Tagged`, `IndexLike`, `Eq`,
`Ord`, `Hash`, and `Debug`, with the MSB masked out in comparisons. Its
stored representation is the backing integer and is used through the
`Tagged` methods.

`containers-conformance/tests/id_macro_parity.rs` instantiates all four widths
from both crates and applies the same runtime contract plus randomized
value/tag checks. This establishes a maintained DenseId macro compatibility
surface. It does not claim that the entire `containers` and
`containers-verus` crate APIs are dependency-swappable.

---
[← Table of Contents](00-table-of-contents.md) · [Ch 2: Semi-Persistent Vectors →](02-semi-persistent-vectors.md)
