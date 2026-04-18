# Chapter 1 — Dense Identifiers and the `Tagged` Trait

[← Table of Contents](00-table-of-contents.md) · [Ch 2: Semi-Persistent Vectors →](02-semi-persistent-vectors.md)


## Motivation

Many high-performance systems — e-graph engines, SAT solvers, constraint
propagators, game-tree searchers — allocate objects in dense pools indexed
by small integers. These ids are used as array indices into flat vectors,
with no pointer chasing and no hash lookups on the hot path.

Applications that use pool-allocated data structures need three things
from their id-indexed storage:

1. Optional values. Many slots are nullable: a parent pointer may be
   absent, a list head may be empty. The standard `Option<T>` costs
   4 extra bytes per slot (discriminant + padding) for a 4-byte id.
   At millions of slots, that doubles memory.

2. Lookup structures. Ids serve as keys into hash maps and sorted
   indices. They must implement `Eq`, `Ord`, and `Hash` cheaply.

3. Semi-persistence. Backtracking search requires snapshotting the
   entire state and restoring it later. The implementation is a
   diff log: on `mark()`, start recording; on each mutation, log the
   old value before overwriting; on `restore()`, replay the log in
   reverse. The critical cost is *detecting first writes*; each slot
   must track whether it has already been captured since the last
   mark. A naive approach adds a `bool` per slot (1 byte + padding),
   or a parallel `BitSet` (1 bit per slot, but a separate allocation
   and cache line).

All three problems share a solution: bit-packing into the id
itself. A 32-bit id only needs 31 bits to address 2 billion
entries. The remaining MSB becomes a free tag bit that different
consumers can repurpose:

| Consumer | Tag meaning |
|----------|-------------|
| `InlineStore` | "captured since last mark": zero-overhead semi-persistence |
| `Opt<T>` | "none": zero-overhead nullable ids |
| `ListHead` | "empty list" |

The `Tagged` trait abstracts over this: any type that can store and
retrieve a tag bit in its representation. For dense ids, the tag is
the MSB. For types that can't spare a bit, a fallback `BoolTagged`
wrapper stores the tag as a separate `bool`.

## The `DenseId` Type

All ids are called *dense* because they are allocated sequentially
starting from 0: the first object gets id 0, the second gets id 1,
and so on. At any point, all live ids form a contiguous range `[0, n)`.
This has a key consequence: a `Vec<T>` indexed by the id type is a
perfect map from ids to values: O(1) lookup, no hashing, no holes,
no wasted capacity. Every slot in the vector corresponds to exactly
one live id.

The dense allocation invariant is why pool-based systems store
per-object metadata in flat `Vec`s rather than `HashMap`s: the vector
index *is* the id.

## `define_id31!`

The `define_id31!` macro stamps out a `#[repr(transparent)]` newtype
around `u32` with bit 31 reserved, producing two types:

| Type | Repr | Purpose |
|------|------|---------|
| `NodeId` | `u32` | Clean user-facing id. MSB always 0. |
| `StoredNodeId` | `u32` | Internal repr. MSB = capture flag. |

Derived trait impls on `NodeId` all mask out the MSB: `PartialEq`
compares `(self.0 & 0x7FFF_FFFF)`, and `Ord` and `Hash` apply the
same mask. `Debug` prints `e42` (prefix + raw value).

Because of this masking, two stored values that differ only in the
tag bit compare as equal, hash identically, and sort the same way.
The tag is invisible to all user-facing operations. Variants exist
for other widths: `define_id7!` (7-bit), `define_id15!` (15-bit),
`define_id63!` (63-bit for large pools).

## The `Tagged` Trait

This trait is the abstraction for values that carry a tag bit
that can we queried, set and reset.

```rust
pub trait Tagged: Clone {
    type Repr: Clone;
    fn into_repr(self) -> Self::Repr;
    fn from_repr(r: &Self::Repr) -> Self;
    fn tag(r: &Self::Repr) -> bool;
    fn set_tag(r: &mut Self::Repr);
    fn clear_tag(r: &mut Self::Repr);
}
```

For `DenseId` types, `Tagged` is implemented by the `define_id!` macro:
`into_repr` wraps the raw value, `from_repr` masks out the MSB,
`set_tag` ORs in the MSB, `clear_tag` ANDs it out.

Different consumers interpret the tag differently: Semi-persistent vectors
require `Tagged<T>` so they can use that control bit to track marked versions
and capture old values on first mutation. `Opt<T>` requires `Tagged<T>`
and uses the tag bit to encode `Some/None, etc.

| Consumer | Tag semantics |
|----------|--------------|
| `InlineStore` | "captured": slot modified since last mark |
| `Opt<T>` | "none": slot is absent |
| `ListHead` | "empty list" flag |

## `Opt<T>` — Tagged Nullable

`Opt<T>` reuses `T`'s tag bit to encode `None`, wrapping a single
`T::Repr`:

`Opt::none()` creates a repr with the tag set. `Opt::some(val)` stores
the repr with tag clear. `Opt::get()` checks the tag.

`Opt<T>` does NOT implement `Tagged` itself.
If it did, storing `Opt<T>` in an `InlineStore` would try to steal the
same bit for capture tracking that `Opt` uses for None, corrupting
both. Instead, `Opt<T>` appears only as a field inside a struct that
implements `Tagged` via a *different* field.

## `BoolTagged<T>` — Out-of-Band Tag

For types that cannot offer a spare bit, `BoolTagged<T>` stores the tag as
a separate `bool`. In that case we pay the padding overhead but can still
benefit from semi-persistence.

```rust
pub struct BoolTagged<T>(bool, T);
```

`Tagged` impl: `tag` reads the bool, `set_tag`/`clear_tag` flip it.
This costs 1 extra byte per slot (plus padding), but works for any
`T`. These two strategies correspond to the two `DiffStore` backends
for the semi-persistent vector:

| | `InlineStore<T: Tagged>` | `ParallelStore<T>` |
|---|---|---|
| Storage | `Vec<T::Repr>` | `Vec<T>` + `BitSet` |
| Tag location | Inline in each slot | Separate bit vector |
| Memory overhead | 0 bytes per slot | 1 bit per slot |
| Requires `Tagged` | Yes | No |
| Best for | DenseId types (free tag) | Arbitrary types |

Both implement the same `DiffStore` trait. The semi-persistent vector
is generic over the backend.

## Compile-Time Elision: `const TRACK: bool`

Every semi-persistent container is parameterized by `const TRACK: bool`.
When `TRACK = false`, `InlineStore::capture()` is a no-op,
`prepare_mark()` skips clearing tags, `restore_entry()` is a no-op,
and the diff log is never written. The compiler eliminates all
tracking code entirely, which is useful for read-only configurations or
benchmarks where push/pop is not needed.

## Defining Your Own ID Types

The `define_id31!` macro stamps out a new id type. For example:

```rust
semi_persistent_containers::define_id31! {
    pub struct NodeId / StoredNodeId, "n";
}
```

This produces `NodeId` (clean, MSB always 0) and `StoredNodeId`
(internal repr, MSB = tag bit). The string `"n"` is the debug prefix:
`NodeId::new(42)` prints as `n42`. Variants exist for other widths:
`define_id7!` (7-bit), `define_id15!` (15-bit), `define_id63!`
(63-bit for large pools).

All generated types implement `DenseId`, `Tagged`, `IndexLike`,
`Eq`, `Ord`, `Hash`, and `Debug`, with the MSB masked out in all
comparisons.

---
[← Table of Contents](00-table-of-contents.md) · [Ch 2: Semi-Persistent Vectors →](02-semi-persistent-vectors.md)
