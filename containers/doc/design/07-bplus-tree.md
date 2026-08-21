# Chapter 7: `BPlusTreeSet`, Arena-Backed B+ Tree

[← Ch 6: SparseSet](06-sparse-set.md) · [Table of Contents](00-table-of-contents.md)

`BPlusTreeSet` is a packed, insert-only B+ tree set of `DenseId` keys. It is
backed by a semi-persistent node arena and parameterized at compile time over
key width, node geometry, in-node search, and tracking:

```rust
pub struct BPlusTreeSet<
    K: DenseId,
    L: NodeLayout<Word = K::Index> = Layout64U32,
    S: SearchKind = BinarySearch,
    const TRACK: bool = true,
> { /* ... */ }
```

Leaves form a linked list, so ordered iteration advances without walking back
up the tree. The tree supports insertion and query cursors, but not deletion.

## Motivation

Sorted containers are needed for ordered iteration and seek-based intersection.
A sorted vector is compact and fast to scan, but an insertion can shift O(n)
elements. The B+ tree keeps insertion logarithmic in the number of keys while
retaining contiguous in-node searches and constant-time movement between
adjacent leaf entries.

## Node Layouts

Every layout supplies one fixed-size, cache-aligned node type. A node contains a
small header, a word array, and a link field:

- A leaf stores sorted keys in `data[0..count]`; `link` names the next leaf.
- An internal node stores sorted separators in the lower part of `data` and
  child indices in the upper part. Its final child reuses `link`.
- `ArenaIdx::MAX` is reserved as the null link.
- Header flag bits distinguish leaves and carry the semi-persistent capture tag.

The available layouts are:

| Layout | Word | Arena index | Bytes | Leaf keys | Internal keys | Children |
|---|---:|---:|---:|---:|---:|---:|
| `Layout64U32` | `u32` | `u32` | 64 | 14 | 7 | 8 |
| `Layout128U32` | `u32` | `u32` | 128 | 30 | 14 | 15 |
| `Layout256U32` | `u32` | `u32` | 256 | 62 | 30 | 31 |
| `Layout128U64` | `u64` | `usize` | 128 | 14 | 6 | 7 |
| `Layout256U64` | `u64` | `usize` | 256 | 30 | 14 | 15 |
| `Layout512U64` | `u64` | `usize` | 512 | 62 | 30 | 31 |

The `u32` layouts pair with 31-bit dense IDs. On 64-bit targets, the `u64`
layouts pair with 63-bit dense IDs and use `usize` arena indices. The default is
`Layout64U32`; callers choose a different layout explicitly when its footprint
and target-specific performance are preferable.

## Search Strategies

`SearchKind` controls how separators and leaf keys are searched:

- `BinarySearch`, the default, uses `slice::partition_point`.
- `Branchless` counts comparisons in a linear scan that the compiler may
  vectorize.

Neither strategy is universally faster across layouts and targets. The
Criterion benchmark in
[`containers/benches/bplus_bench.rs`](../../benches/bplus_bench.rs) exercises
the supported combinations; performance decisions should be based on its
confidence intervals on the deployment architecture, not a single timing run.

## Operations

### Insert

`insert(key)` returns `true` exactly when it adds a new key.

- If the key is greater than the current maximum and the rightmost leaf has
  room, insertion appends directly to that leaf.
- Otherwise the tree descends through internal separators while recording the
  path. A non-full target leaf is updated in place. A full leaf is split and its
  separator is propagated upward; full internal nodes split in turn, possibly
  creating a new root.

In this reference crate, the descent path uses a fixed 24-entry stack array.
Every built-in layout has `MAX_DEPTH <= 24`; the reference implementation
checks that relationship only with `debug_assert!`, so a custom layout that
exceeds 24 is not rejected in a release build and is outside the supported
layout set.

### Bulk Construction

`from_sorted(keys)` builds leaves and internal levels bottom-up in O(n). Its
input contract is stricter than its type: keys must be strictly increasing and
deduplicated. The reference implementation checks this only by
`debug_assert!`, so its release callers must establish the condition
themselves. The verified production implementation performs an unconditional
linear refusal check and proves the resulting model for every returning call.

### Cursor

`BPlusCursor` exposes `seek`, `seek_first`, `key`, and `step`:

| Operation | Behavior |
|---|---|
| `seek(target)` | Positions at the least key greater than or equal to `target`, or exhaustion. |
| `seek_first()` | Positions at the least key. |
| `key()` | Returns the current key, or `None` at exhaustion. |
| `step()` | Advances one entry, following the leaf link at a leaf boundary. |

For repeated forward seeks, `seek` first checks the current leaf and its next
linked leaf. It falls back to a root descent when those leaves cannot answer the
query, including backward seeks.

## Arena And Semi-Persistence

Nodes live in `VecI<L::Node, L::ArenaIdx, TRACK>`. The mutable tree header
(`root`, `last_leaf`, and key count) lives in a one-element
`VecP<BPlusHeader<_>, u32, TRACK>`. A `BPlusToken` composes snapshots of both
stores; restoring it rewinds node mutations, post-mark allocations, and header
changes together.

The tree is append-only at the arena level. It has no free list: ordinary
operation never removes nodes, while restore can truncate nodes allocated after
the corresponding mark.

Capture state uses a flag bit already present in every fixed-size node header,
so it does not add a separate field per node. Marks are not unconditionally
O(1): the underlying inline store clears capture bits associated with the prior
frame, with work proportional to the cells it must clear. Restore cost follows
the underlying stores and the amount of state changed after the mark.

With `TRACK = false`, tracking branches and capture/log execution are removed by
constant specialization. The generic stores and token still retain their
tracking-related fields, which remain empty or at their initial state; this is
an execution-overhead elision claim, not a zero-layout-overhead claim.

## Scope And Tradeoffs

- The tree is a set: duplicate insertion is a no-op and returns `false`.
- Deletion and merge/borrow rebalancing are intentionally absent.
- Layout and search choices affect footprint and machine-specific performance,
  so the library exposes them instead of asserting one universal optimum.
- The verified implementation and proof status are documented in
  [`containers-verus/doc/design/10-bplus-tree.md`](../../../containers-verus/doc/design/10-bplus-tree.md).

---
[← Ch 6: SparseSet](06-sparse-set.md) · [Table of Contents](00-table-of-contents.md)
