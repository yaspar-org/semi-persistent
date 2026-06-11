# Chapter 7 — `BPlusTreeSet` — Arena-Backed B+ Tree

[← Ch 6: SparseSet](06-sparse-set.md) · [Ch 8: Benchmark Analysis →](08-bplus-benchmark-analysis.md) · [Table of Contents](00-table-of-contents.md)

A cache-line-aligned B+ tree set of `u32` keys, backed by an arena
of fixed-size 64-byte nodes. Supports O(log n) insert, O(log n) seek,
and O(1) step for ordered iteration via linked leaves.

## Motivation

Sorted containers are needed whenever an application must iterate
keys in order or perform seek-based intersection (e.g. leapfrog
triejoin). A sorted `Vec` works well when the data is built once and
queried many times, but incremental insertion into a sorted `Vec` is
O(n) due to shifting. The B+ tree offers O(log n) insert while
preserving cache-friendly ordered iteration through linked leaf nodes.

## Node Layout

All nodes — leaf and internal — share a single 64-byte
cache-aligned struct stored in a flat semi-persistent `Vec<BPlusNode>` arena:

```rust
#[repr(C, align(64))]
pub struct BPlusNode {
    len_flags: u16,      // low 15 bits = count, bit 15 = is_leaf
    link_or_pad: u32,    // leaf: next-leaf pointer; internal: 8th child
    data: [u32; 14],     // leaf: up to 14 keys; internal: 7 keys + 7 children
}
```

The 64-byte alignment ensures each node fits in exactly one cache
line. Leaf vs internal is encoded in the MSB of `len_flags`, avoiding
a separate discriminant field.

| Node type | Keys | Children | Link |
|-----------|------|----------|------|
| Leaf | up to 14 in `data[0..14]` | — | `link_or_pad` → next leaf |
| Internal | up to 7 in `data[0..7]` | up to 7 in `data[7..14]`, 8th in `link_or_pad` | — |

## Operations

### Insert

Insert follows the standard B+ tree algorithm with an optimization:

**Fast path:** If the key is greater than all existing keys and the
rightmost leaf has room, it appends in O(1) without tree traversal.
This makes sequential insertion (the common case when building an
index from sorted data) very fast.

**General path:** Iterative descent saving the path on a stack-allocated
array (max depth 8, since branching factor 8 with 14-key leaves
supports billions of entries). On leaf overflow, split in-place and
propagate the separator key upward. Root splits create a new root.

### Bulk Construction

`from_sorted(data)` builds the tree bottom-up in O(n):

1. Pack leaves left-to-right, filling each to capacity (14 keys)
2. Link leaves into a chain
3. Build internal levels bottom-up, each internal node holding up to
   8 children

This is significantly faster than repeated insertion for pre-sorted
data.

### Cursor / Iteration

`BPlusCursor` provides seek-and-step iteration:

```rust
pub struct BPlusCursor<'a> {
    tree: &'a BPlusTreeSet,
    node: u32,   // current leaf index
    pos: usize,  // position within leaf
}
```

| Operation | Cost | Description |
|-----------|------|-------------|
| `seek(key)` | O(log n) | Position at first key ≥ target |
| `key()` | O(1) | Current key, or `None` if exhausted |
| `step()` | O(1) | Advance to next key (follows leaf links) |

The linked-leaf chain makes `step()` a simple increment-and-follow-link,
with no tree traversal. This is the key advantage of B+ trees over
binary search trees for ordered iteration.

## Arena Allocation

All nodes live in a single `Vec<BPlusNode>`. Node indices are `u32`
values into this arena. Allocation is append-only (`push` to the
arena), and there is no free-list or deallocation — the tree grows
monotonically. This is appropriate for use cases where the tree is
built, queried, and then discarded (or rebuilt from scratch).

## Design Tradeoffs

- **`u32` keys only.** The current implementation is specialized for
  `u32` keys. Generalizing to arbitrary `DenseId` types would require
  parameterizing the node layout.

- **No deletion.** The tree supports insert and query but not removal.
  For use cases that need removal, the `SparseSet` (Chapter 6) is a
  better fit.

## Semi-Persistence

The B+ tree is backed by a `VecI<BPlusNode, u32, TRACK>` arena,
making it fully semi-persistent via the same mark/restore protocol
as all other containers in this crate.

```rust
pub struct BPlusTreeSet<const TRACK: bool = true> {
    nodes: VecI<BPlusNode, u32, TRACK>,
    root: u32,
    last_leaf: u32,
    len: usize,
}
```

`mark()` snapshots the arena (via `VecI::mark`) and saves the scalar
fields (`root`, `last_leaf`, `len`) into a `BPlusToken`. `restore()`
replays the arena's diff log in reverse and restores the scalars.

This means inserts — including node splits and pointer rewrites — are
fully reversible. New nodes allocated after the mark are reclaimed by
truncation; modifications to existing nodes (key shifts, child pointer
updates during splits) are undone by the diff log.

### The Capture Tag Bit

`VecI` requires its element type to implement `Tagged` so it can
track which slots have been captured (logged to the diff stack) since
the last mark. For `DenseId` types this is the MSB, but `BPlusNode`
is a 64-byte struct, not an integer.

The solution: steal bit 14 of the `len_flags` field.

```
len_flags (u16):
  bits 0-3:   count (max 14 for leaves, max 7 for internal)
  bit 14:     capture tag (used by VecI for semi-persistence)
  bit 15:     is_leaf flag
  bits 4-13:  unused
```

Count never exceeds 14, so only 4 bits are needed. Bit 15 is the
leaf/internal discriminant. Bit 14 is free in both node types and
serves as the zero-overhead capture flag — no extra memory per node.

The `Tagged` impl for `BPlusNode`:
- `tag()`: reads bit 14
- `set_tag()`: sets bit 14
- `clear_tag()`: clears bit 14
- `from_repr()`: strips bit 14 (and only bit 14 — the leaf flag and
  count are preserved)

This gives the B+ tree the same zero-overhead semi-persistence as
the flat vectors: the capture tracking is packed into existing padding
bits of each 64-byte cache-aligned node.

### Compile-Time Elision

Like all containers, `BPlusTreeSet` is parameterized by
`const TRACK: bool`. When `TRACK = false`, the `VecI` backend
eliminates all capture tracking at compile time, and `mark()`/
`restore()` become no-ops. This is useful when the tree is built
once and never backtracked.

---
[← Ch 6: SparseSet](06-sparse-set.md) · [Ch 8: Benchmark Analysis →](08-bplus-benchmark-analysis.md) · [Table of Contents](00-table-of-contents.md)
