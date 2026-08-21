# Chapter 5: `ListArena`, Intrusive Linked Lists

[← Ch 4: Map](04-map.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: SparseSet →](06-sparse-set.md)

An arena of singly-linked list nodes, supporting amortized O(1) prepend,
append, and splice. The pointer work is constant; allocation and tracked
first-write capture can grow backing vectors.

```rust
pub struct ListArena<T: Tagged, L: DenseId, N: DenseId, const TRACK: bool> {
    heads: VecI<ListHead<N>, L::Index, TRACK>,
    nodes: VecI<ListNode<T, N>, N::Index, TRACK>,
}
```

`ListHead<N>` caches an optional head, a tail, and a count. The optional head's
tag encodes an empty list; the header's tail field supplies the separate
capture tag used by `VecI`. `ListNode<T, N>` stores a payload plus an optional
next pointer, whose tag encodes the end of the list; the payload representation
supplies that node's capture tag.

| Operation | Cost |
|-----------|------|
| `new_list()` → `L` | amortized O(1): append one header and return its typed list id |
| `prepend(head, val)` | amortized O(1): allocate one node, link to old head |
| `append(head, val)` | amortized O(1): allocate one node, use cached tail |
| `splice(dst, src)` | amortized O(1): constant pointer/header writes; tracked capture may grow diff logs |
| `iter(head)` | O(n): follow next pointers |

Both the header and node arenas are semi-persistent vectors. On restore, lists
and nodes allocated after the mark are reclaimed by truncation, while header
and node changes (including cached tails/counts and splice links) are undone
through their diff logs. Useful for adjacency lists, dependency tracking, or
any scenario requiring arena-allocated linked lists with backtracking.

---
[← Ch 4: Map](04-map.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: SparseSet →](06-sparse-set.md)
