# Chapter 5 — `ListArena` — Intrusive Linked Lists

[← Ch 4: Map](04-map.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: SparseSet →](06-sparse-set.md)

An arena of singly-linked list nodes, supporting O(1) prepend, append,
and splice.

```rust
pub struct ListArena<T, I, S, const TRACK: bool> {
    nodes: Vec<ListNode<T, I>, I, S, TRACK>,
}
```

`ListHead<I>`: a tagged id. The tag bit encodes "empty list".
`ListNode<T, I>`: value `T` + next pointer (also tagged; the tag on next
encodes "end of list").

| Operation | Cost |
|-----------|------|
| `new_list()` → `ListHead` | O(1) |
| `prepend(head, val)` | O(1) — allocate node, link to old head |
| `append(head, val)` | O(n) — walk to tail, link new node |
| `splice(dst, src)` | O(n) — link src's tail to dst's head |
| `iter(head)` | O(n) — follow next pointers |

Semi-persistent via the underlying `Vec` of nodes. On restore, nodes
allocated after the mark are reclaimed by truncation, and modifications
to existing nodes (e.g. pointer updates from splice/prepend) are undone
via the diff log. Useful for adjacency lists, dependency tracking, or
any scenario requiring arena-allocated linked lists with backtracking.

---
[← Ch 4: Map](04-map.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: SparseSet →](06-sparse-set.md)
