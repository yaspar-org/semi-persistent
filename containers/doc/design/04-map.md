# Chapter 4 — `Map`

[← Ch 3: AppendOnlyVec](03-append-only-vec.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: ListArena →](05-list-arena.md)

A semi-persistent hash map.

Internally composed of:
- `AppendOnlyVec<(K, V)>` for entry storage (append-only, ids are stable)
- `HashMap<K, Id>` for O(1) lookup by key

```rust
insert(key, val) → Id    // append entry, insert into index
get_by_key(key) → Option<&V>
id_of(key) → Option<Id>
```

On `restore()`: the `AppendOnlyVec` truncates, then `rebuild_index()`
reconstructs the `HashMap` by scanning surviving entries. This is O(n)
in the number of entries, but maps are typically small (tens to
hundreds of entries). Useful for small registries, symbol tables, or
configuration stores that need backtracking support.

---
[← Ch 3: AppendOnlyVec](03-append-only-vec.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: ListArena →](05-list-arena.md)
