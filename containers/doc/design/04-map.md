# Chapter 4: `Map`

[← Ch 3: AppendOnlyVec](03-append-only-vec.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: ListArena →](05-list-arena.md)

A semi-persistent hash map.

Internally composed of:
- `AppendOnlyVec<(K, V)>` for entry storage (append-only, ids are stable)
- `HashMap<K, Id>` for expected O(1) lookup by key

```rust
insert(key, val) → Id    // append entry, insert into index
get_by_key(key) → Option<&V>
id_of(key) → Option<Id>
```

Stored entries have no mutable accessor. An update is another `insert`, which
appends a shadow entry so restore can recover the previous value by truncation.

On `restore()`: the `AppendOnlyVec` truncates, then `rebuild_index()`
reconstructs the `HashMap` by scanning surviving entries. This is O(n)
in the number of surviving log entries. The structure is intended for
registries, symbol tables, or configuration stores where that rebuild cost is
acceptable.

---
[← Ch 3: AppendOnlyVec](03-append-only-vec.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: ListArena →](05-list-arena.md)
