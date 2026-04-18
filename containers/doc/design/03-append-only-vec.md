# Chapter 3 — `AppendOnlyVec`

[← Ch 2: Semi-Persistent Vectors](02-semi-persistent-vectors.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Map →](04-map.md)

An append-only vector: supports `push` and `get`, but not `set` or
`pop`. Since elements are never modified in place, the diff log only
needs to track the length, with no per-element capture.

```
mark():  save len
restore(): truncate to saved len
```

The append-only vector is useful for interned or append-only data such
as string pools, symbol tables, or arena-allocated nodes.

---
[← Ch 2: Semi-Persistent Vectors](02-semi-persistent-vectors.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Map →](04-map.md)
