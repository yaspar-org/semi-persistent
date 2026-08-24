# Chapter 3: `AppendOnlyVec`

[← Ch 2: Semi-Persistent Vectors](02-semi-persistent-vectors.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Map →](04-map.md)

An append-only vector: supports `push` and immutable `get`, but not mutable
access, `set`, or `pop`. Since elements are never modified in place, the
snapshot stack only needs to track lengths, with no per-element diff log or
capture.

```
mark():  save len
restore(): truncate to saved len
```

With `ShrinkPolicy::IfOverallocated { factor, headroom }`, mark shrinks only
when `capacity > len * factor + headroom`, and requests capacity
`len + headroom`. This differs from the general semi-persistent vector's
multiplicative target because append-only storage does not retain a diff log.

The append-only vector is useful for interned or append-only data such
as string pools, symbol tables, or arena-allocated nodes.

---
[← Ch 2: Semi-Persistent Vectors](02-semi-persistent-vectors.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Map →](04-map.md)
