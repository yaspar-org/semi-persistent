# Chapter 1 — Node Representation and Storage

[← Table of Contents](00-table-of-contents.md) · [Ch 2: E-Classes and Union-Find →](02-classes-and-union-find.md)

> **Prerequisites:** This document assumes familiarity with the container
> types from the `semi-persistent-containers` crate (`semi_persistent::containers`), in
> particular `DenseId`, `Tagged`, `VecI`, `SparseSet`, `ListArena`, and
> `Map`. See the `semi-persistent-containers` crate documentation.

## The Problem

An e-graph stores millions of term nodes. Each node is an operator applied
to children: `(Add e3 e7)`, `(Lit 42)`, `(concat e1 e2 e3 e4)`. The
engine must:

1. Hash-cons nodes: two nodes with the same op and canonical children
   must share the same identity.
2. Re-canonize nodes during rebuild: when two classes merge, parent
   nodes must update their children to point to the survivor.
3. Dispatch by operator kind: plain, commutative, associative, AC,
   ACI, and literal nodes all have different canonization rules and
   different memory layouts.

The design partitions nodes by kind into separate typed caches, each with
its own dense local id space. A global routing table maps any `ENodeId` to
the correct cache and local id in O(1).

## Node Types

Three generic structs cover all ten node kinds. Children are stored
inline for small arities (0–3) and in a shared pool for larger
arities, keeping the common case (binary and ternary operators like `ite`)
compact while supporting variadic operators without a separate allocation
per node.

### `FixedArityNode<G, O, const K: usize>`

For operators with 0–3 children (plain and commutative).

```
┌──────────┬───────────┬────────────────────┐
│ global_id│    op     │ children: [G; K]   │
│   (G)    │   (O)     │                    │
└──────────┴───────────┴────────────────────┘
```

| Arity | Size (32-bit ids) | Used by |
|-------|-------------------|---------|
| 0 | 8 bytes | Constants, nullary functions |
| 1 | 12 bytes | Unary ops (Neg, Not) |
| 2 | 16 bytes | Binary ops (Add, Mul), commutative ops |
| 3 | 20 bytes | Ternary ops (ITE) |

### `VariableArityNode<G, O>`

For operators with 4+ children, or associative/AC/ACI operators.

```
┌──────────┬───────────┬───────┬─────┐
│ global_id│    op     │ start │ end │  ← span into shared pool
└──────────┴───────────┴───────┴─────┘
                          │
                          ▼
              pool: [..., c₀, c₁, c₂, c₃, ...]
```

Children are stored in a shared pool (`Vec<C>`). The node stores a
`(start, end)` span. The pool element type `C` depends on the operator
kind:

| Kind | Pool element `C` | Invariant |
|------|-----------------|-----------|
| PlainN, A | `G` | Ordered sequence |
| AC | `(G, Multiplicity)` | Sorted by id, multiplicities summed |
| ACI | `G` | Sorted, deduplicated |

### `LitNode<G, O, V>`

For `@`-prefixed literal operators (`@IBig`, `@bool`, etc.).

```
┌──────────┬───────────┬────────────┐
│ global_id│    op     │ lit_val_id │
│   (G)    │   (O)     │    (V)     │
└──────────┴───────────┴────────────┘
```

No e-node children. The `LitValId` references an interned value in
`LitValStore`. Literal nodes never need re-canonization during rebuild.

## Stolen Bits Convention

All node structs follow the same field order and bit-stealing convention:

1. `global_id: G`: MSB stolen for the `Tagged` impl. This is the
   `semi_persistent::containers::VecI` capture flag (see `semi_persistent::containers::Tagged`). `from_repr` clears this bit, so
   callers always see clean ids.

2. `op: O`: MSB stolen for the history flag (proof support).
   Set on first re-canonization when `PROOFS = true`. Before setting,
   the node's original children are saved to a history store, enabling
   the proof system to reconstruct the pre-merge state (Chapter 15).

Both bits are invisible to `content_hash` and `content_eq`, which
operate on clean values.

> Note: `node_types.rs` also defines `FLAG_CONSTRUCTOR: u8 = 1 << 1`,
> but this per-node flag is currently unused. Constructor status is
> tracked on `OpInfo` in the registry, not on individual nodes.

## `TypedRouting` — Global Dispatch Table

Every e-node gets a globally unique `ENodeId`. But nodes live in
different caches with different local id types. The routing table
bridges the two:

```rust
pub struct TypedRouting<G, I: NodeIds> {
    table: Vec<NodeRef<I>>,   // indexed by G
}

pub enum NodeRef<I: NodeIds> {
    Plain0(I::L0), Plain1(I::L1), Plain2(I::L2), Plain3(I::L3),
    C(I::LC),      PlainN(I::LN), A(I::LA),
    AC(I::LMSet),    ACI(I::LSet),  Lit(I::LLit),
}
```

Each variant carries a typed local id. Pattern matching on `NodeRef`
gives the right type statically, with no raw integer + kind tag and no
runtime reconstruction. This prevents routing errors at compile time:
a `Plain2Id` cannot accidentally index into the AC cache.

### Two-Phase Allocation

Adding a node requires two steps because of a circular dependency:
the hash-consing cache needs the global id to store in the node, but
the node needs to be constructed before it can be inserted.

1. `reserve()` → `ENodeId`: allocates a global id, reserves a slot
   in the routing table (filled with a placeholder).
2. Probe the cache: if a node with the same content exists, call
   `unreserve()` and return the existing id.
3. Otherwise, insert the node into the cache, then `finalize(eid,
   node_ref)` to write the actual `NodeRef` into the reserved slot.

## `NodeStore` — Unified Facade

```rust
pub struct NodeStore<G, O, V, C, I: NodeIds, const TRACK: bool, const PROOFS: bool> {
    routing: TypedRouting<G, I>,
    plain0: FixedArityCache<..., 0, TRACK, PROOFS>,
    plain1: FixedArityCache<..., 1, TRACK, PROOFS>,
    plain2: FixedArityCache<..., 2, TRACK, PROOFS>,
    plain3: FixedArityCache<..., 3, TRACK, PROOFS>,
    c:      FixedArityCache<..., 2, TRACK, PROOFS>,  // commutative (always arity 2)
    plain_n: VariableArityCache<..., TRACK, PROOFS>,
    a:       VariableArityCache<..., TRACK, PROOFS>,
    ac:      VariableArityCache<..., TRACK, PROOFS>,
    aci:     VariableArityCache<..., TRACK, PROOFS>,
    lit:     LitCache<..., TRACK>,  // no PROOFS — lit nodes have no children
}
```

Note that `LitCache` lacks the `PROOFS` parameter: literal nodes have
no e-node children, so there is no history bit to manage and no
re-canonization to perform.

### `add(op, children)` → `Added { id, is_fresh }`

1. Look up `op` → `OpKind` from the registry.
2. Dispatch to the appropriate cache based on kind and arity.
3. Canonize children (sort for C, sort+merge for AC, sort+dedup for ACI).
4. Probe the cache: if a node with the same `(op, canonical_children)`
   exists, return its id with `is_fresh = false`.
5. Otherwise, reserve a global id, insert into the cache, finalize
   the routing entry, return with `is_fresh = true`.

### `recanonize_node(id, find, bufs, collisions)`

During rebuild, after a merge changes canonical representatives:

1. Read the node's children.
2. Apply `find()` to each child to get current canonical ids.
3. If children changed: re-canonize (sort for C, merge mults for AC,
   dedup for ACI), re-probe the cache.
4. If the re-probe finds a *different* existing node with the same
   canonical children: congruence collision. Report `(id, existing)`
   to the collision list for the rebuild worklist.

## `EGraphConfig` — Type Bundle

```rust
pub trait EGraphConfig: 'static {
    type G: DenseId + Hash;     // global e-node id
    type O: DenseId + Hash;     // operator id
    type S: DenseId;            // sort id
    type V: DenseId + Hash;     // literal value id
    type UL: DenseId;           // use-list id
    type UN: DenseId;           // use-list node id
    type C: Tagged + Copy + Hash + Eq;  // AC child (id, mult)
    type M: Copy + Eq + Ord + Hash + From<u32> + Into<u32>;  // multiplicity
    type Ids: NodeIds;          // local id bundle for typed caches

    // Required methods for generic AC child manipulation:
    fn mset_child_id(c: &Self::C) -> Self::G;
    fn mset_child_mult(c: &Self::C) -> Self::M;
    fn mset_child_single(g: Self::G) -> Self::C;
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C;
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool;
}
```

The five `mset_child_*` methods allow the e-graph to manipulate MSet
children generically without knowing the concrete `(G, Multiplicity)`
layout. `mset_child_merge` increments the multiplicity of an existing
child and returns `true` if the ids belong to the same group.

`DefaultConfig` uses 31-bit ids for everything. `Config64` uses
63-bit `ENodeId` for e-graphs exceeding 2 billion nodes.

---
[← Table of Contents](00-table-of-contents.md) · [Ch 2: E-Classes and Union-Find →](02-classes-and-union-find.md)
