# Chapter 1 — Node Representation and Storage

[← Table of Contents](00-table-of-contents.md) · [Ch 2: E-Classes and Union-Find →](02-classes-and-union-find.md)

> **Prerequisites:** This document assumes familiarity with the container
> types from the `semi-persistent-containers` crate (package `semi-persistent-containers-verus`, imported as
> `semi_persistent_containers` and re-exported as `crate::containers`), in
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

| Arity | Tested size (31-bit ids) | Used by |
|-------|-------------------|---------|
| 0 | 12 bytes | Constants, nullary functions |
| 1 | 16 bytes | Unary ops (Neg, Not) |
| 2 | 20 bytes | Binary ops (Add, Mul), commutative ops |
| 3 | 24 bytes | Ternary ops (ITE) |

These sizes include the current `flags: u8` field and alignment padding and
are pinned by `node_types::tests::fixed_arity_sizes`; they are not portable
claims for other id widths or ABIs.

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

Children are stored in the owning cache's shared semi-persistent pool. The
node stores a `(start, end)` span as two `usize` values; its tested size with
31-bit ids on the supported 64-bit target is 32 bytes. The pool element type
`C` depends on the operator kind:

| Kind | Pool element `C` | Invariant |
|------|-----------------|-----------|
| PlainN, A | `G` | Ordered sequence |
| AC | `(G, Multiplicity)` | Sorted by id, multiplicities summed |
| ACI | `G` | Sorted, deduplicated |

### `LitNode<G, O, V>`

For `@`-prefixed literal operators (`@IBig`, `@bool`, etc.).

```
┌──────────┬───────────┬───────┬────────────┐
│ global_id│    op     │ flags │    lit     │
│   (G)    │   (O)     │  (u8) │    (V)     │
└──────────┴───────────┴───────┴────────────┘
```

No e-node children. The `lit` field (a `LitValId` in the 31-bit configurations)
references an interned value in
`LitValStore`. Literal nodes never need re-canonization during rebuild. Their
tested size with 31-bit ids is 16 bytes.

## Stolen Bits Convention

All node structs follow the same field order and bit-stealing convention:

1. `global_id: G`: MSB stolen for the `Tagged` impl. Under the `HotFirst` store policy
   this is the `InlineStore` capture flag of the node column (see
   `semi_persistent_containers::Tagged`); under `TrailFirst` the `TrailStore` keeps no
   runtime capture flag, and the bit stays clear. `from_repr` clears this bit, so
   callers always see clean ids.

2. `op: O`: MSB stolen for the history flag (proof support).
   Set on first re-canonization when `PROOFS = true`. Before setting,
   the node's original children are saved to a history store, enabling
   the proof system to reconstruct the pre-merge state (Chapter 14).

Both bits are invisible to `content_hash` and `content_eq`, which
operate on clean values.

`node_types.rs` also defines `FLAG_CONSTRUCTOR: u8 = 1 << 1`. Constructor
status enters through registration metadata and is stamped onto each node when
the node is created. Nothing in `egraph/src` reads it back: congruence, matching,
and extraction do not branch on it.

## `TypedRouting` — Global Dispatch Table

Every e-node gets a globally unique `ENodeId`. But nodes live in
different caches with different local id types. The routing table
bridges the two:

```rust
pub struct TypedRouting<G, I: NodeIds, const TRACK: bool = true> {
    entries: AppendOnlyVec<NodeRef<I>, I::Index, TRACK>, // indexed by G
    reserved: bool,                                      // one outstanding reservation
    _g: PhantomData<G>,
}

pub enum NodeRef<I: NodeIds> {
    Plain0(I::L0), Plain1(I::L1), Plain2(I::L2), Plain3(I::L3),
    SPair(I::LSPair), PlainN(I::LN), Seq(I::LSeq),
    MSet(I::LMSet), Set(I::LSet), Lit(I::LLit),
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

1. `reserve()` → `ENodeId`: returns the next global id, `entries.len()`, and sets
   the `reserved` flag; it writes no slot, and it panics if a reservation is already
   outstanding or the id space is exhausted.
2. Probe the cache: if a node with the same content exists, call
   `unreserve()` and return the existing id.
3. Otherwise, insert the node into the cache, then `finalize(eid,
   node_ref)` to push the `NodeRef`, asserting that `eid` is `entries.len()`.

## `NodeStore` — Unified Facade

```rust
pub struct NodeStore<G, O, V, C, I: NodeIds, const TRACK: bool, const PROOFS: bool = false,
                     P = HotFirst> where P: CacheFamilies<G, O, V, C, I, TRACK> {
    routing: TypedRouting<G, I, TRACK>,     // every cache below also takes P
    plain0: FixedArityCache<..., 0, TRACK, PROOFS>,
    plain1: FixedArityCache<..., 1, TRACK, PROOFS>,
    plain2: FixedArityCache<..., 2, TRACK, PROOFS>,
    plain3: FixedArityCache<..., 3, TRACK, PROOFS>,
    spair:  FixedArityCache<..., 2, TRACK, PROOFS>,  // commutative pair
    plain_n: VariableArityCache<..., TRACK, PROOFS>,
    seq:     VariableArityCache<..., TRACK, PROOFS>,
    mset:    VariableArityCache<..., TRACK, PROOFS>,
    set:     VariableArityCache<..., TRACK, PROOFS>,
    lit:     LitCache<..., TRACK>,  // no PROOFS — lit nodes have no children
}
```

Note that `LitCache` lacks the `PROOFS` parameter: literal nodes have
no e-node children, so there is no history bit to manage and no
re-canonization to perform.

### `add(op, children, ops, flags)` → `Added<G>`

`Added` is `Existing(G) | Fresh(G)`, with the accessors `id()` and `is_fresh()`.

1. Look up `op` → `OpKind` from the registry.
2. Dispatch to the appropriate cache based on kind and arity.
3. Canonize children: only a commutative pair is ordered here. `MSet`, `Set`, and `Lit`
   panic in `add`; their callers use `add_mset`, `add_set`, and `add_lit`, with children
   already canonized by `EGraph::add` (`nary_canon`).
4. Reserve a global id, then probe the cache (`probe_or_insert`): if a node with the
   same `(op, canonical_children)` exists, unreserve and return `Existing(id)`.
5. Otherwise the node is inserted; finalize the routing entry and return `Fresh(id)`.

### `recanonize_node(id, find, unit_of, g_buf, mset_buf, collisions, touched, ops)` → `Normal<G>`

During rebuild, after a merge changes canonical representatives:

1. Read the node's children.
2. Apply `find()` to each child to get current canonical ids.
3. If children changed: re-canonize (sort for C, merge mults for AC,
   dedup for ACI), re-probe the cache.
4. If the re-probe finds a *different* existing node with the same
   canonical children: congruence collision. Report `(id, existing)`
   to the collision list for the rebuild worklist, and flag the node
   `FLAG_CONGRUENT_DUP`.
5. A changed node is pushed onto `touched`. Under AC and ACI the unit class is dropped
   and the clamp applied; a result that is the unit or a single class (`Normal::Unit`,
   `Normal::Single`) becomes a merge in rebuild.

## `EGraphConfig` — Type Bundle

```rust
pub trait EGraphConfig: 'static {
    type Index: IndexLike + Tagged + Send;
    type G: DenseId<Index = Self::Index> + Hash + Send;
    type ClassKey: DenseId<Index = Self::Index> + Send;
    type O: DenseId + Hash + Send;
    type S: DenseId + Send;
    type V: DenseId<Index = Self::Index> + Hash + Send;
    type UL: DenseId<Index = Self::Index> + Send;
    type UN: DenseId<Index = Self::Index> + Send;
    type C: Tagged + Clone + Copy + Hash + Eq + Debug + Send;
    type M: MultiplicityLike;
    type Ids: NodeIds<Index = Self::Index> + Send;
    type Au: AuIds<Index = Self::Index>;
    type Policy: 'static;

    // Required methods for generic AC child manipulation:
    fn mset_child_id(c: &Self::C) -> Self::G;
    fn mset_child_mult(c: &Self::C) -> Self::M;
    fn mset_child_single(g: Self::G) -> Self::C { /* with_mult(g, ONE) */ }
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C;
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool;
}
```

The five `mset_child_*` methods allow the e-graph to manipulate MSet
children generically without knowing the concrete `(G, Multiplicity)`
layout. `mset_child_merge` increments the multiplicity of an existing
child and returns `true` if the ids belong to the same group.

`DefaultConfig` uses 31-bit capacity-coupled ids and a 32-bit
multiplicity. `Config64` uses 63-bit capacity-coupled ids and a 64-bit multiplicity.
These two are what `--bits 32|64` selects, and every operation on a count in either is
checked: a result past the width is reported as `multiplicity overflow: …`, naming the
width and its maximum. An unbounded width (`BigMult`, one word, interned above 2^63) was
built and then removed (user, 2026-10-06): the stored child sits in the verified
containers, whose elements must be `Copy`, and an unbounded `Copy` count in one word needs
a reserved bit and a table that is never freed. `ConfigM16` keeps the 31-bit ids and
narrows multiplicity to 16 bits, for tests only. Operator and sort ids are not capacity-coupled: their count is the
program's declarations, so every configuration but `Smt64` uses the 31-bit `OpId` and `SortId`.

### Widths are configuration parameters

Every width in the e-graph is a parameter of `EGraphConfig`: no engine code names a concrete
id or count type. The parameters are:

- the id families over one `Index` word (`u32` or `u64`): `G` (node ids, which also name
  classes), `ClassKey`, `UL` and `UN` (use lists), `V` (literal values), and the local ids
  bundled in `Ids` and `Au`;
- `O` and `S`, operator and sort ids, which are not tied to `Index`;
- `M`, the multiplicity of an AC child, and `C`, the stored `(G, M)` pair;
- `Policy`, the store family of every tracked column: `HotFirst` deduplicates on first
  capture, `TrailFirst` appends every write (containers-verus chapters 17 and 18, and
  Chapter 4 here).

The shipped presets (`nodes.rs`) differ only in these parameters:

| Preset | Ids | `O`, `S` | `M` | `Policy` | Selected by |
|---|---|---|---|---|---|
| `DefaultConfig` (`EqSat32`, `EGraph31`) | 31-bit | 31-bit | `Multiplicity` (u32) | `HotFirst` | `--bits 32`, the default |
| `Config64` (`EqSat64`, `EGraph63`) | 63-bit | 31-bit | `Multiplicity64` | `HotFirst` | `--bits 64` |
| `Smt32` | 31-bit | 31-bit | `Multiplicity` (u32) | `TrailFirst` | `satcore`'s `Euf31` |
| `Smt64` | 63-bit | 63-bit (`OpId64`, `SortId64`) | `Multiplicity64` | `TrailFirst` | `satcore`'s `Euf63` |
| `ConfigM16` | 31-bit | 31-bit | `Multiplicity16` | `HotFirst` | tests |

A narrower width is safe only because every value that crosses into it is checked:

- an id past its range is refused (`guard::refuse`, "exceeds range"), never wrapped;
- the surface reads a count as a `u64` (a count past 2^64 is a parse error that names the
  multiplicity), and its narrowing to `M` is checked, as are the sums and products on counts
  (`MultOverflow`, `take_width_error`, `CompletionOutcome::AbortedOverflow`; chapter 5);
- the anti-unification solver keeps counts as `u64` and refuses a wider one (`CountTooWide`).

`tests/multiplicity_width.rs` and `tests/config_matrix.rs` run these boundaries under each
built width, and `tests/au_config64.rs` and `tests/au_id_width.rs` the anti-unification
id families. The cost width of extraction (`--cost-bits 32|64|big`) is not part of
`EGraphConfig`: it belongs to the extraction backend (Chapter 11).

---
[← Table of Contents](00-table-of-contents.md) · [Ch 2: E-Classes and Union-Find →](02-classes-and-union-find.md)
