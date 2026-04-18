# Chapter 5 — The E-Graph

[← Ch 4: Canonization](04-canonization.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: Index Construction →](06-index.md)


## Composition

The e-graph is not a monolithic structure; it is a composition of the
primitives from Chapters 1–4. `NodeStore` handles hash-consed term
storage, `EClasses` handles equivalence tracking with parent use-lists,
and the registries handle sort and operator metadata. All are
semi-persistent.

The e-graph's state is partitioned into two categories:

The e-graph's source of truth consists of the union-find arrays,
e-class entries and representative sparse set, node vectors and
children pools (one cache per kind), the routing table, use-lists,
literal value store, and operator/sort registries. All of these are
semi-persistent and rolled back on backtrack. The derived structures
(per-cache HashMap indices and the four sorted index families) are
ephemeral, rebuilt from the semi-persistent source of truth after each
restore invocation.

Derived structures do not need to be semi-persistent because they can
be reconstructed from the source of truth. Keeping them ephemeral avoids
the overhead of diff tracking on high-churn index structures.

## Structure

The e-graph struct bundles the source-of-truth containers together
with two scratch buffers used by rebuild. `nodes` is the hash-consed
node store (Chapter 1). `classes` is the union-find and use-list
structure (Chapter 2). `lits` and `ops`/`sorts` hold the literal
value store and the operator and sort registries. The `worklist`
collects pending merges produced by `merge()` calls; `collisions`
holds congruence collisions discovered during rebuild. Both are
drained each rebuild cycle.

```rust
pub struct EGraph<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> {
    nodes: NodeStore<..., TRACK, PROOFS>,
    classes: EClasses<Cfg::G, Cfg::UL, Cfg::UN, TRACK, PROOFS>,
    lits: LitValStore<L, Cfg::V, TRACK>,
    ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    sorts: SortRegistry<Cfg::S, TRACK>,
    worklist: Vec<(Cfg::UL, Cfg::G)>,
    collisions: Vec<(Cfg::G, Cfg::G)>,
}
```

## Core Operations

### `add(op, children) → G`

1. Look up `op` → `OpInfo` (kind, arity, sorts).
2. Canonize children via `find()` (path-compressing).
3. Dispatch to `NodeStore::add()` → probe cache, insert if fresh.
4. If fresh: create singleton e-class via `classes.add_singleton()`,
   add the new node to the use-lists of each child class.
5. Return the global id (existing or new).

### `add_lit(op, lit_val_id) → G`

`add_lit(op, lit_val_id)` follows the same flow but for literal
nodes, with no children to canonize and no use-list entries to create.

### `merge(a, b) → Option<(G, G)>`

1. `classes.merge(find(a), find(b))` → `MergeInfo`.
2. Push `(absorbed_uses, survivor)` onto worklist.
3. Return the merged pair.

Does NOT trigger rebuild; it happens lazily at the start of each
saturation iteration or explicitly via `rebuild()`.

### `find(x) → G` / `find_const(x) → G`

`find` delegates to `classes.uf.find(x)`, path-compressing, O(α(n)).
Used during `add()` to canonize children.

`find_const` is non-mutating (no path compression). Used during
read-only phases: index construction, rebuild's child canonization,
and pattern matching.

## Rebuild Algorithm

Rebuild is worklist-driven: it processes one merge at a time, visiting
only the parents of the absorbed class. This is much cheaper than a
full-scan fixpoint loop.

```
rebuild():
    while worklist is not empty:
        (absorbed_uses, survivor) = worklist.pop()
        collisions.clear()

        // Re-canonize all parents of the absorbed class
        for parent in uses.iter(absorbed_uses):
            nodes.recanonize_node(parent, find_const, &mut collisions)

        // Splice absorbed use-list into survivor's use-list
        classes.splice_uses(survivor_list, absorbed_uses)

        // Process congruence collisions
        for (a, b) in collisions:
            if classes.merge(a, b) is Some(info):
                worklist.push((info.absorbed_uses, info.survivor))
```

The rebuild loop is worklist-driven (only processes parents of merged
classes), cascading (congruence collisions generate new worklist
entries), and guaranteed to terminate (each merge reduces the number
of distinct classes).

## The Key Invariant: All Marked States Are Post-Rebuild States

Every `mark()` on the e-graph triggers a full rebuild before pushing
frames and producing a Token. The resulting checkpoint represents a fully
congruence-closed state: all union-find paths are compressed, all nodes are
canonicalized, all congruence-induced merges have been discovered.

The post-rebuild snapshot invariant drives the architecture.
The states worth preserving are post-rebuild states where the congruence
closure property holds. Intermediate states where nodes may be stale are
never snapshotted.

## Push/Pop

```rust
mark(shrink):
    self.rebuild()                    // ensure clean state
    // mark all sub-containers:
    nodes.mark(), classes.mark(), lits.mark(), ops.mark(), sorts.mark()

restore(token, shrink):
    // restore all sub-containers in reverse order:
    sorts.restore(), ops.restore(), lits.restore(),
    classes.restore(), nodes.restore()
    // HashMap indices are rebuilt by each cache's finish_restore()
```

All sub-containers are semi-persistent. A single `mark()`/`restore()`
pair snapshots and restores the entire e-graph state.

## Registries

`OpRegistry` and `SortRegistry` are semi-persistent maps (`semi_persistent::containers::Map` from the `semi-persistent-containers` crate)
that live inside the e-graph. They are populated during sortcheck
(Phase 2 of the pipeline) and snapshotted/restored with push/pop.

`OpRegistry` stores per-operator metadata:

```rust
pub struct OpInfo<S> {
    pub name: String,
    pub kind: OpKind<S>,
    pub arg_sorts: Vec<S>,
    pub return_sort: S,
    pub is_constructor: bool,
}

pub enum OpKind<S> {
    Plain, C, A(S, AssocDir), AC, ACI, Lit,
}

pub enum AssocDir { Left, Right, Both }
```

`AssocDir` controls how associative operators are flattened and
matched:

| Direction | Meaning | Example |
|-----------|---------|---------|
| `Left` | Left-associative: `(f (f a b) c)` | subtraction |
| `Right` | Right-associative: `(f a (f b c))` | cons |
| `Both` | Fully associative: any nesting | concatenation |

`A(S, AssocDir)` also carries the element sort `S` for sort-checking
variadic children.

`Lit` kind is for `@`-prefixed auto-generated literal operators.
`is_constructor` marks datatype constructors (tracked on `OpInfo`).

---
[← Ch 4: Canonization](04-canonization.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: Index Construction →](06-index.md)
