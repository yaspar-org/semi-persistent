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
literal value store, registries, and the unit/inverse maps. These are
semi-persistent and rolled back on backtrack. Each node cache also has a
transient hash-cons map. Cache restore repairs that map incrementally when the
saved change set is small and otherwise rebuilds it from the restored node
arena.

The four sorted matching-index families are separate transient
`IndexStore`s. The saturation driver builds them after e-graph rebuild, once
per matching round; they are not fields restored by `EGraph::restore`.
Keeping these acceleration structures transient avoids diff capture on their
high-churn contents.

## Structure

The e-graph struct bundles the source-of-truth containers together
with reusable buffers and completion state. `nodes` is the hash-consed
node store (Chapter 1). `classes` is the union-find and use-list
structure (Chapter 2). `lits` and `ops`/`sorts` hold the literal
value store and the operator and sort registries. The `worklist`
collects pending merges produced by `merge()` calls; `collisions`
holds congruence collisions discovered during rebuild. Both are
drained each rebuild cycle.

```rust
pub struct EGraph<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> {
    sorts: SortRegistry<Cfg::S, TRACK>,
    ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    rules: RuleRegistry<TRACK>,
    axioms: AxiomRegistry<Cfg::G, TRACK>,
    lits: LitValStore<L, Cfg::V, TRACK>,
    classes: EClasses<Cfg::G, Cfg::UL, Cfg::UN, TRACK, PROOFS>,
    nodes: NodeStore<..., TRACK, PROOFS>,
    worklist: Vec<(Cfg::UL, Cfg::G)>,
    collisions: Vec<(Cfg::G, Cfg::G)>,
    // Reusable scratch, semi-naive touched state, completion
    // configuration/outcome, and persistent unit/inverse maps follow.
}
```

## Core Operations

### `add(op, children) → G`

1. Look up `op` → `OpInfo` (kind, arity, sorts).
2. Canonize children via `find()` (path-compressing), then apply the
   operator's structural normal form: pair reorder, sequence flattening, or
   multiset/set flattening and count clamp.
3. Resolve associative/AC degenerate arity, or dispatch to the corresponding
   `NodeStore` cache to probe and insert.
4. If fresh: create a singleton e-class via `classes.add_singleton()`,
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

`find` delegates to `classes.uf.find(x)` and path-compresses. With the default
rank survivor policy it has the standard O(α(n)) amortized bound. Directed
`size`/`uses`/`sum` policies do not preserve rank-balanced linking, so that
complexity claim does not apply to them. It is used during `add()` to canonize
children.

`find_const` is non-mutating (no path compression). Used during
read-only phases: index construction, rebuild's child canonization,
and pattern matching. Its rank-policy worst case is O(log n); directed unions
can produce a linear-height tree.

## Rebuild Algorithm

Rebuild is worklist-driven: it processes one merge at a time, visiting
the parents of the absorbed class rather than scanning every node. The
amount saved relative to a full scan depends on use-list sizes and merge
history.

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

The pseudo-code above is the plain-congruence pass. Under a completion
mode (`--derive-ac-eqs`, or inside a lazy check's transaction), `rebuild`
interleaves that pass with AC completion rounds and the A-only
inter-reduction round to a joint fixpoint, polls the completion goal pair
between passes and inside a round's apply loops, and stops a blown-up
round at the node-growth budget mid-apply. The completion algorithm, the
goal-directed early stop, and the budget are specified in
[ac-congruence-completeness.md](ac-congruence-completeness.md) §8, §13
and §14.

## The Key Invariant: All Marked States Are Post-Rebuild States

Every `mark()` on the e-graph triggers a full rebuild before pushing
frames and producing a Token. The resulting checkpoint is always plain
congruence closed: nodes are canonicalized and congruence-induced merges have
been drained. If completion is disabled, goal-stopped, or budget-aborted, that
is the strongest closure claim. If the recorded outcome is
`CompletionOutcome::Converged`, one full round of the implemented completion
passes made no change; this still does not by itself prove the broader
mathematical completeness claims discussed in the AC chapters.

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

restore(token):
    classes.restore(); nodes.restore()
    sorts.restore(); ops.restore(); rules.restore(); axioms.restore()
    lits.restore(); unit_node.restore(); inverse_op.restore()
    completion_outcome = token.completion_outcome
    clear worklist, collisions, and touched log
```

All source-of-truth sub-containers participate in the semi-persistent
protocol. Each cache restore either repairs or reconstructs its transient
hash-cons map. Matching indexes have round lifetime and are built later by the
saturation driver. One coordinated `mark()`/`restore()` pair therefore
restores the logical e-graph state without making every acceleration structure
semi-persistent.

## Registries

`OpRegistry` and `SortRegistry` are semi-persistent maps (`semi_persistent::containers::Map` from the `semi-persistent-containers` crate)
that live inside the e-graph. They are populated during sortcheck
(Phase 2 of the pipeline) and snapshotted/restored with push/pop.

`OpRegistry` stores per-operator metadata:

```rust
pub struct OpInfo<S> {
    pub name: String,
    pub return_sort: S,
    pub kind: OpKind<S>,
    pub is_constructor: bool,
    pub cost: u32,
    pub unextractable: bool,
}

pub enum OpKind<S> {
    Normal { arg_sorts: Vec<S> },
    Commutative { arg_sorts: [S; 2] },
    A { arg_sort: S, dir: AssocDir },
    MSet {
        arg_sort: S, clamp: Clamp,
        identity: Option<UnitRef>, cancellative: bool,
    },
    Set {
        arg_sort: S, clamp: Clamp,
        identity: Option<UnitRef>, cancellative: bool,
    },
    Lit,
}

pub enum AssocDir { Left, Right, Both }
```

`AssocDir` records whether the source used `:assoc-left`, `:assoc-right`, or
`:assoc`. It does not currently select different runtime behavior:
construction flattens every `OpKind::A` to the same order-preserving sequence,
and matching reads that representation uniformly. Code that requires
one-sided/directional semantics must not infer it from this field; implementing
such semantics would require new canonization and matching behavior.

`A { arg_sort, dir }` also carries the element sort for sort-checking
variadic children.

`Lit` kind is for `@`-prefixed auto-generated literal operators.
`OpInfo` separately stores constructor, extraction cost, and
unextractability metadata. Resolved inverse operators and built identity nodes
live in persistent maps on `EGraph`, because `OpKind<S>` cannot carry the
configured operator/node id types.

---
[← Ch 4: Canonization](04-canonization.md) · [Table of Contents](00-table-of-contents.md) · [Ch 6: Index Construction →](06-index.md)
