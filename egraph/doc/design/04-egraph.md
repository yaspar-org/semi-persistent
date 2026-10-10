# Chapter 4 — The E-Graph

[← Ch 3: Hash-Consing Caches](03-hash-consing-caches.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: Algebraic Operators →](05-algebraic-operators.md)

## Composition

The e-graph is not a monolithic structure; it is a composition of the
primitives from Chapters 1–3 and §5.2. `NodeStore` handles hash-consed term
storage, `EClasses` handles equivalence tracking with parent use-lists,
and the registries handle sort and operator metadata. All are
semi-persistent.

The e-graph's state is partitioned into two categories:

The e-graph's source of truth consists of the union-find arrays,
e-class entries and representative sparse set, node vectors and
children pools (one cache per kind), the routing table, use-lists,
literal value store, registries, and the unit/inverse maps. These are
semi-persistent and rolled back on backtrack. Each node cache also has a
transient hint index from content fingerprints to local ids. A restore does no
work on it: probes validate every hint against the restored node arena (Chapter 3).

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
    classes: EClasses<Cfg::G, Cfg::ClassKey, Cfg::UL, Cfg::UN, TRACK, PROOFS, Cfg::Policy>,
    nodes: NodeStore<..., TRACK, PROOFS, Cfg::Policy>,
    history: crate::containers::history::History,
    worklist: Vec<(Cfg::UL, Cfg::G)>,
    collisions: Vec<(Cfg::G, Cfg::G)>,
    // Reusable scratch, semi-naive touched state, completion
    // configuration/outcome, and persistent unit/inverse maps follow.
}
```

## Core Operations

### `add(op, children) → G`

1. Look up `op` → `OpInfo` (kind, arity, sorts).
2. Canonize children via `find()` (path-halving), then apply the
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

1. `merge_in_classes(a, b)`: return `None` if `find_const(a) == find_const(b)`;
   otherwise choose the survivor by the `--union-by` policy and call `classes.merge`
   (or a directed or justified variant) → `MergeInfo`.
2. Fold the absorbed class's min-monomial row into the survivor's (`fold_min_monomial`).
3. Push `(absorbed_uses, survivor)` onto worklist.
4. Return the merged pair.

Does NOT trigger rebuild; it happens lazily at the start of each
saturation iteration or explicitly via `rebuild()`.

### `find(x) → G` / `find_const(x) → G`

`find` delegates to `classes.uf.find(x)` and applies path halving. With the default
rank survivor policy it has the standard O(α(n)) amortized bound. Directed
`size`/`uses`/`sum` policies do not preserve rank-balanced linking, so that
complexity claim does not apply to them. It is used during `add()` to canonize
children.

`find_const` is non-mutating (no path halving). Used during
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
            normal = nodes.recanonize_node(parent, find_const, unit_of, .., &mut collisions)
            if normal names an existing class (Unit or Single):
                collisions.push((parent, that class))

        // Splice absorbed use-list into survivor's use-list
        classes.splice_uses(survivor_list, absorbed_uses)
        // a merge into an op's unit class re-sweeps the whole survivor list

        // Process congruence collisions
        for (a, b) in collisions:
            if merge_in_classes(a, b) is Some(info):   // Congruence justification under PROOFS
                fold_min_monomial(info.survivor, ..)
                worklist.push((info.absorbed_uses, info.survivor))
```

The rebuild loop is worklist-driven (only processes parents of merged
classes), cascading (congruence collisions generate new worklist
entries), and guaranteed to terminate (each merge reduces the number
of distinct classes).

The pseudo-code above is the plain-congruence pass. With completion off, `rebuild`
alternates it with `canon_repair_round`, the inverse-pair cancellation repair, until
neither changes anything. Under a completion
mode (`--derive-ac-eqs`, or inside a lazy check's transaction), `rebuild`
interleaves that pass with AC completion rounds and the A-only
inter-reduction round to a joint fixpoint, polls the completion goal pair
between passes and inside a round's apply loops, and stops a blown-up
round at the node-growth budget mid-apply. The completion algorithm, the
goal-directed early stop, and the budget are specified in
[Chapter 6](06-ac-congruence-closure.md) §8, §13
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
    self.rebuild()                       // ensure clean state
    // one stamp for the whole member set, one frame pushed on each member:
    let members = EGraphMembers { nodes, classes, lits, ops, sorts,
                                  rules, axioms, unit_node, inverse_op, par }
    let group = self.history.mark_member(&mut members, shrink)
        .expect(..)                      // a refusal panics before anything moved
    EGraphToken { group, completion_outcome: self.completion_outcome }

restore(token):
    // one validity question, asked of the history; refuses without moving
    // anything if the token is foreign, cut or popped, or if a member drifted
    self.history.restore_member(&mut members, token.group)   // asserted: a refusal panics
    self.completion_outcome = token.completion_outcome
    clear worklist, collisions, and touched log
```

The e-graph owns one `History` (containers' `history` module; the member methods are in
`group`) and its nine
synchronized members carry no tokens: `EGraphMembers` is a borrowed forwarding
view implementing `Member`. `restore`, `restore_and_pop`, and `pop_scope` fan the
structural operation of its seven wide members out over a `rayon::scope` on disjoint
`&mut` borrows at or above `PAR_NODE_MIN` (2^14) live nodes (the `SEMPER_PAR` variable
forces it on or off); `unit_node` and `inverse_op` run after them. `mark` always runs
sequentially.
Before 2026-09-18 each member kept its own depth-indexed token stack — nine of
them, plus the choreography to push and truncate them together — and a mark
minted one token per column. Now a scope costs one stamp, and `restore_with`,
`restore_and_pop_with` and `pop_scope` are each one call into the history plus
the e-graph's own bookkeeping. The measured effect: an empty-store push/pop trace
dropped to 0.79–0.80× of the token-era cost, other store traces 0.97–1.00×, and
saturation at parity.

All source-of-truth sub-containers participate in the semi-persistent
protocol. A cache restore does no work on its hint index; probes revalidate the hints
against the restored arena. Matching indexes have round lifetime and are built later by the
saturation driver. One coordinated `mark()`/`restore()` pair therefore
restores the logical e-graph state without making every acceleration structure
semi-persistent.

### Store policy: Hot-first and Trail-first

The members' tracked columns are stores of the configuration's `Policy` (Chapter 1).
`HotFirst`, used by `DefaultConfig`, `Config64`, and `ConfigM16`, saves a slot's old value
once per frame, at its first write, at the cost of a lookup per write. `TrailFirst`, used by
`Smt32` and `Smt64`, appends every write without a lookup and keeps the duplicates until
rollover deduplicates them. The mark and restore protocol above is the same under both;
only the cost of a write and of a restore differs. Equality saturation writes the same
slots many times between two marks, so deduplicating at first capture keeps one saved word
per touched slot per frame. An SMT search marks and backtracks at every decision level and
writes few slots per level, so the append-only write is the cheaper one.

The three representations a frame passes through (Trail, Hot, Cold), when a mark converts
one into the next, and how a restore replays each are documented in the containers crate:
`containers-verus/doc/design/17-three-tier-frame-grid.md` (§4, §5, and §9, "Rollover"),
`18-store-policy.md` for the two policies, and `09-diff-stack-compression.md` for the Cold
encoding.

## Registries

`SortRegistry`, `OpRegistry`, `RuleRegistry`, and `AxiomRegistry` are each backed by an
`SpUniqueMap` from the `semi-persistent-containers` crate, whose log positions are the
ids; `OpRegistry` also keeps one `AppendOnlyVec` entry of completion bookkeeping per
operator. They live inside the e-graph. They are populated during sortcheck
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

`AssocDir` controls how nested applications are folded into the
order-preserving sequence representation:

| Direction | Surface tag | Construction normal form |
|-----------|-------------|--------------------------|
| `Left` | `:assoc-left` | flatten the first-child spine |
| `Right` | `:assoc-right` | flatten the last-child spine |
| `Both` | `:assoc` | flatten every nested same-op child |

The distinction is semantic for non-associative folds: with `Left`,
`f(f(a,b),c)` has the flat form `f(a,b,c)`, but `f(a,f(b,c))` retains its
grouped right child. Both checked ground terms and rewrite RHS terms pass
through the same `EGraph::add` canonization.

`A { arg_sort, dir }` also carries the element sort for sort-checking
variadic children.

`Lit` kind is for `@`-prefixed auto-generated literal operators.
`OpInfo` separately stores constructor, extraction cost, and
unextractability metadata. Resolved inverse operators and built identity nodes
live in persistent maps on `EGraph`, because `OpKind<S>` cannot carry the
configured operator/node id types.

---
[← Ch 3: Hash-Consing Caches](03-hash-consing-caches.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: Algebraic Operators →](05-algebraic-operators.md)
