# E-nodes, e-classes, congruence

This chapter defines e-nodes and e-classes, measures structural sharing, and
explains union-find, congruence closure, rebuild, and equality checks.

## E-nodes and e-classes

An **e-node** is an operator together with references to its argument
e-classes. An **e-class** is a set of e-nodes that Semper currently knows to
be equal.

```lisp
{{#include ../examples/06-congruence.egg:enodes-and-eclasses}}
```

The `print-size` command reports:

```text
a: 1
b: 1
f: 1
total: 3
```

The term contributes three e-nodes: `a()`, `b()`, and `f(Ca, Cb)`, where `Ca`
and `Cb` are the classes containing the two leaves. All three nodes are new in
this example and initially belong to separate e-classes.

The parent stores class arguments, not pointers to fixed syntax-tree children.
Once a child class acquires additional members, the same parent e-node
represents applications using any equal member of that child class. After
insertion, `left` names an e-class rather than one retained syntax tree.

The node arena and the e-class relation are separate structures. Adding a new
e-node creates a singleton e-class. Later equalities can merge classes without
deleting their member nodes. This is why `print-size` counts nodes rather than
equivalence classes.

## Hash-consing

At insertion time, hash-consing maps an operator and canonical argument tuple
to an existing e-node's class. Inserting the same key again therefore reuses
that class instead of allocating another node.

```lisp
{{#include ../examples/06-congruence.egg:hash-consing}}
```

The second `print-size` has the same output as the first:

```text
a: 1
b: 1
f: 1
total: 3
```

Reinserting `(f (a) (b))` reuses both leaves and their parent, so the measured
node total remains three. The identity test uses e-class representatives for
the children. If those representatives change after a merge, rebuild updates
the affected parent keys.

## Union-find

Semper maintains e-class membership with union-find. Every e-node has a class
identifier. `find` follows parent links to the class's canonical
representative, and path compression shortens later lookups. A `union` between
two representatives makes one the survivor and the other a child of it.

The survivor is an implementation choice, not a preferred term. A merge does
not rewrite or delete either side, and choosing a different survivor does not
change the asserted equality. The `--union-by` flag changes the survivor
heuristic and can change operational work and printed representatives, but it
does not change which input equality was asserted. [Annex C](C-flag-reference.md)
lists the available policies.

Path compression and union updates are included in push and pop restoration.
Chapter 7 describes that semi-persistent storage.

## Congruence

Congruence adds the rule that applications of the same operator to equal
arguments are equal. The example first creates a second parent and confirms
that it is distinct from `left`. It then merges only the leaf classes:

```lisp
{{#include ../examples/06-congruence.egg:congruence}}
```

After `(union (a) (b))`, both parent nodes have the canonical key
`f(Cab, Cab)`. Rebuild detects that collision and merges the parent classes, so
`(check (= left right))` passes without a rewrite rule.

The final `print-size` reports:

```text
a: 1
b: 1
f: 2
total: 4
```

The graph still stores four e-nodes. The two leaves now occupy one e-class, and
the two parents occupy another. Congruence changes class membership, not the
node count. Hash-consing prevents duplicate allocation for a key when it is
inserted; rebuild can later make historical nodes collide, in which case it
merges their classes and retains both arena entries.

A rewrite that merges two classes therefore also affects every application
whose child points into those classes. Rules match and extend these shared
classes instead of enumerating a separate rewritten tree for every equivalent
term.

## Rebuild

A class merge immediately updates union-find, but parent e-nodes can still
contain the absorbed representative in their stored keys. Rebuild restores a
congruence-closed state. It visits parents from the absorbed class's use-list,
replaces child identifiers with current representatives, canonizes the
children, and probes the hash-consing cache again. A collision schedules
another class merge, so the process continues until no pending merges remain.

The `union` and equality-check commands rebuild before returning their result.
Saturation also rebuilds before constructing each round's matching indexes.
Rules therefore match against a congruence-closed graph rather than an
intermediate state with stale parent keys. `print-size` itself only reads the
node arenas; it does not trigger rebuild.

Chapter 10 describes the operator-specific canonization performed during term
construction and parent recanonization. The
[e-graph design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/05-egraph.md)
specifies the rebuild worklist and use-list algorithm.

## What an equality check asks

`(check (= t1 t2))` builds both ground terms, rebuilds the e-graph, and asks
whether their e-nodes have the same union-find representative. It does not
compare two extracted syntax trees.

A passing check means the asserted unions, fired rules, declared algebraic
canonization, and active congruence procedure derived the equality. A failing
check means the terms remain in different classes in the graph as currently
computed. It is not a proof that the terms are unequal in every model of the
declared laws.

Likewise, `(check (!= t1 t2))` accepts when the two current representatives are
different. Chapter 11 explains how plain, eager, and lazy congruence modes
change the work performed before that decision.

The storage structures are specified in the design chapters for
[nodes](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/01-node-storage.md),
[e-classes](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/02-classes-and-union-find.md),
and
[hash-consing](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/03-hash-consing-caches.md).
