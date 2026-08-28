# Canonization and the node kinds

Chapter 4 defines the algebraic declaration contract. This chapter describes
the physical child representations selected by those declarations and the
canonization pipeline that prepares an e-node for hash-consing.

## The five child representations

Each operator selects one of five representations for its children. Literal
nodes are a separate leaf kind that carries a concrete value.

| representation | internal kind | stored children | information not represented |
| --- | --- | --- | --- |
| ordered tuple | `Normal` | a fixed-arity tuple in argument order | none |
| unordered pair | `Commutative` | two class ids in sorted order | argument order |
| sequence | `A` | a variadic sequence of class ids | selected associative nesting |
| sorted multiset | `MSet` | class-id and multiplicity pairs | order and nesting |
| sorted set | `Set` | sorted, distinct class ids | order, nesting, and repetition |

Ordinary operators use ordered tuples. Tuples of up to three children have
dedicated storage, while wider tuples use a pooled slice. `:comm` selects the
unordered pair. The associative declarations select a sequence,
`:assoc-comm` selects a multiset, and `:assoc-comm-idem` selects a set.

The missing information in the last column cannot distinguish two e-nodes.
Chapter 4 defines the corresponding equations and Chapter 5 defines how
patterns inspect each representation.

## The canonization pipeline

Term construction performs these operations before inserting an e-node:

1. Replace every child id with its current e-class representative.
2. Flatten eligible nested applications of the same variadic operator.
3. Normalize the resulting child representation.
4. Resolve an empty or singleton variadic result when its declaration permits it.
5. Look up the operator and normalized children in the hash-cons table.

Normalization sorts an unordered pair. It preserves sequence order. For a
multiset it sorts children, coalesces equal entries, and applies the configured
unit, count, and inverse transforms. For a set it sorts and deduplicates
children and removes a configured unit. The legality and meaning of those
transforms belong to Chapter 4.

```lisp
{{#include ../examples/10-node-kinds.egg:node-kinds}}
```

Both `print-size` commands report `total: 3`. The second spelling replaces its
children by the same representatives, sorts them to the same pair, and finds
the existing `eq` node.

Ground-term insertion and rewrite right-hand-side evaluation use this same
pipeline. The full procedure is specified in
[`04-canonization.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/04-canonization.md).

## Recanonization during rebuild

A class merge can make a stored child id noncanonical or make two direct
children equal. Rebuild revisits affected parents, replaces their direct
children with current representatives, and reapplies the representation's
sorting, coalescing, deduplication, unit removal, and multiplicity clamp. A
hash-cons collision then triggers the generic congruence merge described in
Chapter 6.

Multisets retain the original multiplicities until the configured clamp runs.
Nilpotent operators therefore remain `MSet` nodes even at order two. Sets store
no explicit counts because every represented count is one.

Sequence nodes have a narrower rebuild boundary. Rebuild recanonizes the ids
already present in a sequence span, but it cannot enlarge that span when a
child class later acquires a same-operator sequence. Chapter 11 describes the
optional associative inter-reduction work that can add further equalities.

## The boundary

Canonization normalizes one node under its selected representation. It does not
derive consequences that require equations between separate stored nodes.
Generic congruence belongs to Chapter 6, domain equations belong to the rules
of Chapter 5, and optional completion belongs to Chapter 11.
