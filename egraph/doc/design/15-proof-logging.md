# Chapter 15 — Proof Logging

[← Ch 14: Soundness](14-soundness.md) · [Table of Contents](00-table-of-contents.md) · [Ch 16: Extraction →](16-extraction.md)


## Motivation

When two e-nodes are found equal, the user may want to know *why*.
A chain of axioms and congruences led to the equality, and the proof
system must reconstruct that chain on demand.

the engine's approach: zero overhead when proofs are off, full
reconstruction when proofs are on. The `PROOFS` const generic
selects code paths at compile time. When `false`, no proof arrays
are allocated, no history is recorded, and the history bit is never
touched. When `true`, the engine maintains an uncompressed proof
forest and a copy-on-first-re-canonization history store.
The engine optionally records a proof forest that can reconstruct the
chain of axioms and congruences leading to any equality.

Enabled by `const PROOFS: bool = true` on the `EGraph` type parameter.
When `false`, all proof machinery compiles away.

## The History Bit

Each node type has a history bit (MSB of the op field's stored
representation). This bit tracks whether the node's original children
have been saved before re-canonization.

### Copy-on-First-Re-Canonization

During rebuild, when `recanonize_node` is about to update a node's
children:

1. Check the history bit.
2. If clear: save the original children to a proof buffer, set the bit.
3. If already set: skip (children were already saved in a previous
   rebuild cycle).

The copy-on-first-write protocol ensures that the proof system can
always reconstruct the pre-merge state of any node, even after
multiple rebuild cycles.

## `Justification`

```rust
pub enum Justification<G: Copy> {
    Rewrite { rule_id: u32 },
    Congruence { node_a: G, node_b: G },
    Axiom { axiom_id: u32 },
}
```

- `Rewrite`: two nodes were merged by a rewrite rule firing.
- `Congruence`: two nodes were merged because their children became
  equal (detected during rebuild).
- `Axiom`: two nodes were merged by an explicit `(union ...)` command
  or a built-in axiom (e.g., commutativity).

The distinction between `Rewrite` and `Axiom` matters for proof
presentation: rewrites reference user-defined rules (by index),
while axioms reference built-in equalities.

## Proof Forest

The union-find stores a `Justification` edge for each union operation
in the `justification` vector (only allocated when `PROOFS = true`).

The proof forest uses the uncompressed `parent_proof` vector
(see Chapter 2), not the path-compressed `parent_fast`. This
preserves the original merge tree so the proof system can walk from
any node to the root, collecting justifications along the way.

To explain why `a ≡ b`:

1. Find the paths from `a` and `b` to their common ancestor in the
   proof forest.
2. The path from `a` to the ancestor, reversed, concatenated with
   the path from the ancestor to `b`, gives the proof chain.

## LCA Algorithms

Finding the common ancestor uses the Lowest Common Ancestor (LCA)
algorithm on the proof forest. Two implementations are available:

### Naive Walk-Up (default)

Walk up from both nodes simultaneously, marking visited nodes in a
hash set. The first node visited by both paths is the LCA. This is
O(depth) per query and requires no preprocessing.

```
Proof tree (edges = parent pointers with justifications):

        r
       / \
      c   d
     / \   \
    a   b   e
```

Example: `LCA(a, e)` walks `a → c → r` and `e → d → r`, finding
`r` as the first shared ancestor. `LCA(a, b)` walks `a → c` and
`b → c`, finding `c`.

```rust
pub fn explain(&self, a: G, b: G, buf: &mut ProofBuf<G>) -> bool {
    // Walk both paths to root, marking visited nodes.
    // First node visited by both paths is the LCA.
    // Collect justifications along both paths.
}
```

### Euler-Tour Based (batch queries)

For batch proof checking and proof export, the `LcaTable` and
`LcaTableCompact` implementations use the Bender–Farach-Colton
algorithm: O(n) preprocessing and O(1) per LCA query. The algorithm
reduces LCA to range minimum query (RMQ) via an Euler tour of the
proof tree, then exploits the ±1 property of the depth array to
build a block-decomposed lookup table.

```
Tree:           C                    Depth:
              /   \                    0: C
             B     A                   1: B, A
                 /   \                 2: E, D
                E     D                3: F
                      |
                      F

Position:    1  2  3  4  5  6  7  8  9  10  11
Euler E:     C  B  C  A  E  A  D  F  D   A   C
Depth D:     0  1  0  1  2  1  2  3  2   1   0
```

Between the first occurrences of any two nodes, the Euler tour must
visit their LCA — the shallowest node in that range. This reduces
LCA to range minimum query (RMQ) on the depth array.

```
LCA(E, F):
  R[E]=5, R[F]=8
  D[5..8] = [2, 1, 2, 3]  →  min at position 6, depth 1 → node A  ✓
```

Two variants are provided:

- `LcaTable`: stores full absolute depths. Simpler, faster queries.
- `LcaTableCompact`: stores `i8` deltas + block-start depths. ~4×
  less memory for the depth array, queries do a short prefix sum.

| Scenario | Naive walk-up | Euler-tour BFC |
|----------|--------------|----------------|
| Single explain(a, b) | O(depth) | O(depth) (not worth preprocessing) |
| Batch proof checking | O(k × depth) | O(n) + O(1) per query |
| Proof export/compression | O(k × depth) | O(n) + O(1) per query |

`ProofBuf` accumulates the justification chain:

```rust
pub struct ProofBuf<G> {
    steps: Vec<Justification<G>>,
}
```

## `explain_deep`

For a more detailed proof, `explain_deep` recursively explains
congruence steps: if two nodes were merged by congruence, it
explains why each pair of children is equal.

## Semi-Persistence

The proof forest is stored in the union-find's parent/justification
vectors, which are semi-persistent. `push`/`pop` correctly
snapshots and restores proof state.

---
[← Ch 14: Soundness](14-soundness.md) · [Table of Contents](00-table-of-contents.md) · [Ch 16: Extraction →](16-extraction.md)
