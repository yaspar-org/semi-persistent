# Chapter 15 — Proof Logging

[← Ch 14: Soundness](14-soundness.md) · [Table of Contents](00-table-of-contents.md) · [Ch 16: Extraction →](16-extraction.md)


## Motivation

When two e-nodes are found equal, the user may want to know *why*.
A chain of axioms and congruences led to the equality, and the proof
system must reconstruct that chain on demand.

The `PROOFS` const generic selects code paths at compile time. When `false`, no
proof/history vectors are allocated, no history is recorded, and const-gated
proof work is eliminated. The `Option` fields that would own those vectors
remain as `None` in the generic structs. When `true`, the engine maintains an uncompressed proof
forest and a copy-on-first-re-canonization history store.
The engine optionally records a proof forest that can reconstruct the
chain of axioms and congruences leading to any equality.

Enabled by `const PROOFS: bool = true` on the `EGraph` type parameter.
When `false`, proof-specific execution compiles away; empty `Option` fields
remain in the data layout.

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
    Filler,
    Rewrite { rule_id: RuleId },
    Congruence { node_a: G, node_b: G },
    Axiom { axiom_id: AxiomId },
    ACSuperposition { node_a: G, node_b: G },
    ACInterReduction { node_a: G, node_b: G },
    ACAxiomCP { node_a: G, node_b: G },
    Cancellative { node_a: G, node_b: G },
    InverseCancel { node_a: G, node_b: G },
}
```

- `Filler`: default-initialization value; it is never a real proof edge.
- `Rewrite`: two nodes were merged by a rewrite rule firing.
- `Congruence`: two nodes were merged because their children became
  equal (detected during rebuild).
- `Axiom`: two nodes were merged by an explicit `(union ...)` command or
  another caller-supplied axiom merge.
- The five AC-specific variants identify critical-pair, inter-reduction,
  semantic-axiom, cancellative, and inverse-cancellation merges.

The distinction between `Rewrite` and `Axiom` matters for proof
presentation: rewrites reference user-defined rules (by index),
while axioms reference caller-registered equality assertions.

## Proof Forest

The union-find stores a `Justification` edge for each union operation
in the `justification` vector (only allocated when `PROOFS = true`).

The proof forest uses the uncompressed `parent_proof` vector
(see Chapter 2), not the path-compressed `parent`. This
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

Build each node-to-root path, put the first path's ids in a hash set, then
scan the second path to its first shared node. This is O(depth) expected
time per query under the hash table's usual assumptions and requires no
preprocessing.

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

For batch proof checking and proof export, `LcaTable` uses the
Bender–Farach-Colton algorithm: O(n) preprocessing and O(1) per LCA
query. The algorithm reduces LCA to range minimum query (RMQ) via an
Euler tour of the proof tree, then exploits the ±1 property of the
depth array to build a block-decomposed lookup table. The alternative
`LcaTableCompact` stores depth deltas and reconstructs candidate depths
with an O(log n)-length in-block prefix sum.

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
visit their LCA: the shallowest node in that range. This reduces
LCA to range minimum query (RMQ) on the depth array.

```
LCA(E, F):
  R[E]=5, R[F]=8
  D[5..8] = [2, 1, 2, 3]  →  min at position 6, depth 1 → node A  ✓
```

Two variants are provided:

- `LcaTable`: stores full absolute depths. Simpler, faster queries.
- `LcaTableCompact`: stores `i8` deltas + block-start depths. It avoids
  one absolute-depth word per Euler entry, but its total-memory effect is
  workload- and index-width-dependent; queries do a short prefix sum.

| Scenario | Naive walk-up | Full-depth Euler-tour table |
|----------|---------------|-----------------------------|
| Single `explain(a, b)` | O(depth) | O(n) build + O(1) LCA + O(depth) path output |
| `k` batch queries | O(k × depth) | O(n) build + O(k) LCA + output paths |
| Proof export | O(k × depth) | O(n) build + O(k) LCA + emitted proof steps |

The compact table has the same O(n) build bound and O(log n) query bound
because its block size is O(log n).

The production batch path is `EGraph::dump_all_proofs`, exposed by
`--proofs --dump-proofs FILE`. It builds one `LcaTable`, queries one LCA per
e-node, and writes the path from each node to its current representative.
Writing remains O(total emitted proof steps); O(1) describes the LCA query,
not serialization of an arbitrarily long path.

`ProofBuf` accumulates the justification chain:

```rust
pub struct ProofBuf<G> {
    steps: Vec<(G, G, Justification<G>)>,
    path_a: Vec<G>,
    path_b: Vec<G>,
    seen: HashSet<usize>,
    rev: Vec<(G, G, Justification<G>)>,
    children_a: Vec<G>,
    children_b: Vec<G>,
    group_a: Vec<G>,
    group_b: Vec<G>,
}
```

`steps` records each directed proof edge and its justification. The
remaining fields are reusable scratch for path discovery, reversal, and
deep child grouping.

## `explain_deep`

For a more detailed proof, `explain_deep` expands congruence steps: if two
nodes were merged by congruence, it explains why each pair of children is
equal. The implementation iterates by index through the growing
`ProofBuf.steps` vector, so it does not recurse on the Rust call stack. It does
not maintain a separate visited set for deep expansions; `ProofBuf.seen` is
scratch for the shallow LCA walk.

## Semi-Persistence

The proof forest is stored in the union-find's parent/justification
vectors. In a `TRACK = true` graph those vectors are semi-persistent, and
`push`/`pop` snapshots and restores proof state. `TRACK = false` retains
forward proof logging when `PROOFS = true` but does not support marks.

## Verification Boundary

The verified union-find core proves the fast parent forest's partition and
well-foundedness invariants and proves storage/restore contracts for the
optional proof-parent and justification columns. Proof-path rerooting, the
proof-parent forest invariant, the naive explanation walk, `LcaTable`
construction/query, `explain_deep`, and serialization remain ordinary Rust
covered by executable tests.

`dump_all_proofs` emits one deterministic node-to-representative path for each
e-node. It does not enumerate alternative proofs and does not call
`explain_deep`. No independent replay checker currently validates the dump.
Accordingly, this chapter does not claim a machine-checked theorem that every
emitted explanation is a valid independently checked certificate.

---
[← Ch 14: Soundness](14-soundness.md) · [Table of Contents](00-table-of-contents.md) · [Ch 16: Extraction →](16-extraction.md)
