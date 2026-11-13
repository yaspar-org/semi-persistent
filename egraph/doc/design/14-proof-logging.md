# Chapter 14 — Proof Logging

[← Ch 13: Soundness](13-soundness.md) · [Table of Contents](00-table-of-contents.md)

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

During rebuild, when `recanonize_node` finds that a node's children changed:

1. Check the history bit.
2. If clear: append the original node to the cache's `history` column (variadic
   caches use `history_nodes` and `history_children`), and write the recanonized
   node with the bit set.
3. If already set: skip (children were already saved in a previous
   rebuild cycle).

The copy-on-first-write protocol ensures that the proof system can
always reconstruct the pre-merge state of any node, even after
multiple rebuild cycles.

## `Justification`

```rust
pub enum Justification<G: DenseId> {
    Filler,
    Rewrite { rule_id: RuleId, inst: u32 },
    Congruence { node_a: G, node_b: G },
    Axiom { axiom_id: AxiomId },
    Normalize { node: G, normal: G },
    Build { node: G, inst: u32 },
    ACSuperposition { node_a: G, node_b: G },
    ACInterReduction { node_a: G, node_b: G },
    ACAxiomCP { node_a: G, node_b: G },
    Cancellative { node_a: G, node_b: G },
    InverseCancel { node_a: G, node_b: G },
    Assumption { lit: <G as DenseId>::Index },
}
```

- `Filler`: default-initialization value; it is never a real proof edge.
- `Rewrite`: two nodes were merged by a rule application. `inst` names the
  rule instance, whose premise pairs are the equalities the application
  used (see below); `NO_INSTANCE` when the caller recorded none.
- `Congruence`: two nodes were merged because their children became
  equal (detected during rebuild).
- `Normalize`: a node was merged with its normal form under the operator's
  laws, one child's class or the unit (`and(a, a) = a`, `x + 0 = x`,
  `xor(a, a) = 0`).
- `Build`: a client's set, AC or associative term, kept as an evidence node
  with the children it was given, was merged with the node it is stored as.
  The build `find`s the children, flattens a nested same-operator child by
  splicing a node of its class, and normalizes under the operator's laws;
  `inst` names the splices, and whether the build collapsed to a class.
- `Axiom`: two nodes were merged by an explicit `(union ...)` command or
  another caller-supplied axiom merge.
- The five AC-specific variants identify critical-pair, inter-reduction,
  semantic-axiom, cancellative, and inverse-cancellation merges.
- `Assumption`: a companion solver (the `satcore` crate's EUF layer) asserted an
  equality atom true, and the merge is that assertion. `lit` is an opaque word of the
  configuration's index width whose encoding the client owns; proof extraction
  surfaces it as a leaf antecedent for the client's conflict analysis.

The distinction between `Rewrite` and `Axiom` matters for proof
presentation: rewrites reference user-defined rules (by index),
while axioms reference caller-registered equality assertions.

### Rule instances

A rule application depends on more than its rule: `(rewrite (F (B)) H)`
matches `F(A)` only through `A = B`. Under `PROOFS`, each match opens a rule
instance in a table on the e-graph, and the instance records its premise
pairs, the pairs of nodes the application needs equal:

- for each atom of the query, each child of the matched node paired with
  the node the pattern binds at that position (by position for ordered
  operators, by class for commutative, AC and ACI operators);
- the two sides of each equality atom (`(= x y)`, a global);
- each variable the right-hand side fetches, paired with the class root the
  right-hand side is built over.

An instance that cannot pair a pattern position with a child of the matched
node (a flattened view, whose elements come from nested nodes) or that
contains a collected sequence is marked partial, and `rewrite_premises`
reports it as unknown instead of claiming a complete list. Rule applications
of the sequence engine and of collection rules record no instance yet. The
table is append-only between marks; `restore`, `restore_and_pop` and
`pop_scope` truncate it to the mark's lengths.

## Proof Forest

The union-find stores a `Justification` edge for each union operation
in the `justification` vector (only allocated when `PROOFS = true`).

The proof forest uses the uncompressed `parent_proof` vector
(see Chapter 2), not the path-halved `parent`. This
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

The batch path is `EGraph::dump_all_proofs`, exposed by
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

For a more detailed proof, `explain_deep` expands every step whose premises
are equalities between other nodes, and appends the explanations of those
equalities:

- `Congruence`: the two nodes' original children. For ordered operators the
  children pair by position. For commutative, AC and ACI operators the
  children of both sides, together with the operator's unit and the
  argument of each inverse child, are grouped by class, and in each class
  every member is explained against the first. Pairing one child per class
  from each side would miss the rest: `+(a, b)` and `+(a, a)` after `a = b`
  pair `a` with `a`, and a child in the unit's class has no partner at all.
- `Normalize`: the node's original children, the normal form and the unit,
  grouped the same way.
- `Build`: the evidence node's given children, the spliced nodes and their
  children, and the stored node's original children (or the class it
  collapsed to), grouped the same way.
- `Rewrite`: the rule instance's premise pairs.

The grouped steps (unordered congruence, `Normalize`, `Build`) record their
premise pairs when they merge, from the classes just before the merge, keyed
by the merged pair. Pairing by the classes at explanation time would also
pair children that became equal only through this step or a later one, so an
explanation would cite its own conclusion as a premise.

The leaves are then `Axiom`, `Assumption`, a `Rewrite` with no complete
instance, and the five completion variants, which do not record the rules
and law instances they used. The implementation iterates by index through
the growing `ProofBuf.steps` vector, so it does not recurse on the Rust call
stack. `ProofBuf.seen` is scratch for the shallow LCA walk only.

The expansion is memoized with two order-normalized pair sets, and the
memoization is what makes the walk terminate, not just what makes it fast:

- `expanded` holds the `(node_a, node_b)` pairs of congruence steps whose
  child pairs have already been walked. A congruence step whose pair is
  already in the set is skipped.
- `explained` holds the child pairs whose forest path is already in
  `steps`. A child pair already in the set is not explained again.

Two sets because the guards protect different work. A congruence pair must
not seed `explained`: its forest path can be longer than the one recorded
congruence edge. The initial pair `(a, b)` seeds `explained` but not
`expanded`: its own congruence step still needs its children walked.

Two failure modes without the sets, both observed:

1. **Exponential re-expansion.** A child pair shared by several paths of a
   diamond-shaped explanation is expanded once per path, so nested diamonds
   double the work per level. A two-assertion Boolean-congruence input took
   over 15 seconds; with the sets it takes 0.08 seconds.
2. **Non-termination.** A congruence step's premises are the two nodes'
   *original* children, which predate recanonization. Their present equality
   can route through the very congruence edge the hash-consing collision
   produced. The walk then explains the child pair, re-emits that edge,
   expands it again, and never ends. The SMT regression
   `edge_cases/boolean_backtracking.smt2` (a Boolean child oscillating across
   backtracks) grew past 2 million steps and 16 GB before being killed.

With the sets, every congruence pair is expanded at most once and every
pair's path is appended at most once, so `steps` is bounded by the number of
distinct pairs times the longest forest path, whatever the forest's shape.
Skipping a repeat loses nothing: a repeat appends no steps, and consumers
collect leaf justifications as a set. `deep_proof_diamond_is_linear` in
`egraph_proof_test.rs` pins the linear bound on a nested diamond.

## Proof Mode During Saturation

Proof mode builds client terms through creation evidence, which can add a
node the plain engine would not: a fresh node over non-root children, or a
flagged duplicate of a node with history. Two rules keep saturation under
proofs the same computation as without them:

- **Built terms are memoized.** The hash-cons table cannot find such a node,
  because its stored children are recanonicalized while its history keeps
  the given ones, so `creation_memo` maps `(op, given children)` to the node
  built for it. Without it a rule whose right-hand side re-fires each round
  added one copy per round, and AC patterns enumerated every combination of
  copies: `ac_lazy_alternation.egg` and `deep_constant_fold.egg` exceeded
  2 GB with `--proofs` while they finish in under a second without it.
- **Congruence waits for the round's rebuild.** Creation evidence closes
  congruence after the term it built, which recanonicalizes nodes; inside a
  saturation round those nodes are in the index every later rule of the
  round matches against. While a round is open (`set_round_open`) the merges
  wait on the worklist, as they do without proofs, and the round-end snapshot
  check holds.

Over the fixtures of `tests/egg`, each run with `--proofs` under a 20 s and
2 GB bound, every fixture ends as it does without proofs.

### Evidence nodes

Under `PROOFS`, a build of a set, AC or associative term that changed the
client's term (a child not its class root, a splice, a law that dropped,
merged or cancelled children, or a hit on a node first built from other
children) keeps the client's term as an evidence node and merges it with the
stored node by a `Build` step. Evidence nodes carry `FLAG_SUBSUMED` and
`FLAG_CONGRUENT_DUP`: their content is the stored node's, so matching,
completion, extraction and the hash-cons index skip them, and saturation is
the plain engine's. The canonical build runs on every build, and an evidence
node is reused only for the same client term stored as the same node: the
spelling a build stores depends on the graph (a splice takes the class's
current minimal monomial), so the same term can store a new node later. A
`Build` merge keeps the stored node's root as the class representative.

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

`tests/proof_replay.rs` replays explanations independently of the engine:
for every node of every fixture in `tests/egg` run with proofs on, it takes
`explain_deep(node, find(node))` and accepts a step in a fresh union-find
only once its premises hold there (an axiom joins exactly the terms of its
`union` command; a congruence step's children agree by position, or as
classes after the operator's laws; a normalization leaves only the normal
form's class or repeated classes; a rule application's premise pairs are
joined). Every explanation over the fixtures replays. Steps the checker
cannot replay, because the step records no premises, are counted and
printed: the completion variants and the partial rule instances.

Explanations stay incomplete in the following ways, listed here so a client
does not read them as certificates:

- The completion variants are leaves: a superposition, inter-reduction or
  cancellation step does not record the rules and law instances it used.

`dump_all_proofs` emits one deterministic node-to-representative path for
each e-node (format v2): the registered axioms with their two terms, each
node's current and original children, and each rule application's instance
premises. It does not enumerate alternative proofs and does not call
`explain_deep`. No independent replay checker validates the dump itself.

---
[← Ch 13: Soundness](13-soundness.md) · [Table of Contents](00-table-of-contents.md)
