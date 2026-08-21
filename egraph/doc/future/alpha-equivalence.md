# Alpha-Equivalent E-Graphs: Unified Design

**Status**: design for future work. Of the three variants below, only the
Director variant has landed primitives: `egraph/src/director.rs` (the
bitmatrix types and `PortArity`). Nothing is wired into the e-graph: no
module outside `director.rs` uses it, and the `PortAlgebra` trait does not
exist in the tree. `A3-future-work.md` also records thinnings as a third
binder-aware candidate; its merge and matching laws are not yet specified
enough to instantiate the interface proposed here.

## 1. Overview

This document explores a possible common e-graph interface for
alpha-equivalence with binders. It proposes a `PortAlgebra` trait for three
variants, but does not establish that the trait is sufficient for the full
Slotted semantics:

| Variant | Edge label | Class metadata | UF witness | Merge policy |
|---------|-----------|----------------|------------|--------------|
| Classic | `()` | `()` | `()` | trivial |
| Director | partial-injection matrix | port count `u8` | contraction matrix | shrink to intersection |
| Slotted | slot renaming map | `(SlotSet, SymmetryGroup)` | slot renaming | shrink to intersection |

The binder-aware variants share labeled e-class references and composable
union-find witnesses. Interface contraction is central to both, but a literal
set intersection is not a complete shared merge law: Director ports are
positional, while Slotted classes also quotient references by a symmetry group.
The exact contraction and canonicalization laws must be stated per instance.

The key invariant is that every eclass reference carries a port mapping.
In a standard e-graph, an enode stores plain eclass ids for its children,
and the union-find stores plain eclass ids for parent pointers. In a
binder-aware e-graph, there are no bare eclass references. Every reference
to an eclass (whether from an enode child edge, a union-find link, or a
match binding) is paired with a label that describes how the referrer's
ports map to the referent's ports. This is what makes alpha-equivalence
work: the same eclass can be referenced from different contexts with
different port mappings, and the label on each reference explains how
bound variables are routed through that particular edge.

## 2. Background: Directors and Slotted E-Graphs

### 2.1 Directors (Sinot, Fernández & Mackie)

In a standard e-graph, every eclass implicitly depends on whatever
bound variables are in scope. Directors make this dependency explicit
by annotating each parent-to-child edge with a director matrix
that says how the parent's bound variables route into the child.

Each eclass has a set of ports numbered `0..n-1`. A port represents
a bound variable that the eclass depends on. The port numbering is
local to each eclass: port 0 in one eclass is unrelated to port 0
in another. There are no global variable names.

Each edge from a parent enode to a child eclass carries a partial
injection from parent ports to child ports. Entry `D[j] = i` means
"the bound variable at parent port `j` corresponds to child port
`i`." If a parent port has no entry, that bound variable doesn't
appear in this child. This follows Sinot's convention: directors
"direct" you from the parent down to where each bound variable lives
in the children.

When an edge crosses a binder (like `lambda`), the binder introduces
a new port in the child that has no corresponding parent port. The
child's scope is the parent's scope plus the newly bound variable.

Example: `lambda x. lambda y. lambda z. (foo x y z 0)`.

```
lambda_x (scope: {})
 └─ edge: [binds x → child port 0]
    lambda_y (scope: {x=0})
     └─ edge: [port 0→0, binds y → child port 1]
        lambda_z (scope: {x=0, y=1})
         └─ edge: [port 0→0, port 1→1, binds z → child port 2]
            foo (scope: {x=0, y=1, z=2})
             ├─ child 1 (x): [parent port 0 → child port 0]
             ├─ child 2 (y): [parent port 1 → child port 0]
             ├─ child 3 (z): [parent port 2 → child port 0]
             └─ child 4 (0): [] (no ports, constant)
```

Each leaf eclass (`x`, `y`, `z`) has 1 port. The `foo` enode has 3
ports and its director matrices route each port to exactly one child.

An n×k partial-injection matrix encodes the edge (n parent ports, k
child ports). For small arities, this fits in a `u64`.

Following two edges in sequence composes their directors: for each
parent port, follow the outer matrix to get the
intermediate port, then follow the inner matrix to get the child port.

When a rewrite proves two eclasses equal, the merged eclass may need
fewer ports than either side. The rewrite produces a UF label that
maps the absorbed eclass's ports to the representative's ports. Ports
not in the mapping are dropped: they represent bound variables that
the merged equivalence no longer depends on.

After a merge shrinks a scope, every parent edge must be rewritten
by composing the old edge label with the UF label. If this causes a
parent's scope to shrink too (because some of its ports now map to
nothing), the cascade continues upward.

### Worked example: rewrite `(foo x y z 0) → y`

The rule `(foo ?a ?b ?c 0) → ?b` fires. Eclass A = `foo(x,y,z,0)`
has scope `{x=0, y=1, z=2}`. Eclass B = `y` has scope `{0}`.

UF label `A → B`: port 1 → port 0 (only `y` survives).

Rebuild cascade:

```
lambda_z edge: [0→0, 1→1, binds z→2] into A
  compose with A→B [1→0]:
  port 0(x) → A.0 → dropped
  port 1(y) → A.1 → B.0  ✓
  binds z   → A.2 → dropped
  → new edge: [port 1→0], lambda_z scope shrinks to {y=0}

lambda_y edge: [0→0, binds y→1] into lambda_z
  compose with lambda_z relabel [old 1→new 0]:
  port 0(x) → old 0 → dropped
  binds y   → old 1 → new 0  ✓
  → new edge: [binds y→0], lambda_y scope shrinks to {}

lambda_x edge: [binds x→0] into lambda_y
  compose with lambda_y relabel [old 0→dropped]:
  binds x → old 0 → dropped
  → new edge: [], lambda_x scope unchanged (already {})
```

Final state: `(lambda x. lambda y. lambda z. y)` with directors
correctly showing only `y` flows through.

### 2.2 Slotted E-Graphs (Schneider et al., PLDI 2025)

Slot maps annotate each edge with a bijective renaming from the child class's
slots to the parent's invocation slots. Slots are globally unique names
(interned `u32`), not positional indices.

Each class carries a `SlotSet` (the set of slot names that are
semantically meaningful) and a `SymmetryGroup` (permutations of slots
that leave the class invariant).

`find(id)` returns `(leader, SlotMap)`, where the slot map composes
along the UF path. Composition is lazy: edges are not rewritten on
merge.

On merge, `slots(merged) = slots(a) ∩ slots(b)`. Slots present in one
side but not the other become redundant. The UF entry for the absorbed
class stores the renaming from its slots to the survivor's slots, and
`shrink_slots` removes redundant slots from the class and restricts
the symmetry group.

The hashcons key is the "weak shape": a canonical renaming of slots
to `$0, $1, $2, ...` in order of first occurrence. Two alpha-equivalent
terms produce the same weak shape.

Substitution is pluggable via the `SubstMethod` trait. The default
extracts one representative term, performs tree substitution, and
re-adds the result. This is sound but potentially incomplete per
iteration.

### 2.3 Comparison

| | Directors | Slotted |
|---|---|---|
| Variable identity | positional (0..n) | nominal (global names) |
| Edge label size | k×n bits | k pairs of u32 |
| Composition cost | O(n) | O(k log k) |
| Merge direction | shrink (intersection) | shrink (intersection) |
| Symmetry tracking | no | yes (group algebra) |
| UF witness | contraction matrix | slot renaming |
| Hashcons key | (op, edges with labels) | weak shape |
| Permutations | representable on an edge; no class-symmetry quotient | represented with class symmetry |

Both are instances of the same abstract pattern: edges carry morphisms
between port interfaces, and merge shrinks the interface to the intersection.

### 2.4 The Underlying Mathematical Object

At the level of one edge, Director and slot-map labels can both encode a
partial injection between finite interfaces. That common edge-level object is
not the whole e-graph semantics. Slotted classes additionally carry
automorphisms that identify multiple slot renamings; positional Directors do
not obtain that quotient merely by choosing a port order.

For directors, ports are indices `0..n`. The mapping is an array of
integers: `map[child_port] = parent_port` (child-indexed) or
`map[parent_port] = child_port` (parent-indexed). The encoding is
compact (a few bits per entry) but fragile: indices shift when ports
are added or removed.

For slot maps, ports are names such as `Slot(u32)` and a mapping can be a
sorted list of `(source_name, target_name)` pairs. Its size depends on the
chosen inline capacity and representation. No implementation or measurement in
this repository establishes a concrete byte ratio against Directors.

Converting names to positions can reproduce an individual mapping only after
choosing an order. Reproducing Slotted semantics also requires canonicalizing
that order under the class symmetry group and proving that merge, matching,
and hash-consing respect the quotient. Until those obligations are discharged,
the algorithms should not be described as isomorphic.

The practical tradeoff between positional and nominal addressing:

| | Positional (directors) | Nominal (slotted) |
|---|---|---|
| Storage per edge | representation-dependent; dense matrix or compact partial map | representation-dependent name pairs |
| Merge | Compute index correspondence, renumber | Intersect by name, no renumbering |
| Shrink | Shift indices above removed port | Just drop the name |
| Composition | Array index chasing, O(k) | Hash/sorted lookup, O(k) |
| Hashcons | Canonicalize index assignment | Canonicalize name assignment |

Positional encodings can be more compact when arities are small, while nominal
encodings avoid positional renumbering. The magnitude is workload- and
layout-dependent and must be measured with the actual inline/spill and slot-map
representations before making a ratio claim.

- Commutative operators swap children (the two orderings need different
  port mappings that are not order-preserving)
- Multi-arity binders bind variables in an order that children may permute
- Symmetry groups exist (two e-nodes in the same class may use ports in
  different orders)

Positional directors can encode the first two cases after an order is chosen,
and nominal slot maps can represent the corresponding name relations. Neither
representation by itself solves the third case: matching Slotted
alpha-equivalence semantics still requires canonicalizing under the class
symmetry group and proving that merge, matching, and hash-consing respect that
quotient.

### 2.5 Director Encoding: Child-Indexed vs Parent-Indexed

A director matrix can be stored two ways. Parent-indexed storage
(the original ColIdx form) uses one entry per parent port:
`col[parent_port] = child_port` (0 = dropped, 1..k = child port 0..k-1).

```
Example: Add(x, y) left child edge, parent ports {y=0, x=1}, child port {0}

    col[0] = 1   (parent port 0 (y) → child port 0)
    col[1] = 0   (parent port 1 (x) → dropped)
```

Parent-indexed is good for substitution: "does parent port j flow
here?" is an O(1) lookup. It is bad for child shrink: the scheme must
scan all n entries to find and remove references to the deleted child
port, then renumber.

Child-indexed storage uses one entry per child port:
`entry[child_port] = parent_port` (NONE = unmapped).

```
Example: same edge

    entry[0] = 0   (parent port 0 → child port 0 (y))
```

Child-indexed is good for child shrink (delete the entry, shift
remaining, O(k)) and good for composition (follow child→parent
directly). The substitution check scans k entries for the target
parent port (O(k), but k is typically 1-2).

The recommendation is to use child-indexed storage (better for
shrink-on-merge) and use the bitvector matrix (k×n bits) as a working
form for bulk operations (compose, intersection), converting between
them as needed (both are O(k×n)).

### 2.6 Worked Example: Director Matrices

Consider `Lam x. Lam y. Add(x, y)`:

```
Lam_x (arity 1: port 0 = x)
  │
  │ edge: child-indexed [0 → 0]
  │ "parent port 0 → child port 0 (x)"
  ▼
Lam_y (arity 2: port 0 = y, port 1 = x)
  │
  │ edge to Add: child-indexed [0 → 0, 1 → 1]
  │ "parent port 0 → child port 0 (y), parent port 1 → child port 1 (x)"
  ▼
Add (arity 2)
  ├── left child edge: child-indexed [0 → 0]
  │   "parent port 0 → child port 0 (y)"
  │   parent port 1 (x) is DROPPED — not in this child
  │   ▼
  │  VAR (arity 1) — this is y
  │
  └── right child edge: child-indexed [0 → 1]
      "parent port 1 → child port 0 (x)"
      parent port 0 (y) is DROPPED — not in this child
      ▼
     VAR (arity 1) — this is x
```

The bitvector matrix form (n rows = parent ports, k cols = child ports):

Left edge (1×2):
```
         p0(y)  p1(x)
    c0 [   1      0  ]
```

Right edge (1×2):
```
         p0(y)  p1(x)
    c0 [   0      1  ]
```

Substitution `[y := expr]` (substitute parent port 0) walks Add's
children:

- Left edge: child-indexed `[0 → 0]`. Entry 0 maps to parent port 0
  (y). Match: the child is VAR, so replace it with `expr`.
- Right edge: child-indexed `[0 → 1]`. Entry 0 maps to parent port 1
  (x). No match: skip, since `y` doesn't flow through this child.

Director-guided pruning: only the left subtree is visited. The right
subtree is skipped entirely in O(1).

### 2.7 Shift Analysis: Binder Introduction and Removal

A critical test for any binder representation is what happens when
a rewrite rule introduces or removes a binder, causing free variables
to shift. This is the operation that breaks sharing in de Bruijn
representations and motivates the edge-label approach.

Consider the eta-expansion rule:

```
(rewrite t (Lam ((x Term)) (App t x)))
```

This wraps `t` under a new binder. (In practice, this rule would be
guarded by a type or eta-long condition to prevent it from firing on
its own output and diverging. We omit the guard here to focus on the
sharing analysis.)

In a direct de Bruijn substitution that stores indices in nodes, wrapping `t`
under a new binder changes the indices of its free variables. Implementations
using explicit substitutions, levels, delayed shifts, or memoized shifted
views can mitigate the resulting copying, so the example below is a
worst-case illustration of the direct representation rather than a universal
cost theorem.

Suppose the e-graph contains a large shared subterm `S` that appears in
many places, some under 0 binders, some under 1, some under 2. Before
the rewrite, `S` is a single e-class. After eta-expanding one occurrence,
what happens?

#### De Bruijn indices

Under that direct representation, `S` at depth 0 uses `var(0)` for its first
free variable. Wrapping it under a new binder shifts free indices:
`var(0)` becomes `var(1)`, `var(1)` becomes `var(2)`, and so on. The shifted
term has a different structural key, so an eager tree-copy implementation may
materialize a second representation. If every node depends on a shifted free
index, a 1000-node term can require up to another 1000 changed nodes; unaffected
subgraphs can still be shared.

At ten binder depths, the direct eager representation can approach ten shifted
variants. This is the workload the edge-label designs intend to avoid, not a
claim about every de Bruijn implementation.

```
Before:  S (shared, 1000 nodes)
After:   S, S↑1, S↑2, ... S↑10  (10,000 nodes, no sharing)
```

#### Slotted e-graphs

`S` has slots `{$a, $b}` for its free variables. Wrapping under a new
binder doesn't change `S` at all: the new binder introduces a fresh
slot `$x`, and the edge from the new `Lam` to `App(t, x)` carries a
slot map `{$a → $a, $b → $b}` (identity on S's slots). The new variable
`$x` is routed separately to the `Var` node.

Under the proposed Slotted invariants, `S` can remain one e-class; the new
context is represented by labels rather than eager index shifting.

```
Before:  S (shared, 1000 nodes)
After:   S (unchanged, still 1000 nodes)
         + 1 new Lam node, 1 new App node, 1 new Var node
```

The slot map on the edge absorbs the "shift": it is just a renaming that
maps S's slots through the new binder's scope. The e-class itself is
untouched.

#### Directors

`S` has arity 2 (ports 0, 1 for its free variables). Wrapping under a new
binder creates a new scope with arity 3 (port 0 = new bound var, ports 1-2
= S's free vars). The edge from `App` to `S` carries a director matrix:

```
Child-indexed: [0 → 1, 1 → 2]
"parent port 1 → child port 0
 parent port 2 → child port 1"
```

Under the proposed Director invariants, `S` itself remains unchanged: the edge
director represents the changed context.

```
Before:  S (shared, 1000 nodes, arity 2)
After:   S (unchanged, still 1000 nodes, arity 2)
         + 1 new Lam node, 1 new App node
         + edge to S has director [0→1, 1→2] (the "shift")
```

Both proposals aim to preserve this sharing in the example. That does not make
their complete merge, symmetry, matching, or canonicalization semantics
identical.


## 3. The `PortAlgebra` Trait

The trait abstracts the scope/edge-label representation. Every e-graph
operation that touches scopes routes through it.

### Edge Labels

Every parent-to-child edge carries a label describing how the
parent's bound variables route into that child. This follows the
original director convention (Sinot 2005): the director at a parent
node tells you, for each bound variable in the parent's scope, which
child it appears in.

- E-node → child edge: the label maps parent ports to child ports.
  For each port in the parent's scope, the label says where that
  bound variable is found in the child (or that it's absent from
  this child).
- UF edge (member → rep): the label maps member ports to rep ports.
  `find(x)` walks the chain from `x` to the rep, composing labels
  along the way, and returns `(rep, composed_label)`.

### What Each E-Graph Operation Needs

Before presenting the trait, it helps to know which primitives each
e-graph operation relies on. Most operations only compose labels;
`factor` is exclusive to e-matching, and `merge` is the contraction
step.

| Operation | What it does | Required primitives |
|-----------|-------------|-------------------|
| `mk_enode(op, children)` | Build enode, store edge labels | (type-check only) |
| `hashcons_key(enode)` | Structural key for congruence lookup | `canon_key` |
| `ac_canon(children)` | Sort child multiset for AC | `canon_key` |
| `find(ec)` | Walk UF to rep, compose labels | `compose`, `is_id` |
| `path_compress(ec)` | Shorten UF chain | `compose` |
| `union(a, b, witness_a, witness_b)` | Merge eclasses, shrink scope | `merge` |
| `rebuild()`, update edges | Rewrite child edges to current reps | `compose`, `canon_key` |
| `rebuild()`, congruence | Merge eclasses with equal keys | `merge` (indirect) |
| `enter_binder(edge, k)` | Extend child scope with k bound ports | `extend_child_scope` |
| `ematch_edge(pat, cand)` | Match pattern against candidate | `factor` |
| `α_equal(n1, n2)` | Compare enodes modulo scope | `canon_key` |
| `explain(a, b)` | Walk proof forest, collect labels | `compose` (display only) |
| `instantiate(rhs, σ)` | Build enodes from RHS template | `compose`, `extend_child_scope` |

### Trait Definition

The trait sketch exposes seven methods. `id` produces the identity label
for a scope, and `compose` chains two labels: these two are used on
every `find`. `is_id` is a fast check used to short-circuit no-op
composition. `canon_key` produces an equality-checkable hash-consing key
within one instance. Cross-instance agreement is a separate refinement
obligation. `merge` computes the instance-specific contracted rep scope when
two classes are unified. `extend_child_scope` is used when entering a binder.
`factor` is the e-matching primitive: given a pattern edge and a
candidate edge, find the label that completes the triangle.

```rust
trait PortAlgebra {
    type Scope: Clone + Eq + Hash;
    type Label: Clone + Eq + Hash;
    type CanonKey: Clone + Eq + Hash;

    fn id(s: &Self::Scope) -> Self::Label;
    fn compose(f: &Self::Label, g: &Self::Label) -> Self::Label;
    fn is_id(m: &Self::Label) -> bool;

    /// Equality-checkable key for hash-consing. The instance must prove:
    /// equal keys iff the labels denote the same mapping under that
    /// instance's symmetry semantics. Hash collisions are then resolved by
    /// CanonKey::eq in the ordinary HashMap contract.
    fn canon_key(m: &Self::Label) -> Self::CanonKey;

    /// Merge two eclasses. Given evidence that eclasses A and B
    /// should be equal (via labels witness_a: W→A and witness_b: W→B
    /// from a common source scope W), compute a contracted scope R satisfying
    /// the instance's merge law. Returns R and the UF labels A→R and B→R.
    /// Any claim that R is minimal is an instance theorem, not part of this
    /// signature alone.
    ///
    /// The common source W is implicit: callers construct the
    /// witnesses differently depending on context (see table below).
    fn merge(
        witness_a: &Self::Label,
        witness_b: &Self::Label,
    ) -> MergeResult<Self>;

    /// Extend the child scope of this edge by k fresh ports
    /// (for entering a binder that binds k variables). The parent
    /// scope is unchanged; the child scope grows by k new ports
    /// that have no corresponding parent port.
    fn extend_child_scope(m: &Self::Label, k: usize) -> Self::Label;

    /// E-matching: given a pattern edge and a candidate edge that
    /// share a target, find a label that makes the triangle commute.
    /// Returns None if the pattern doesn't match.
    fn factor(
        pattern: &Self::Label,
        candidate: &Self::Label,
    ) -> Option<Self::Label>;
}

struct MergeResult<A: PortAlgebra + ?Sized> {
    pub rep_scope: A::Scope,
    pub a_to_rep: A::Label,  // A → R
    pub b_to_rep: A::Label,  // B → R
}
```

### How `merge` Witnesses Are Constructed

The `merge` signature takes two labels from an implicit common source.
The source and witness construction differ by caller:

| Caller | Common source W | witness_a | witness_b |
|--------|----------------|-----------|-----------|
| Rewrite fires | Pattern scope (the pattern's free variables) | Pattern-to-A via match substitution σ | Pattern-to-B via RHS evaluation |
| Congruence closure | Shared enode shape (the enode's port space) | Enode-shape-to-A (identity or projection) | Enode-shape-to-B (identity or projection) |
| Port GC | Used-port subset | Identity on used ports of A | (not applicable: single-class operation) |

### How `find` and `rebuild` Work Together

`find(x)` walks the UF chain `x → ... → rep`, composing labels.
The result is `(rep, label: x_scope → rep_scope)`.

During rebuild, for each enode's child edge `(child_ec, label_old)`:

1. Call `find(child_ec)` to get `(rep, uf_label)`.
2. The new edge is `(rep, compose(label_old, uf_label))`.
3. Rehash the enode with the updated edges.

Rebuild only ever composes labels; it never needs `factor`. The
`factor` operation is only used during e-matching.

### Instances

In the proposed classic (no-binders) instance, `Scope = ()`, `Label = ()`, and
`CanonKey = ()`.
All operations are trivial: `compose((), ()) = ()`, `merge` returns
`((), (), ())`, `canon_key` returns `()`, `extend_child_scope` returns
`()`, and `factor` returns `Some(())`. This is intended to recover
standard egg-style e-graphs as a degenerate instance. Whether monomorphization
preserves the current layout and removes all additional work must be checked
with layout/code-generation tests and Criterion; it is not established by the
trait sketch.

In a Directors instance, `Scope` can be a port count and `Label` a compact or
spilled bitmatrix. Composition follows partial-injection composition. A
collision-safe `CanonKey` must include dimensions and normalized matrix
content; a bare 64-bit hash is not identity. Merge, scope extension, and
factorization remain algorithms to specify and prove. Positional ports avoid
nominal lookup but do not by themselves represent class automorphism groups.

In a slot-map instance, `Scope` can contain a slot set plus symmetry metadata
and `Label` a partial renaming. Composition is map composition. Merge,
factorization, and canonical-key construction must operate modulo the class
symmetry group. A canonical key must be an equality-checkable representation,
not only a hash. Agreement with a Director implementation is a future
cross-instance refinement target, not a property supplied by relabeling alone.

The slotted e-graph design (Schneider et al.) tracks a `SymmetryGroup`
per eclass: the set of slot permutations that leave the class
invariant. The trait above does not model symmetry tracking; it
handles only the morphism algebra on edges. Symmetry is an orthogonal
extension: the directors instance has trivial
symmetry (ports are positional), and a full slotted implementation
would layer symmetry tracking on top of this trait.

## 4. Ground Term Insertion After Scope Contraction

Ground term insertion is bottom-up and representation-agnostic.
The key insight: insertion only sees current reps and current labels,
so historical contractions are invisible.

### Insertion Algorithm

To insert `f(t1, …, tk)`:

1. Recursively insert each `ti`, getting `(rep_i, scope_i)`.
2. Compute the enode's scope from the children's scopes plus any
   ports `f` binds. Build edge labels `label_i` mapping each
   `scope_i` into the enode's scope.
3. Hash-cons lookup on `(f, [(rep_i, canon_key(label_i))])`.
4. Hit → return existing eclass. Miss → create fresh enode and eclass.

### What Happens When a Scope Shrinks

When `union` merges two eclasses and the merged scope is smaller
(some ports were redundant), rebuild propagates: every parent edge
gets its label rewritten via `compose` with the UF label. After
rebuild, all existing enodes' hash-cons keys reflect current scopes.

New insertions build edges against current scopes (step 1 calls
`find`), so they naturally produce the same keys as rebuilt enodes.

### Worked Example: `(foo x y z 0) → y`

Setup: inside `lambda x. lambda y. lambda z. ...`, eclass A =
`foo(x,y,z,0)` has scope `{x=0, y=1, z=2}`. The rule
`(foo ?a ?b ?c 0) → ?b` fires. RHS eclass B = `y` has scope `{0}`.

The merge produces UF label `A → B`: port 1 → port 0, with ports 0
and 2 dropped.

The rebuild composes each parent edge with the UF label. The cascade
propagates up through the lambdas, shrinking scopes at each level
(see the full cascade in section 2.1).

Re-inserting `foo(x,y,z,0)`:

- `find(A)` returns `(B, [1→0])`. Build edges against B's scope.
- Hash-cons key matches A's post-rebuild key. It hits and returns B.

Inserting `foo(x,w,z,0)` for fresh `w`:

- Different second child (`w ≠ y`). Hash-cons misses, so a new eclass
  is created.
- Rewrite fires again and merges it with B.

### Invariants

1. Read scope from the rep, not from members. Stale scopes produce
   wrong hash-cons keys.

2. Rebuild before insertion (or compose UF labels into edges lazily
   during insertion). Otherwise hash-cons hits are missed.

3. Enode scope ≠ eclass scope. After contraction, member enodes
   may have larger scopes than their eclass. This is correct: the
   enode scope is for hash-consing, and the eclass scope is what
   parent edges refer to.

4. Don't delete member enodes with larger scope. After contraction,
   member enodes may have more ports than their eclass. These enodes
   are the *only* structural record connecting the larger-scope term
   to the smaller-scope class. Without them, `explain(foo(x,y,z,0), y)`
   must reconstruct the rewrite derivation from rule history, which is
   slower and sometimes impossible if rules were retired. They are
   redundant for evaluation but essential for provenance.

### Testing Strategy

Two harnesses behind the same `PortAlgebra` boundary:

1. Algebraic laws per instance (property-based): `compose`
   associative, `id` neutral, canonical keys agree exactly with semantic label
   equality, and each instance's stated merge and scope-extension laws hold.

2. Cross-instance equivalence: fix a rewrite system and terms with binders,
   saturate under each completed `PortAlgebra` instance, and assert the induced
   alpha-equivalence relation is identical. Include symmetric classes so the
   test does not erase the main semantic difference between the candidates.
   This is finite evidence; a refinement theorem remains the release criterion.
   The laws catch internal bugs; the cross-check catches "internally
   consistent but semantically wrong."
