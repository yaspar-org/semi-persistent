# Arena Aliasing and the Ghost-Id-Set Proof Style

*The method-layer companion to [Chapter 1 §10](01-verification-design.md). That
section says **why** arena-backed containers need verifying and what we get; this
one develops **how**: the dynamic-frames lineage, the ghost-id-set invariant,
and the frame/anti-frame shape every operation proof takes.*

[Table of Contents](00-table-of-contents.md)

## Abstract

The containers in this crate that hold *graphs* of objects (a sparse set's
dense/sparse cross-index, a linked-list arena, a circular class-list) connect
their nodes with **integer identifiers into a flat arena**, not Rust references.
[Chapter 1 §10](01-verification-design.md) establishes the stakes: this
deliberately bypasses Rust's ownership to allow internally **aliased** and
**cyclic** structures the borrow checker would reject, and in doing so forfeits
all compiler help for the discipline that keeps them well-formed, leaving Verus
as the only guarantee. This chapter is the methodology behind that guarantee. It
names the proof style (a **ghost field describing the structure as unique arena
ids**, with aliasing and separation written as explicit predicates over those
ids) as a concrete instance of **dynamic frames**, and shows how the resulting
operation proofs decompose, bi-abductively, into a *frame* (the untouched ids,
preserved via disjointness) and an *anti-frame* (the side condition the operation
abduces for correctness), with the real reasoning confined to a small explicit
footprint. The aim is that the next person verifying an arena structure (the
B+ tree, the union-find forest) recognizes the pattern and reaches for it.

## 1. Recap: integers-as-pointers bypass rust reference discipline

Recall the setup from [§10](01-verification-design.md): these
containers name their nodes by **integer index into a shared arena `Vec`**, so an
"edge" is an integer stored in a cell's value, not an `&mut` in the borrow graph.
That is the only way to express what they need: the sparse set's mutually-
inverse dense/sparse cross-index (every live id reachable from two directions),
the list arena's many lists sharing one `nodes` vector with tails pointing into
its middle, the class list's literal **cycles** of `next` indices, all of which
`&mut`'s uniqueness rule forbids by construction. And it is why the compiler can
no longer help: a `usize` "pointer" carries no type-level claim about what it
points at, so nothing but a proof rules out a dangling `next`, two lists sharing
a node, or a ring that never closes. The invariants have moved out of the type
system and into the values; Verus is where we put them back. The rest of this
chapter is *how*.

## 2. The proof style: a ghost set of ids, with explicit separation

The technique we use to recover the guarantee is a deliberate, uniform one, and
it is worth naming because it recurs in every arena-backed container. Alongside
the executable arena, each structure carries a **ghost field that describes the
structure mathematically as sets (or sequences) of unique arena ids.** The
executable `next`/`head`/`sparse` indices are then a *representation* of that
ghost description, and well-formedness `wf` is the predicate that ties the
representation to the description. Concretely:

- **`SparseSet`** carries a ghost `Set<nat>` of the live ids (plus a ghost
  sequence modeling the free-id pool). The executable cross-index is well-formed
  exactly when it is a bijection realizing that set: `wf` says the dense and
  sparse arrays are mutual inverses on the live prefix, which is to say the live
  ids are *exactly* the ghost set, each occupying a unique position.

- **`ListArena`** carries a ghost `Seq<Seq<usize>>`: for each list, the sequence
  of its node ids in order. The executable `head`/`tail`/`next` pointers are
  well-formed when they trace out precisely those sequences.

- **`CircularList`** carries the same ghost `Seq<Seq<usize>>`, read as a
  *partition into rings*: each inner sequence is one class, and the executable
  `next` is well-formed when it is the cyclic successor within each ring.

The decisive part, the part the compiler used to enforce and now cannot, is
that **aliasing and separation are written down explicitly, as predicates over
the ids.** In every one of these structures `wf` contains a *disjointness*
clause stating that the ghost id-sets do not overlap:

> no arena id appears in two different lists (or two positions of one list);
> equivalently, the ghost sequences/sets are pairwise disjoint and the live ids
> are distinct.

That single predicate is what the borrow checker would have guaranteed by
forbidding aliasing, except now it is a *formal property we can name, assume,
and prove*, rather than an implicit consequence of `&mut`. Its companion, a
*coverage* clause ("every allocated node belongs to some list"), pins down the
other direction; together, disjoint + coverage say the ghost description is a
genuine **partition** of the arena's live ids, and the executable pointers
realize it.

## 3. This is explicit dynamic frames

The style is not ad hoc; it is a concrete instance of **dynamic frames**
(Kassios), the verification methodology built precisely for heap structures
whose footprint is not statically fixed. In dynamic-frames reasoning, a data
structure is equipped with a specification-level *region*, the set of heap
locations it occupies, and its operations are specified in terms of how they
read, write, and grow that region; separation between two structures is the
*disjointness of their regions*, stated explicitly rather than baked into a
connective. Our ghost id-sets are exactly such regions, with the arena standing
in for the heap and an integer id for a heap location. The disjointness clause
in `wf` is the dynamic-frames separation assertion; the coverage clause bounds
the region; and an operation's contract describes how it moves ids between
regions (a node leaves one list's sequence and joins another's). Where
separation logic hides the footprint inside the `∗` connective and the frame
rule, dynamic frames, and our encoding, make the footprint a first-class
ghost object you can quantify over, which is what we need when the footprint is
"some subset of a shared arena, determined at run time."

This connection is also why the operation proofs have the shape described in the
[ListArena](../../../containers/doc/design/05-list-arena.md) and circular-list
developments. Each mutation touches a small, explicitly identified set of ids,
its *footprint*, and the proof splits into two halves that are exactly the two
halves of a bi-abductive triple `{P ∗ frame} op {Q ∗ frame}`. The **frame** is
the disjointness clause put to work: because the operation's footprint is
disjoint from every untouched list's id-set, those lists' well-formedness is
preserved *for free*: their ids did not move, so their representation facts
carry across unchanged. (In `splice`, every "other ring" case of the proof is
nothing but this frame step.) The remaining work (the **anti-frame**, the
precondition the operation needs to be *correct* and not merely safe) is
likewise discovered the way bi-abduction discovers it: by trying to prove the
postcondition and reading off what is missing. For `splice`, that missing
precondition is `the two rings are distinct` (`cs ≠ ca`); without it the merge
would split a ring instead of joining two, and the proof of the cyclic clause
fails. The disjointness invariant supplies the frame; the abduced side condition
supplies correctness; the footprint is where the genuine reasoning happens.

## 4. The invariant, made operational (per container)

Concretely, the ghost-id-set discipline turns into the same four `wf`
sub-predicates each time, instantiated to the structure's ghost field. Reading
across the row tells you what to write for the next arena container:

| `wf` clause | role (dynamic-frames reading) | `SparseSet` | `ListArena` | `CircularList` |
|---|---|---|---|---|
| **in-range** | ids name real arena slots | `indices` is a bijection of `[0, cap)` | every `model[l][p] < nodes.len()` | every `model[c][p] < n` |
| **disjoint** | regions don't overlap (separation) | live ids distinct; inverse-on-live | a node id is in ≤1 list at ≤1 pos | a node id is in ≤1 ring at ≤1 pos |
| **coverage** | the region is bounded/total | live ∪ free-pool `= [0, cap)` | (lists need not cover the arena) | every node is in some ring |
| **shape** | the pointers realize the region | dense/sparse mutually inverse | `head`/`tail`/`next` trace `model[l]` | `next` is the cyclic successor in `model[c]` |

Two things are worth highlighting because they are easy to get wrong. First, the
**shape** clause is stated *over the ghost model*, never as a pointer-only
property: `list_seq(l)` is the payloads read off the finite ghost sequence
`model[l]`, with no recursion that follows `next`. This is deliberate: an earlier
ListArena attempt made shape a pointer-chasing predicate and needed a "`next`
points at a smaller index" ordering to make the recursion terminate, a *false*
invariant that could express `prepend` but not `append` (which links an old node
*forward* to a freshly-allocated larger index) or `splice`. Defining content off
the ghost sequence removes the termination problem entirely and lets the only
per-index constraint be in-range. Second, **disjoint + coverage together are the
partition**, and that is exactly the dynamic-frames separation between the
structure's sub-regions; it is what makes "merge two lists / two rings" even
*meaningful*, since concatenating overlapping id-sets would not be a set.

## 5. What we get

The payoff is that, for structures the Rust compiler cannot vouch for at all, we
end up with *more* than the compiler would have given us, and all of it as
machine-checked formal properties:

- **Well-formedness**, maintained across every operation: indices stay in
  bounds, chains are exactly the ghost sequences, rings close. The structure can
  never silently corrupt.

- **Non-aliasing / separation**, stated explicitly and proved: distinct lists
  share no node, the live ids of a sparse set are distinct, the class rings
  partition the arena. This is the guarantee `&mut` would have enforced for
  reference-based structures, recovered, by proof, for id-based ones, and
  *available as a predicate we can reason with* rather than an invisible
  property of the borrow graph.

- **Aliasing and cycles where we want them**, soundly: because the discipline is
  a proved invariant rather than a borrow-checker prohibition, we are free to
  build the mutually-indexed sparse set, the shared node arena, and the cyclic
  class-list, structures Rust references forbid, and still know they are
  correct.

In short, encoding references as arena ids deliberately discards the compiler's
structural guarantees in exchange for expressiveness, and the ghost-id-set /
dynamic-frames proof style buys those guarantees back, in stronger and more
explicit form, with Verus as the enforcing authority. For these containers that
is the whole point: the proof is not decoration on top of a structure the
compiler already blessed; it *is* the structure's only well-formedness
guarantee.

---
[Table of Contents](00-table-of-contents.md)
