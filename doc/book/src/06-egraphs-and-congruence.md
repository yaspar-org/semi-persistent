# E-nodes, e-classes, congruence

> Chapter contents: what an e-graph stores, the two structures it is made of, what
> congruence closure adds to a union, what rebuild is for, and what
> `(check (= t1 t2))` is actually asking. This is the chapter that lets a reader
> stop guessing at the model, and everything in Parts II to IV is stated in its
> vocabulary.
>
> Sources: design `01-node-storage.md`, `02-classes-and-union-find.md`,
> `03-hash-consing-caches.md`, `05-egraph.md`.
>
> Example: write `examples/06-congruence.egg`. It needs to show, with `print-size`
> and `check`, that one `union` of two arguments makes two parent terms equal
> without any rule firing.
>
> Nothing in this chapter is new material for the project: it is the standard model,
> written for a reader who has not met it. Keep it to five pages and resist
> restating design chapter 05.

## E-nodes and e-classes

An **e-node** is an operator together with references to its argument
e-classes. An **e-class** is a collection of e-nodes that Semper currently
knows to be equal.

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
A term is therefore not retained as one tree. Once a child class acquires
additional members, the same parent e-node represents every equal term in that
class at that argument position. After insertion there is no unique stored
syntax tree that `left` names; `left` names the resulting e-class.

## Hash-consing

> Inserting a term that is already present returns the existing class rather than
> adding a node. Show the node count staying flat across a duplicate insertion.
> State the identity of an e-node: operator plus canonical argument classes.

## Union-find

> How classes are merged and what "canonical" means for a class identifier. State
> that a merge is not a rewrite: nothing is deleted and no representative choice
> changes what is equal, which is why `--union-by` changes work and printed
> representatives and not the equalities. Link Annex C.

## Congruence

> The rule that makes it a congruence closure: equal arguments make equal
> applications. Show the case where the reader can see it, namely `union` on two
> arguments causing two parents to be equal with no rule involved. Quote the
> `check` that passes.
>
> State what this buys: a rule that fires once relates every term built over the
> merged class, which is the reason equality saturation scales to term sets a
> rewriting engine would enumerate.

## Rebuild

> Why a merge leaves the graph temporarily out of congruence and what rebuild
> restores. Keep it to what a user can observe: rebuild happens before matching, so
> a rule never sees a half-merged graph, and node counts printed between commands are
> counts after rebuild. Point at design chapter 05 for the algorithm and say that
> canonization runs here, which is where chapter 10 picks up.

## What an equality check asks

> `(check (= t1 t2))` inserts both terms and asks whether they are in one class.
> State the two consequences carefully, because Part IV depends on both: an equality
> holds only if the declared rules and the declared algebra derived it, and a
> negative answer is a statement about the engine's current knowledge. Forward
> reference chapter 11 for what a negative answer means under each congruence mode.
