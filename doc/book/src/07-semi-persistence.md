# Semi-persistence: push and pop

This chapter defines `push` and `pop`, explains their sparse restoration
mechanism and capacity behavior, and shows nesting, scoped names, and
speculative use.

## Opening and discarding a scope

`(push)` records the current logical state. `(pop)` restores the most recent
recorded state, discarding insertions, unions, and rule effects performed
inside the scope.

```lisp
{{#include ../examples/07-push-pop.egg:push-pop}}
```

Before the first push, `a`, `b`, `f(a)`, and `f(b)` account for four e-nodes.
The union inside the outer scope makes `left` and `right` equal. The nested
scope then adds one `g` node, so its `print-size` reports five nodes:

```text
a: 1
b: 1
f: 2
g: 1
total: 5
```

Popping the nested scope removes the `g` node but preserves the outer scope's
union. Popping the outer scope removes that union. The final disequality check
passes, and the last `print-size` reports the original four nodes:

```text
a: 1
b: 1
f: 2
total: 4
```

Rules installed inside a scope and `let` bindings created there are also
discarded. Output is not reversible: text printed before a `pop` remains in
the process output.

## Why the pop is cheap

Semper uses semi-persistent containers instead of copying the complete e-graph
at every push. Append-only arenas record their logical lengths and truncate
new suffixes on restore. Mutable arrays, including union-find parent arrays,
capture a slot's previous value the first time that slot changes in a scope.
Restore replays those sparse differences and restores the saved lengths.

Hash-consing tables and other derived indexes are not themselves the logical
state. On restore, a node cache removes or repairs entries affected by the
discarded suffix and by recanonized nodes. It reconstructs the table when that
is cheaper than incremental repair. Saturation's matching indexes have
round-local lifetimes and are built again when needed.

Push therefore records coordinated container tokens rather than cloning all
nodes and classes. Its exact work includes frame and capture bookkeeping, and
pop work depends on changes made since the mark, discarded suffixes, and cache
repair. The project name refers to this semi-persistent representation.

The command-line mode is `--push-pop diff`, and it is the default.

## `push :shrink`

Plain `(push)` preserves allocation capacity even though a later `(pop)`
restores the logical lengths. Reusing that capacity avoids reallocating when
the next branch grows to a similar size. `print-size` reports logical e-nodes,
so it cannot show retained capacity.

`(push :shrink)` conditionally reclaims excess container capacity before
recording the mark. The current interpreter requests shrinking when capacity
is more than four times logical length plus a small headroom. Shrinking can
move live storage and add work to `push`; `pop` does not perform another
shrink. The option does not promise that every allocation is returned.

```lisp
{{#include ../examples/07-push-pop.egg:push-shrink}}
```

## Nesting and lifetime

Scopes nest in last-in, first-out order. In the main example, the first `pop`
discards only `nested`; the equality created in the outer scope remains until
the second `pop`.

A `pop` with no matching `push` is a runtime error:

```lisp
{{#include ../examples/07-pop-without-push.egg:pop-without-push}}
```

The interpreter reports `pop without matching push`.

`let` introduces a runtime global name. A binding created inside a pushed
scope is unavailable after its matching pop:

```lisp
{{#include ../examples/07-scoped-name-error.egg:scoped-name-error}}
```

This program is rejected during whole-program sortchecking because `scoped`
is no longer in the global-name environment at the final check. If an inner
`let` shadows an outer name, popping restores the outer binding:

```lisp
{{#include ../examples/07-push-pop.egg:shadowed-global}}
```

Sort and operator declarations are different. Semper sortchecks the complete
program before interpretation and registers declarations in source order, so
`push` and `pop` do not give declarations a runtime lifetime. Installed rules,
runtime `let` bindings, e-nodes, and equalities are scoped.

## Speculative assertion

Scopes support repeated speculative checks over one shared background graph.
A program can saturate its background facts, push, assert one candidate
formalization, inspect the equalities it implies, and pop before trying the
next candidate. Chapter 19 applies this sequence to alternative explanations
of differences between autoformalization clusters.

The exact restore order and cache repair are specified in the design chapters
for the
[e-graph](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/05-egraph.md)
and
[interpreter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/17-interpreter.md).
