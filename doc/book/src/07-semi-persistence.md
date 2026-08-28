# Semi-persistence: push and pop

> Chapter contents: what `push` and `pop` do, the undo-log mechanism the project is
> named for, what a scope costs, what `:shrink` trades, the `--push-pop clone`
> reference implementation, and the use Part IV makes of scopes.
>
> Sources: design `01-node-storage.md` and `02-classes-and-union-find.md` for the
> restorable containers, `05-egraph.md` for the token and restore order,
> `17-interpreter.md` for the commands.
>
> Example: write `examples/07-push-pop.egg`. Show a `push`, an assertion that makes
> two terms equal, a `check` that passes inside the scope, a `pop`, and a
> `(check (!= ...))` that passes after it, with `print-size` before and after so the
> reader sees the graph return to its previous size.
>
> Verify before writing: whether `pop` restores the node count exactly, or whether
> arena capacity stays and only the logical size returns. Say which. Do not claim
> the memory is returned unless `:shrink` was used.

## Opening and discarding a scope

> `(push)` and `(pop)`, with the example. State what is discarded: every insertion,
> union and rule application performed inside the scope. State what is not: anything
> printed, since output already happened.

## Why the pop is cheap

> The mechanism, at the level a user needs. Each mutation appends to an undo log and
> `pop` replays the log backwards, so a scope costs what was done inside it rather
> than the size of the graph it was opened on. Contrast with the alternative of
> copying the graph at `push`, which is what `--push-pop clone` does and what the
> `diff` implementation is differentially tested against.
>
> This is the property the project is named for. State it once, plainly, and do not
> return to it.

## `push :shrink`

> What it additionally releases and what it costs to do so. One paragraph.

## Nesting and lifetime

> Whether scopes nest, what happens to a `pop` with no matching `push`, and whether
> a `let`-bound name survives its scope. Verify each by running a program: this
> section is exactly the kind of thing that gets guessed at wrongly.

## Speculative assertion

> The use Part IV makes of this: push, assert one candidate reading of an ambiguous
> sentence, check what it implies, pop, and try the next reading, all on the same
> e-graph with the same saturated background facts. Say that chapter 19 does this and
> forward reference it. Keep this section to one paragraph and let chapter 19 show
> the program.
