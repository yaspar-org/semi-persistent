# calc: deviation ledger

Source: `egglog/tests/calc.egg` at 7b1adf2. Benchmark 6 of the intersection set,
paired with `until`: associativity-only group theory driven by `:until` goals over
four `push`/`run`/`check`/`pop` blocks.

Files: `calc.egglog.egg` (theirs), `calc.rules.egg` (ours, associativity as a
birewrite rule), `calc.native.egg` (ours, native A), this ledger.

The `:assoc` flattening defect this ledger reported is fixed (item 1 below is
withdrawn); the native file carries the source's nested terms unchanged.

`comparison/semi-persistence/calc.*.egg` is a different pair of files: E6's macro
exhibit, which needed only two configurations and whose `calc.native.egg` is in
fact the rules encoding. These files supersede it for E3/E4 purposes.

## Adjustments to the egglog original

1. Appended `(print-size)`, `(print-stats)` and
   `(print-stats :file "calc.egglog.stats.json")` for the harness.

No other change; the program is otherwise byte-identical to theirs.

## Deviations in the rules translation

1. **`(datatype G)` with no variants becomes `(sort G)`.** The separate
   `(constructor …)` declarations carry over unchanged. Pure surface syntax.
2. **Identifiers renamed into our lexical class**: `g*` becomes `gmul`, `$X`
   becomes `gX` (`$I` → `gI`, `$A` → `gA`, `$a` → `ga`). Pure renaming; the term
   structure is identical.

Nothing else changes: same rules, same four blocks, same `:until` goals, same
checks. All four checks pass.

## Deviations in the native translation

The group operation is associative and **not** commutative — the original has an
assoc birewrite and no commutativity rule — so `gmul` is declared `:assoc`, giving
sequence semantics, not `:assoc-comm`. Declaring AC would compare against a
strictly stronger system, the same reasoning as `eqsat-basic`'s `:comm`-only dual.

### 1. Withdrawn 2026-08-15: our `:assoc` did not flatten nested applications

The defect is fixed in `egraph/src/egraph.rs`, the file is back to the nested term
forms the source writes, and the extra singleton rule is gone. Do not cite this item
as a live deviation; it is kept because the pilot's first published numbers for this
benchmark were measured under it. Same shape as the withdrawn literal-matcher
workaround in `math-microbenchmark.deviations.md`.

What it said: `egraph/doc/design/ac-algebraic-properties.md` (lines 460 and 475)
specifies the A-operator normal form as a flattened sequence, and the engine did not
produce it. Reproduction:

```
;; TYPES: machine
(sort G)
(constructor Aa () G) (constructor Bb () G) (constructor Cc () G)
(constructor seq (G) G :assoc)
(let x1 (seq (seq (Aa) (Bb)) (Cc)))
(let x3 (seq (Aa) (Bb) (Cc)))
(check (= x1 x3))
```

```
error: check failed: terms are not equal
```

The same program with `:assoc-comm` instead of `:assoc` passed, so the defect was
specific to A-only operators; AC flattening was correct. A one-element node was not
collapsed either: `(seq (Aa))` and `(Aa)` were distinct classes under `:assoc`,
while `(bag (Zero) (A))` correctly reduces to `(A)` under `:assoc-comm`.

The two workarounds it forced, both now removed:

- **Every `gmul` term was written flat.** `(gmul gA2 gA2)` was written
  `(gmul gA gA gA gA)`, and so on — exactly the node a correct implementation
  builds from the nested form, so the program the engine ran was the intended one;
  what the workaround removed was the engine's obligation to normalize. The nested
  text now reproduces these files without change, and does.
- **The singleton law `(rewrite (gmul x) x)` was stated explicitly.** Without it the
  n-ary rules below stranded results such as `(gmul gI)` in a class of their own and
  block 4's check failed. It was not a rule of the source program, and it is no
  longer needed: `add` returns the element's class for a one-element sequence.

Both `:assoc` laws now run at build time (`egraph/doc/design/04-canonization.md`,
"A-Only Operators"). Fixing them removed one rule from this file, which is why the
native column's iteration count drops from 2 to 1 in the table below; the node count
is unchanged, since the flat sequences were what the workaround was writing by hand.

### 2. n-ary restatements

A binary pattern is an exact pattern against a flat sequence node and would stop
firing at length 3 or more, so the rules are restated with rest variables, per the
`math-microbenchmark` precedent. Only A operators take two rest variables (prefix
and suffix), which is what lets an interior pattern be expressed:

| theirs | ours, native |
|---|---|
| `(rewrite (gmul $I a) a)` and `(rewrite (gmul a $I) a)` | `(rewrite (gmul ..p gI ..s) (gmul ..p ..s))` |
| `(rewrite (gmul (inv a) a) $I)` | `(rewrite (gmul ..p (inv a) a ..s) (gmul ..p gI ..s))` |
| `(rewrite (gmul a (inv a)) $I)` | `(rewrite (gmul ..p a (inv a) ..s) (gmul ..p gI ..s))` |
| `(rewrite (gmul $A (gmul $A (gmul $A $A))) $I)` | `(rewrite (gmul ..p gA gA gA gA ..s) (gmul ..p gI ..s))` |

The two identity rules merge into one, which strictly generalizes both: an
identity element is deleted wherever it sits, not only at an end. The inverse
rules keep adjacency, which is the right reading — in a sequence, "adjacent after
re-association" and "adjacent in the flat sequence" are the same condition,
because A alone cannot reorder.

### 3. Blocks 1 and 2 become trivial, and that is the result

Under sequence semantics `(gmul gA4 gA4)` and `(gmul (gmul gA2 gA2) (gmul gA2 gA2))`
are the same eight-element node, as are block 2's two goal terms. Both `:until`
goals therefore hold before the run starts and both checks are true by
canonization. The blocks are written exactly as the source writes them — the two
sides of each check are textually the nested originals, and the engine flattens
them to one node on the way in. This is the same phenomenon as `math-add-ac`'s
native column saturating in one iteration at 25 nodes, and it is the value
proposition being measured, not a weakened check. Blocks 3 and 4, which need
inverse cancellation, still do real work.

## Cross-check

All four checks pass in all three configurations. Smoke pass (1 run, 0 warmups —
not a timing result):

| config | nodes | iterations |
|---|---|---|
| egglog | 5 | 4 |
| ours, rules | 8 | 1 |
| ours, native | 8 | 1 |

The node counts are the base state after the last `(pop)` and say nothing about
the work inside the blocks. The iteration counts are not comparable either: egglog's
stats file accumulates one entry per iteration across every `(run …)` in the
program, ours reports the last `(run …)` only. Both caveats apply to every
multi-block benchmark (`calc`, `until`, `herbie`) and are recorded in
`methodology.md` section 3.
