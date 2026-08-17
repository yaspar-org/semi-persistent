# calc: deviation ledger

Source: `egglog/tests/calc.egg` at 7b1adf2. Benchmark 6 of the intersection set,
paired with `until`: associativity-only group theory driven by `:until` goals over
four `push`/`run`/`check`/`pop` blocks.

Files: `calc.egglog.egg` (theirs), `calc.rules.egg` (ours, associativity as a
birewrite rule), `calc.native.egg` (ours, native A), this ledger.

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

### 1. Load-bearing: our `:assoc` does not flatten nested applications

`egraph/doc/design/ac-algebraic-properties.md` (lines 460 and 475) specifies the
A-operator normal form as a flattened sequence. The engine does not produce it.
Reproduction:

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

The same program with `:assoc-comm` instead of `:assoc` passes, so the defect is
specific to A-only operators; AC flattening is correct. A one-element node is not
collapsed either: `(seq (Aa))` and `(Aa)` are distinct classes under `:assoc`,
while `(bag (Zero) (A))` correctly reduces to `(A)` under `:assoc-comm`.

Two consequences for this file, both stated rather than corrected, because the fix
is in `egraph/src` and outside this directory's scope:

- **Every `gmul` term is written flat.** `(gmul gA2 gA2)` is written
  `(gmul gA gA gA gA)`, and so on. This is exactly the node a correct
  implementation would have built from the nested form, so the program the engine
  runs is the intended one; what the workaround removes is the engine's obligation
  to normalize. When `:assoc` flattens, the nested text reproduces these files
  without change. Same shape as the withdrawn literal-matcher workaround in
  `math-microbenchmark.deviations.md`.
- **The singleton law `(rewrite (gmul x) x)` is stated explicitly.** Without it
  the n-ary rules below strand results such as `(gmul gI)` in a class of their
  own and block 4's check fails. It is not a rule of the source program.

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
canonization. The files state them in the flat form, so they read as
`(check (= X X))`; the nested originals are in the block comments. This is the
same phenomenon as `math-add-ac`'s native column saturating in one iteration at 25
nodes, and it is the value proposition being measured, not a weakened check.
Blocks 3 and 4, which need inverse cancellation, still do real work.

## Cross-check

All four checks pass in all three configurations. Smoke pass (1 run, 0 warmups —
not a timing result):

| config | nodes | iterations |
|---|---|---|
| egglog | 5 | 4 |
| ours, rules | 8 | 1 |
| ours, native | 8 | 2 |

The node counts are the base state after the last `(pop)` and say nothing about
the work inside the blocks. The iteration counts are not comparable either: egglog's
stats file accumulates one entry per iteration across every `(run …)` in the
program, ours reports the last `(run …)` only. Both caveats apply to every
multi-block benchmark (`calc`, `until`, `herbie`) and are recorded in
`methodology.md` section 3.
