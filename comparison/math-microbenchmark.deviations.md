# math-microbenchmark: deviation ledger

Source: `egglog/tests/math-microbenchmark.egg` at 7b1adf2. Benchmark 1 of the
intersection set: 24 rewrite rules over a symbolic-differentiation signature, seven
seed terms, `(run 11)`, no primitives beyond an opaque `i64` tag and a `String` name.
Their own harness excludes it from proof mode as too heavy.

Files: `math-microbenchmark.egglog.egg` (theirs), `math-microbenchmark.rules.egg`
(ours, A/C as rewrite rules), `math-microbenchmark.native.egg` (ours, native AC).

## Adjustments to the egglog original

1. Appended `(print-stats :file "math-microbenchmark.egglog.stats.json")` for the
   harness. The original's `(print-size Add)`, `(print-size Mul)`, `(print-size)` and
   `(print-stats)` are untouched.

No other change; the program is otherwise byte-identical to theirs.

## Deviations in the rules translation

1. **Primitive handling: none needed.** The benchmark has no primitive *operations*:
   `Const` wraps an `i64` that is never added, compared, or folded, and `Var` wraps a
   `String` used only as a name. Running under `--types machine` puts both sorts in
   scope and the datatype is copied verbatim, so no substitution is made at all. The
   alternative the plan floated (a plain sort with nullary constructors, or `IBig`
   literals) was rejected: replacing `i64` with `IBig` would run the same program with a
   heavier literal representation and no semantic gain, and nullary constructors would
   change the signature. Note that our `bignum` type group has no `String` sort, so
   `machine` is also the only single group that types this program as written.
2. **Statistics.** `(print-stats)` becomes `(print-stats :file "…")`. The three
   `print-size` commands and their positions are kept.

3. **Withdrawn 2026-08-15. Six left-hand sides used let-bound globals**, to work around
   the engine defect below. The defect is fixed, the six rules are back to the literal
   form egglog writes, and the shipped files carry no globals. Do not cite this item as a
   live deviation; it is kept because the pilot's first published numbers were measured
   under it. What it said: `(rewrite (Add a (Const 0)) a)` was written
   `(rewrite (Add a c0) a)` after `(let c0 (Const 0))`, and likewise for
   `(Mul a (Const 0))`, `(Mul a (Const 1))`, `(Pow x (Const 1))`, `(Pow x (Const 2))` and
   `(Integral (Const 1) x)` with `c0`, `c1`, `c2`. Right-hand sides kept the literal form.
   The substitution was sound, because a global in a pattern position means "the child at
   this position is in the same e-class as this binding", which is the reading of the
   ground sub-pattern. Its one side effect was that the three `(let …)` commands inserted
   `(Const 0)`, `(Const 1)` and `(Const 2)` before the run. `(Const 1)` and `(Const 2)`
   are in the seed terms anyway; `(Const 0)` is not, and at this budget the run never
   builds it, so removing the workaround removes exactly two nodes and two classes from
   each configuration's totals. The tables below are the post-fix numbers.

Everything else is copied verbatim: all 24 rules, all seven seed terms, `(run 11)`.
No rule dropped, no check weakened (the benchmark has no checks), no schedule change.

## Engine defect found while translating: ground literal sub-patterns never match (fixed)

Fixed 2026-08-15 in `egraph/src/schedule.rs` and `egraph/src/resolve.rs`; the description
below is the state at the time of translation, kept because it is what the workaround
above was written against.

A concrete literal written inside a rule's left-hand side does not match. The whole of it:

```
(datatype Math (Add Math Math) (Const i64) (Var String))
(rewrite (Add a (Const 0)) a)
(Add (Var "p") (Const 0))
(run 5)
(check (= (Add (Var "p") (Const 0)) (Var "p")))    ;; fails on our engine, passes on egglog
```

Three probes bound the defect. Replacing `(Const 0)` with a nullary constructor `(Zero)`
matches. Binding the literal to a pattern variable, `(Add a (Const k))`, matches. Naming
the same ground term with `(let z (Const 0))` and writing `(Add a z)` matches. So the
failure is specific to a literal appearing as a concrete value inside an LHS pattern:
either the literal is not interned when the pattern is compiled, or the compiled atom
does not constrain the child to the literal's class.

Six of this benchmark's 24 rules are written that way, so before the workaround they were
dead in both of our configurations while live in egglog's. The effect on this benchmark's
totals is small, because at a budget of 11 iterations egglog's own statistics report those
six rules matching 0, 0, 0, 0, 1 and 0 times; the node count moved from 1 234 182 to
1 234 680 in the rules encoding and from 755 925 to 755 928 in the native one. The defect
is recorded here because it is a correctness bug in the matcher, not a benchmarking
detail, and because any translated program that folds constants by pattern will hit it.

**Cause and fix.** The third guess was the right one: the compiled atom did not constrain
the child. `resolve` turned a pattern literal into an `RAtom::Lit` carrying the literal's
sort and value but not the `@sort` constructor that owns the literal nodes, so the
scheduler had no key to look the atom up by and emitted `Step::Join { lookups: [] }` from
`schedule::emit_atom` and `schedule::try_eager_lower`. An empty lookup list makes both
matcher engines abandon the query (`ematch::run_join` returns before binding anything, and
`MatchIterator::enter_join` reports failure), and because the scheduler estimated that atom's
cardinality at 1 it ran first, so the rule produced no matches at all rather than too
many. The fix carries the `@sort` op in `RAtom::Lit` and lowers the atom the way
`RAtom::LitBind` is already lowered: join `by_op[@sort]`, then a new `Step::CheckLit` that
keeps the candidate only if its payload equals the pattern's value. The atom is now a
scanning position, so `saturate::atom_op` reports its op and semi-naive gives it a
variant. Regression tests: `egraph/tests/egg/lit_pattern_*.egg` and
`schedule::tests::literal_atom_joins_and_checks_payload`.

**Equivalence check on this benchmark.** Rewriting the six rules back to literals and
keeping the three `(let …)` commands reproduces the workaround's run exactly: 1 234 680
nodes, 506 565 classes, 11 iterations in the rules encoding, and 755 928 / 446 917 / 11 in
the native one, the same totals the globals produced. Dropping the `(let …)` commands as
well, which is what the shipped files now do, subtracts the two nodes and two classes
those commands inserted: 1 234 678 / 506 563 and 755 926 / 446 915, iterations unchanged.
Wall time is unchanged within run-to-run spread (11 597 ms against 11 642 ms for the rules
encoding, 1 097 ms against 1 136 ms for the native one), and match steps move by 0.0003%,
because the literal atom now costs a join and a payload check where the global cost an
equality check. The identical totals under identical seeding are the semantic statement:
a ground literal in a pattern derives the same e-graph as the let-bound global that stood
in for it.

## Deviations specific to the native configuration

This is the benchmark where the native dual is not a deletion. `Add` and `Mul` are
declared `(Add Math :assoc-comm)` and `(Mul Math :assoc-comm)`, variadic with one element
sort, and the four A/C rules are deleted. But eleven of the remaining rules match an
`Add` or a `Mul`, and a binary pattern against a variadic AC operator is an *exact*
pattern: `(Add a (Const 0))` matches a node whose multiset has total multiplicity two,
and never matches the flat node `+{a, b, Const 0}`. Our matcher does not bind a scalar
variable to a virtual sub-sum, because that is AC unification, which we do not do
(see `egraph/doc/design/ac-congruence-completeness.md` §5b).

So a literal "delete the A/C rules, keep everything else" native file would be **strictly
weaker** than the rules encoding: the identity, annihilator, distribution, factoring,
power, differentiation, and integration rules would all silently stop firing on flat
nodes of arity three or more. Its wall time would be fast and meaningless. That variant
is not shipped.

Instead each affected rule is restated in its n-ary form, using the rest-variable idiom
that the same document identifies as the shape native AC rules are expected to take
(§5b case (a): sub-multisets reachable by pulling elements out of the matched multiset
are enumerated). The eleven restatements:

| rules encoding | native encoding | shape |
|---|---|---|
| `(Add a (Const 0))` → `a` | `(Add (Const 0) ..rest)` → `(Add ..rest)` | drop the unit from any sum |
| `(Mul a (Const 0))` → `(Const 0)` | `(Mul (Const 0) ..rest)` → `(Const 0)` | annihilate any product |
| `(Mul a (Const 1))` → `a` | `(Mul (Const 1) ..rest)` → `(Mul ..rest)` | drop the unit from any product |
| `(Mul a (Add b c))` → `(Add (Mul a b) (Mul a c))` | `(Mul (Add b ..s) ..rest)` → `(Add (Mul b ..rest) (Mul (Add ..s) ..rest))` | distribute by peeling one summand |
| `(Add (Mul a b) (Mul a c))` → `(Mul a (Add b c))` | `(Add (Mul a ..p) (Mul a ..q) ..rest)` → `(Add (Mul a (Add (Mul ..p) (Mul ..q))) ..rest)` | factor two summands of any sum |
| `(Mul (Pow a b) (Pow a c))` → `(Pow a (Add b c))` | `(Mul (Pow a b) (Pow a c) ..rest)` → `(Mul (Pow a (Add b c)) ..rest)` | combine two factors of any product |
| `(Diff x (Add a b))` | `(Diff x (Add a ..s))` → `(Add (Diff x a) (Diff x (Add ..s)))` | sum rule by peeling |
| `(Diff x (Mul a b))` | `(Diff x (Mul a ..s))` → `(Add (Mul a (Diff x (Mul ..s))) (Mul (Mul ..s) (Diff x a)))` | product rule by peeling |
| `(Integral (Add f g) x)` | `(Integral (Add f ..s) x)` → `(Add (Integral f x) (Integral (Add ..s) x))` | sum rule by peeling |
| `(Integral (Mul a b) x)` | `(Integral (Mul a ..s) x)` → `(Sub (Mul a (Integral (Mul ..s) x)) (Integral (Mul (Diff x a) (Integral (Mul ..s) x)) x))` | integration by parts, peeling |
| `(Pow x (Const 2))` → `(Mul x x)` | unchanged | RHS builds the multiset `{x:2}` |

The first three lines were written with the globals `c0` and `c1` until 2026-08-15, for
the same defect workaround the rules configuration needed: `(Add c0 ..rest)`,
`(Mul c0 ..rest)`, `(Mul c1 ..rest)`. The shipped file now carries the literal form the
table shows, which also exercises a literal in an AC element position.

Each restatement degenerates to the original binary rule when the rest variable binds a
single element, and a one-element AC node collapses to that element (verified: with
`(rewrite (Add (z) ..rest) (Add ..rest))`, `(Add (a) (z))` becomes `(a)`). The peeling
forms are recursive rather than closed-form (a comprehension over the whole rest was not
attempted), which means they generate the intermediate sub-products and sub-sums
explicitly; that cost shows up in the node counts below.

**These restatements are the deviation to weigh.** They are not the same rule set as
egglog's. They are the *n-ary generalizations* of egglog's rules: each one derives every
consequence the binary rule derives on the corresponding flat node, and no more. The
alternative readings are both worse: the literal deletion is strictly weaker (above), and
keeping the A/C rules alongside a native AC operator would double-encode the same
property. Read the native column as "the same mathematics stated for variadic operators",
not as "the same program".

Three rules mention `Add`/`Mul` only on the right-hand side and are copied verbatim:
`(Sub a b)` → `(Add a (Mul (Const -1) b))`, `(Diff x (Cos x))` → `(Mul (Const -1) (Sin x))`,
`(Integral (Sin x) x)` → `(Mul (Const -1) (Cos x))`. The `Div`, `Pow`, `Ln`, `Sqrt`, `Sin`,
`Cos`, `Sub`, `Diff` and `Integral` operators stay plain; the commented-out `Div` rule
stays commented out; all seven seed terms and `(run 11)` are unchanged.

## Semantic cross-check

The benchmark ships no `(check …)` commands, so the cross-check was constructed: seed
`(Mul (Add (Var "p") (Var "q")) (Var "r"))` and `(Add (Mul (Var "q") (Var "p")) (Const 0))`
before the run, and assert after it that the first equals
`(Add (Mul (Var "p") (Var "r")) (Mul (Var "q") (Var "r")))` (distribution modulo
commutativity, which needs the AC treatment to be right in every configuration) and that
the second equals `(Mul (Var "p") (Var "q"))` (the additive identity, which is one of the
six rules the defect above had killed). **Both assertions pass in all three
configurations.** The seeded variants are scratch files, not committed: adding a seed term
changes the program being timed.

What is comparable in the timed programs is the shape of the search at the shared budget
of 11 iterations, which all five configurations reach without saturating.

| | egglog | ours, rules (naive) | ours, native (naive) |
|---|---|---|---|
| total | 1 047 896 | 1 234 678 | 755 926 |
| classes | not reported | 506 563 | 446 915 |
| iterations | 11 | 11 | 11 |
| median wall time | 508 ms | 11 562 ms | 1 118 ms |

Our two node counts each dropped by 2 on 2026-08-15, when the ground-literal workaround
was withdrawn and its three `(let …)` commands with it. The wall times are the pilot's
medians, taken under the workaround; the post-fix single runs land inside their spread
(11 597 ms and 1 097 ms), so they are not restated here. Re-run `run-pilot.py` to refresh
the medians.

Per operator, in the same three configurations (the counts below predate the global-constant
workaround by at most a few hundred nodes; the totals above are the current ones):

| | egglog | ours, rules | ours, native |
|---|---|---|---|
| Add | 641 743 | 805 156 | 257 467 |
| Mul | 345 075 | 366 032 | 311 323 |
| Integral | 32 434 | 33 078 | 106 991 |
| Sub | 15 123 | 15 800 | 51 538 |
| Diff | 13 504 | 14 091 | 28 581 |
| Const / Var / Div / Pow / Ln / Sqrt / Sin / Cos | 17 | 17 | 17 |
| match steps | not reported | 219 865 470 | 3 073 653 |

Reading the differences:

- **egglog vs. our rules encoding (1.05 M vs. 1.23 M nodes, +18%; 508 ms vs. 11 562 ms, 22.7x).** Same rules, same budget,
  same iteration count. Part of the gap is the canonical-tuples vs. stored-nodes accounting
  difference documented in `eqsat-basic.deviations.md`: egglog reports table cardinality after
  rebuild, we report stored nodes including those that congruence later made duplicates.
  The rest is that neither engine has saturated at 11 iterations, so the frontier reached
  depends on the order rules fire and rebuild runs within an iteration. This is a
  legitimate difference in intermediate state, not a difference in derived equalities.
  The wall-time gap is not explained by the node gap: 18% more nodes does not cost 22.7x
  more time. On the same program with the same rules, their matcher is roughly an order
  of magnitude faster than ours, and our 220 M match steps are the place to look. This is
  the pilot's main negative result and the reason the full benchmark set matters.
- **Our rules vs. our native (1.23 M vs. 0.76 M nodes; 11 562 ms vs. 1 118 ms, 10.3x).** `Add` drops 3.1x, because one AC node
  replaces the whole orbit of re-associations and re-orderings of a sum. `Integral`,
  `Sub` and `Diff` go *up* 2-3x, because the peeling forms of the sum, product and
  parts rules materialize sub-sums and sub-products that the binary rules never name.
  The net is 39% fewer nodes and, more sharply, **72x fewer match steps** (3.1 M vs.
  220 M): the AC node is matched once where the rules encoding matches every
  rearrangement of it.
- **Our two strategies.** Semi-naive and naive agree to within 1.4% on node count in the
  rules encoding (1 234 678 vs. 1 251 191) and to 9 nodes in the native encoding, and cost
  the same in the rules encoding (11 562 ms naive, 11 299 ms semi-naive). Under native AC
  they diverge sharply: 1 118 ms naive against 15 539 ms semi-naive, 13.9x, for the same
  final e-graph. Semi-naive delta tracking over variadic AC nodes is the suspect; that is a
  hypothesis, not a measurement, and it wants its own experiment.

## Verdict

Kept, with the n-ary restatement recorded as a first-class deviation. The rules
configuration is a faithful transcription of egglog's program and is directly comparable
to it. The native configuration is *not* the same rule set and its wall time should be
read as "what this problem costs when the algebra is native", not as a same-program
speedup.

## Coincidence twins (2026-08-17)

Partition semantics (see `integer_math.deviations.md`, same date): five `:k>=2`
twins are added, one each for the factoring rule (`k` reinserted as a `Const`
factor) and the Pow-product rule (`(a^b)^k = a^(b*k)`), and one per identity
(`0+`, `0*`, `1*`) because this file has no constant fold to normalize a
repeated 0 or 1 down to multiplicity 1. Residual: the distributivity rule
cannot keep `k-1` copies of its matched Add child on the RHS, so a repeated
Add factor (`(x+y)^2 * z`) still distributes only through other paths;
verified latent, all checks pass. Re-validated after the change: node counts
identical to the campaign under both strategies (755 926 / 755 917), so the
twins fire zero times on this workload and the numbers stand.
