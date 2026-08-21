# repro-herbie-vanilla: dropped, with corrected premises

Source: `egglog/tests/repro-herbie-vanilla.egg` at 7b1adf2. It had been
described as "471 rewrites, same signature and same analysis as herbie" and
ranked behind herbie's native encoding in `herbie.deviations.md`. Both
descriptions are wrong at the pinned commit, and
the correction is what decides the drop.

## What the file actually is

3,374 lines, no `push`/`pop`, no checks. It is a minimized reproduction of an
unsoundness bug in typed lowering, not a simplification benchmark:

- Ten-odd precision-specialized datatypes (`Num_sym_binary64`,
  `Var_arr_3_sym_binary32`, ...) beside the source `M` datatype, every
  constructor carrying `:cost 4294967295`.
- 165 `(rule ...)` forms lowering `M` terms into the typed datatypes through
  `(constructor do-lower (M String) MTy :unextractable)` and lifting back.
- One 45-let rule in a `run-extract-commands` ruleset that builds the single
  input expression, run once via `(run-schedule (repeat 1 ...))`.
- A `(function bad-merge? () bool :merge (or old new))` lattice flag whose
  ruleset detects merges across differently-typed lowered terms - the bug the
  repro exists to catch.
- The schedule
  `(run-schedule (repeat 3 (seq (run rewrite) (run const-fold) (run bad-merge-rule :until (bad-merge?)))))`
  followed by `(saturate unsound)` and `(saturate lower)`.
- The 471 `(rewrite ...)` forms are herbie's `rewrite`/`const-fold` rulesets
  plus per-precision duplicates of the lowering equations, not 2.9x the
  simplify layer.

## Why it is dropped rather than translated

Three blockers, each individually sufficient under the methodology's
drop-don't-fudge rule:

1. **No oracle.** The file asserts nothing: no checks, no extraction whose
   output is compared. The intersection-set discipline exists so that a
   passing check certifies both engines solved the same problem; with no
   checks, a 3,000-line hand translation would produce a time-only comparison
   with no evidence the two programs agree, which section 3 of
   `methodology.md` rules out as a basis for claims.
2. **Lattice function in the driving loop.** `bad-merge?` is a `:merge`
   lattice function and its `:until (bad-merge?)` guard is the schedule's
   stopping condition. Lattice functions are documented as outside the
   intersection set (herbie's own interval analysis was stripped for the same
   reason); here the lattice is not an optional analysis but part of the
   harness.
3. **Schedule composition.** `run-schedule` with `seq`, `repeat`, `saturate`
   and a function-valued `:until` has no counterpart in our run forms
   (`(run [ruleset] N [:until goal-facts])`). The `repeat 3 (seq ...)` phase
   could be paraphrased as interleaved single-iteration runs, but the
   paraphrase plus the dropped lattice guard is a different program, and with
   blocker 1 there is no oracle to certify the paraphrase.

## Postponed, with hypothesis

The file becomes translatable if the comparison ever needs it, in this order:
strip the `bad-merge?` machinery (behavior-neutral on a post-fix egglog,
where the flag never fires - an assumption that must be checked against their
run, not assumed silently), paraphrase the schedule as explicit interleaved
runs, translate the lowering rules mechanically (root-binding and constructor
support both exist since 93d698d and the E1 work), and use within-engine
rules-vs-native node-count equivalence as the internal oracle in place of the
missing checks. That yields an our-side-only benchmark; the cross-engine
column would remain time-only and should be labeled as such. None of this is
scheduled: the herbie benchmark already covers the simplify layer with a real
oracle, and this file's distinctive content - typed lowering at scale - is
machinery we do not claim to cover.
