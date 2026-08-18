# subsume: deviation ledger

Source: `egglog/tests/web-demo/subsume.egg` at 7b1adf2. A `:subsume` rewrite
replaces multiplication by three with three additions; the benchmark's point
is that the subsumed multiplication is excluded from later matching and from
extraction.

Files: `subsume.egglog.egg` (theirs, verbatim), `subsume.rules.egg` (a
BLOCKED carrier that runs but diverges on extraction), this ledger.

**Blocked on subsume-extraction semantics.** Measured on the same program:
both engines pass both checks, egglog extracts
`(Mul (Num 2) (Add (Var "x") (Add (Var "x") (Var "x"))))` before and after
the added commutativity rule, and we extract
`(Mul (Num 2) (Mul (Num 3) (Var "x")))` both times. Our subsume excludes the
node from future matches, which the second run confirms (commutativity does
not resurrect the form), but the node stays extractable. The condition that
unblocks the benchmark is extraction skipping subsumed nodes; the validation
that then applies is extraction agreement on both extracts.
