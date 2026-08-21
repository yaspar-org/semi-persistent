# array: deviation ledger

Source: `egglog/tests/web-demo/array.egg` at 7b1adf2, the SMT-LIB theory of
arrays: select-over-store with disequality-guarded read-past-write rules.

Files: `array.egglog.egg` (theirs, verbatim), `array.rules.egg` (a BLOCKED
carrier, not runnable), this ledger.

**Blocked on relations.** The `neq` relation is load-bearing: its facts are
derived by injectivity rules and consumed as guards by the select-over-store
rules, and a relation fact is not an e-class our `:when` can express. The
carrier translates the literal-op qualifications and keeps every
relation-dependent form in source syntax. The condition that unblocks it is
datalog relations as rule atoms; the validation that then applies is the
source's own checks run on both engines.

The `panic` action in the `(neq x x)` consistency rule is also outside our
action set; it falls with the same feature.
