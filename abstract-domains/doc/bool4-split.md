# Four-point boolean: split

Task 1's four-point boolean, from `interval-extensions.md` §2. Two people, two pieces. Piece A does not depend on intervals. Piece B uses the type from piece A and does not change its lattice.

## Piece A — the domain

Owner: implementation owner. Files: `src/bool4.rs`, `tests/bool4.rs`.

`Bool4 = Bottom | False | True | Top`.

| Value | Concrete booleans | Running example |
| --- | --- | --- |
| `Bottom` | none | impossible |
| `False` | `{false}` | false |
| `True` | `{true}` | true |
| `Top` | `{false, true}` | unknown |

Implement and prove:

- canonical `bottom`, `top`, and concrete-boolean `constant` constructors
- `has`, and `refines` as subset of `has`
- `join`, `meet`, `not`, `and`, `or`, each with containment: every concrete input's concrete result is in the abstract result
- §3.5 for `meet` and `join`: idempotent, commutative, associative, units, zeros
- monotonicity of `not`, `and`, and `or` in the refined argument

`meet(Top, True) = True` is the running example's `(union c (True))`. `meet(True, False) = Bottom`. Bottom contains neither boolean.

## Piece B — comparisons and backward narrowing

The forward comparisons were written on `ReducedProduct`. This base does not
have that type, so those comparisons are not part of this branch. Backward
narrowing remains future work.
