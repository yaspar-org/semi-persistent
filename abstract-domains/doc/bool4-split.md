# Four-point boolean: split

Task 1's four-point boolean, from `interval-extensions.md` §2. Two people, two pieces. Piece A does not depend on intervals. Piece B uses the type from piece A and does not change its lattice.

## Piece A — the domain

Owner: implementation owner. Files: `src/bool4.rs`, `tests/bool4.rs`.

A boolean lattice has four points. The empty set is `BotOr::Bot`, outside the enum. `Bool4` itself is only the nonempty values:

| Value | Concrete booleans | Running example |
| --- | --- | --- |
| `BotOr::Bot` | none | impossible |
| `False` | `{false}` | false |
| `True` | `{true}` | true |
| `Top` | `{false, true}` | unknown |

There is no `Bottom` variant and no eight-point boolean. Every `Bool4` value contains `false` or `true`.

`not`, `and`, `or`, and `eq` are exact in both directions: every concrete input's result is in the abstract result, and every value of the result is produced by some concrete pair. `eq` is boolean equality. `meet(Top, True)` is `BotOr::Val(True)`. `meet(True, False)` is `BotOr::Bot`.

## Piece B — comparisons and backward narrowing

The forward comparisons were written on `ReducedProduct`. This base does not
have that type, so those comparisons are not part of this branch. Backward
narrowing remains future work. Piece B does not add a variant to `Bool4` and
does not change `join`, `meet`, `not`, `and`, `or`, or `eq`.
