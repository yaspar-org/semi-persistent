# Tutorial

The canonical tutorial is now
[`tests/testorial.rs`](tests/testorial.rs) — a set of
worked chapters, each covering one recursion scheme or technique on a
small imperative language. Each chapter is a standalone `#[test]`, so you
can step through them in your editor and run them individually.

## Chapter index

| Ch | What | Scheme |
|----|------|--------|
|  0 | The Language | `rec_family!` |
|  1 | Pretty Print + Size | `fold` (multi-sorted) |
|  2 | Constant Folding | `rewrite` |
|  3 | Double Negation | `rewrite` |
|  4 | Find Variable | `fold_short` |
|  5 | Build from Seed | `unfold` |
|  6 | Build with Reuse | `unfold_short` |
|  8 | Desugar While | `rewrite` |
|  9 | Type Inference | `fold` |
| 10 | Interpreter | `fold` |
| 11 | Free Variables | `fold` |
| 12 | Precedence Print | `fold` |
| 13 | Depth Complexity | `fold_with_history` |
| 14 | Type Check + Eval | `fold_with_aux` |
| 15 | Saturating Eval | `fold_pair` |
| 16 | Simplify Before Eval | `prefold` |
| 17 | Canonicalize Build | `postunfold` |
| 19 | Top-Down Desugar | `rewrite_down` |
| 20 | Cost Model | `fold_with_original` |
| 21 | Dead Code Search | `fold_short` |
| 22 | Desugar Then Eval | `prefold` |
| 23 | Bytecode Compiler | `fold` |
| 24 | Zipper: Find Binder | `Zipper` |
| 25 | Zipper: Patch Node | `ZipperMut` |
| 26 | Zipper: Specialize | `ZipperCow` |

## Other docs

- [README.md](README.md) — quick-start example and overview.
- [doc/design/memo-and-dedup.md](doc/design/memo-and-dedup.md) — decision
  guide for memo strategy and hash-consing, with benchmark numbers.
- [tests/family.rs](tests/family.rs) — smaller structural tests
  for the macro output (variadic pools, dedup semantics, mark/restore).
