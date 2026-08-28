# Design documents

This book is the user-facing extract. The design documentation is a separate
body of work: it specifies the data structures, the algorithms and the soundness
arguments, and it is written for somebody changing the engine rather than using
it.

It lives in
[`egraph/doc/design/`](https://github.com/yaspar-org/semi-persistent/tree/main/egraph/doc/design)
and its own table of contents is
[`00-table-of-contents.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/00-table-of-contents.md).

## The ones this book leans on

| document | what it specifies |
| --- | --- |
| [`19-anti-unification.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md) | the solvers, the cost model, the three cycle policies, the exactness certificate |
| [`ac-algebraic-properties.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-algebraic-properties.md) | what each declaration means and which combinations are legal |
| [`04-canonization.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/04-canonization.md) | how AC and ACI children are normalized, which is why order and repetition cost nothing |
| [`A1-language-guide.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/A1-language-guide.md) | the full surface language, including the variadic pattern and comprehension syntax this book only mentions |
| [`ac-congruence-completeness.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-congruence-completeness.md) | the gap between AC matching completeness and AC congruence completeness, which is what `--derive-ac-eqs` addresses |
| [`14-soundness.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/14-soundness.md) | what the engine claims to prove and what it does not |

## The rest of the map

- **Representation.** `01-node-storage`, `02-classes-and-union-find`,
  `03-hash-consing-caches`, `05-egraph`, `13-literal-model`.
- **Matching and evaluation.** `06-index`, `07-leapfrog`,
  `08-query-compilation`, `09-pattern-matching`, `12-rule-application`,
  `18-semi-naive-evaluation`, `20-index-selectivity-and-delta-suffixes`.
- **Front end.** `10-surface-language`, `11-sortcheck-and-resolution`,
  `17-interpreter`.
- **Output.** `15-proof-logging`, `16-extraction`.
- **Orientation.** `A0-overview` for why semi-persistence, `A2-developer-guide`
  for working on the engine, `A3-future-work` for what is not built.

## Other reading in the repository

- [`autoformalization/README.md`](https://github.com/yaspar-org/semi-persistent/blob/main/autoformalization/README.md)
  is the full record behind [chapter 9](09-corpus.md): the generator, the runner,
  the hybrid-divisor sweep, and the metamorphic corpus.
- The `containers-verus` crate carries its own proof documentation. It is the
  verified container layer underneath the engine and is independent of anything
  in this book.
