# Writing brief

Read this before writing any chapter. It is not part of the book and mdbook does
not build it.

## What the book is

The user-facing manual for the `semi-persistent` e-graph engine, in four parts:
build and run it, understand the e-graph, understand anti-unification, then use
both to diagnose autoformalizations. A reader works through it in order. Part I
is reference material for someone who has just cloned the repository, Part IV is
the application the book exists to explain.

The audience knows what a term rewriting system is and does not know this engine.
Assume no familiarity with e-graphs, equality saturation, or anti-unification.

## Ownership and reuse

Use a strict define-once, apply-later rule. A later chapter links to the
authoritative chapter instead of teaching the same mechanism again.

- Chapter 3 owns sorts, literals, declarations, and ground-term construction.
- Chapter 4 owns algebraic laws, legality, arity, inverse, and cancellativity.
- Chapter 5 owns every rule, pattern, remainder, multiplicity, and comprehension
  form. Annex A alone owns the complete formal grammar.
- Chapter 6 owns e-nodes, e-classes, hash-consing, union-find, generic
  congruence, and rebuild.
- Chapter 7 owns push/pop behavior, cost, nesting, and `:shrink`.
- Chapter 8 owns round ordering, `run`, saturation, extraction, and statistics.
- Chapter 9 assumes Chapter 8 and explains only the delta optimization and
  full-index fallback cases.
- Chapter 10 owns physical child representations and the canonization pipeline.
  It uses one representation table and one canonization example.
- Chapter 11 owns the additional equalities obtained in plain, eager, and lazy
  completion. Use its counterexample and comparison table; detailed limits
  belong to Chapter 23.
- Chapter 12 owns the AU definition, `Variants`, output fields, and objective.
- Chapter 13 measures the effect of declared algebra on AU output without
  redefining the declarations.
- Chapter 14 is authoritative for pair-graph search, cycle policies, pruning,
  and the exact certificate.
- Chapter 15 explains only UCT playouts, shared-node bookkeeping, closure, and
  hybrid exact calls. It links to Chapter 14 for cycle and pruning semantics.
- Chapter 16 measures the consequences of the three optimality qualifiers. It
  does not redefine the objective, cycle modes, or completion.
- Chapter 17 owns motivation, presentational noise, and correlated errors.
- Chapter 18 owns clustering and troubleshooting.
- Chapter 19 owns pairwise cluster explanations and speculative resolution. It
  demonstrates Chapter 7 scopes without explaining them again.
- Chapter 20 is the small end-to-end application.
- Chapter 21 covers scale, several clusters, and deduplication of recurring
  disagreements. It does not add another domain-rewrite lesson.
- Chapter 22 owns the two-unit result, readability, domain-specific resolution,
  and the UCT cross-check. It does not reteach clustering.
- Chapter 23 intentionally repeats limits, but each is one short paragraph with
  a link to its authoritative chapter.

Display a complete program once. A later chapter includes only the new query,
changed declaration or rule, or resulting output. Chapters 18 and 19 share one
fixture. Chapters 20 through 22 do not repeat the grid-and-query procedure.
Delete "What comes next" sections that only summarize the following chapter.

Annex A contains only the complete grammar. Annex B contains compact command
signatures and links. Annex C contains flag/default/effect tables and links.

## Where things live

| path | what |
| --- | --- |
| `src/*.md` | the chapters. One file per chapter, numbered to match `SUMMARY.md` |
| `src/SUMMARY.md` | the table of contents. mdbook builds only what is listed here |
| `examples/*.egg` | every program the book shows. Executed by `book_examples` in `egraph/tests/egg_tests.rs` |
| `v1-draft/*.md` | the discarded first draft. Not built. Source material to carry over where a chapter outline says so |
| `build.sh` | the validation script. A chapter is not done until this passes |
| `book.toml` | mdbook config |

`v1-draft/` is scratch. Delete it in the commit that finishes the last chapter.

## Style

The rule catalog is `~/.claude/skills/technical-writing-critic/references/rules.md`.
The rules that get violated most in this book:

- A chapter opens by stating its contents: what it defines, shows, and measures,
  in one sentence or two. Not a hook, not a thesis.
- A section opens with its subject stated directly, or with its code block. Never
  write "This section ...". A previous draft prefixed every section with a summary
  of itself and it was rejected: the reader ends up reading each section twice.
- No em-dashes and no en-dashes anywhere, with one exception: verbatim program
  output is quoted as the engine emits it.
- No metaphors. Not "load-bearing", "levers", "gates", "arms", "legs". Plain
  technical vocabulary.
- Name what you count in the same sentence that announces the count. Not "three
  consequences follow" with the list in the next paragraph.
- No commentary on significance: "matters", "deliberate", "crucial", "essential",
  "the point is", "worth noting". State the consequence instead, or delete.
- Wrap prose at 90 columns. Tables and URLs are exempt.

Check the last one with:

```bash
awk 'length>90 && $0 !~ /^\|/ && $0 !~ /http/ {print FILENAME": "FNR}' doc/book/src/*.md
```

## Examples

Every program shown in the book is a file in `examples/`, included with
`{{#include ../examples/NN-name.egg}}`, and ends in `check` or `checkau`
assertions so that the test suite fails if the engine's behaviour changes.
Nothing is written out in prose only.

Directives go in the file's first six lines and mirror the CLI flags, so a file
selects its own mode and needs no harness change:

```text
;; EXPECT: ok|check-failed|parse-error|sort-error|error|panic     default ok
;; TYPES: machine|bignum                                          default bignum
;; EVAL: naive|semi|both                                          default both
;; DERIVE_AC_EQS: on                                              default off
;; LAZY_AC_EQS: on                                                default off
;; UNION_BY: rank|size|uses|sum                                   default rank
;; CHECK_AC_BASIS: on                                             default off
```

A chapter that compares modes ships one file per mode with the same program body,
differing only in the directive line, and says so in prose.

Every number, size, ratio and error string quoted in the book is captured by
running the engine. Never write a plausible one. Build the binary once
(`cargo build --release`) and run the example to get the text.

## Verification loop

```bash
bash doc/book/build.sh
cargo test -p semi-persistent-egraph --test egg_tests book_examples
```

`build.sh` greps the mdbook log for `ERROR`, fails if rendered HTML still
contains `{{#`, verifies every `{{#include}}` target and named anchor exists, and
fails if the book links to a repository path that git does not track. The anchor
check covers include anchors only, not in-page markdown links, which is why
cross-references name the heading in prose as well as linking the file.

## Constraints

- The untracked `autoformalization/` folder is a scratch experiment. Nothing in
  the book may reference it, include from it, or depend on it. Any example it
  once held gets rewritten as a self-contained file in `examples/`.
- Book work is committed on a feature branch, never directly on `main`.
- Design documents are the source of truth for internals and are linked as
  `https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/NN-name.md`.
  The book states what a reader needs and points at the design chapter for the
  full specification; it does not restate a specification.

## Where the facts are

| subject | design chapter |
| --- | --- |
| node storage, classes, union-find, hash-consing | `01`, `02`, `03` |
| canonization and node kinds | `04` |
| the e-graph and rebuild | `05` |
| indexes, leapfrog joins, query compilation, matching | `06`, `07`, `08`, `09` |
| surface language, sortcheck | `10`, `11`, `A1-language-guide` |
| rule application | `12` |
| literals | `13` |
| soundness, proofs | `14`, `15` |
| extraction | `16` |
| interpreter | `17` |
| semi-naive evaluation | `18` |
| anti-unification | `19` |
| index selectivity | `20` |
| algebraic properties, AC completion, completeness | `ac-algebraic-properties`, `ac-completion-spec`, `ac-congruence-completeness` |
