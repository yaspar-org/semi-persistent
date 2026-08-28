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

## The example files that already exist

These were written for the discarded structure, run green, and have been renumbered
to the new chapters. Their bodies are good. Their header comments still carry v1
chapter numbers and, in a few files, the old name of a sibling file, so each header
needs correcting when its chapter is written. Do not renumber them again.

| file | chapter | header says |
| --- | --- | --- |
| `03-terms.egg` | 3 | chapter 3, and a forward reference to "chapter 6" that is now chapter 7 |
| `04-rewrite-rules.egg` | 4 | chapter 4 |
| `09-saturation.egg` | 9 | chapter 5, and a reference to "chapter 4" that is now 7 |
| `11-node-kinds.egg` | 11 | chapter 6 |
| `11-clamping.egg` | 11 | chapter 8 |
| `11-illegal-clamp.egg` | 11 | chapter 8 |
| `12-illegal-seq-identity.egg` | 12 | chapter 11, and a reference to "chapter 8" that is now 11 |
| `13-rules-over-set.egg` | 13 | chapter 9, and a reference to "chapter 10" that is now 13 |
| `13-rules-over-mset.egg` | 13 | chapter 10 |
| `13-rules-over-seq.egg` | 13 | chapter 11, plus the old path `11-illegal-seq-identity.egg` |
| `14-cc-plain.egg`, `14-cc-eager.egg`, `14-cc-lazy.egg` | 14 | chapter 13, plus the old name `13-cc-plain.egg` |
| `16-identity-arity.egg` | 16 | chapter 3 |
| `19-au-plain.egg`, `19-au-eager.egg`, `19-au-lazy.egg` | 19 | chapter 14, plus the old name `14-au-plain.egg` |

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
- Book work is committed on `docs/semper-book`, never on `main`.
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
