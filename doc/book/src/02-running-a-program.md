# Running a program

## Invocation

The command line takes one positional argument: the path to an `.egg` program.
We write any options after that path:

```text
./target/release/semi-persistent PROGRAM.egg [OPTIONS]
```

Here is the program used in Chapter 3:

```lisp
{{#include ../examples/03-terms.egg}}
```

Run it from the repository root:

```bash
./target/release/semi-persistent doc/book/examples/03-terms.egg
```

```text
ok — 11 nodes
```

All its checks pass, and the engine finishes with 11 e-nodes.

## What a program file is

A Semper program is a text file containing S-expression commands. The `.egg`
extension is a convention rather than a requirement. A semicolon starts a
comment that continues to the end of the line.

Semper parses the complete file, sort-checks its commands in source order, and
then executes the checked commands in that same order. Declarations are not
hoisted: a sort must precede operators that use it, and an operator must precede
terms or rules that use it. A declaration later in the file cannot satisfy an
earlier reference.

The example above follows this order: it declares its sorts, declares its
operators, builds and names terms, and finally checks equalities.

## Output streams

Commands that return data, including `extract`, `antiunify`, `print-size`, and
`print-stats`, write their results to standard output. Successful checks print
nothing. After the program finishes, Semper writes its closing status to
standard error:

```text
ok — N nodes
```

The example above therefore has no standard output; its only visible line is
the closing status.

Redirecting standard output gives a script only the query results while leaving
the status visible on the terminal:

```bash
./target/release/semi-persistent PROGRAM.egg > answers.txt
```

To capture both streams separately:

```bash
./target/release/semi-persistent PROGRAM.egg \
  > answers.txt 2> status.txt
```

## Exit status

Semper exits with status 0 only after the complete program runs successfully.
Syntax, sort-checking, and failed-check errors exit with status 1.

| Status | Cause | Standard error |
| --- | --- | --- |
| 0 | The program ran and every check passed. | `ok — N nodes` |
| 1 | A `check` or `checkau` assertion failed. | `error: check failed: ...` |
| 1 | The parser rejected the program. | `parse error: ...` |
| 1 | A declaration or term failed sort-checking. | `sort error: ...` |

A failed check stops the program immediately. Its nonzero status lets an
example file act as a regression test: a script or test runner fails when the
behavior asserted by the file no longer holds. Query output may have been
written before a later check failed, so callers should use the exit status
rather than the presence of output to decide whether the run succeeded.

## Running the book's examples

Every program displayed in this book lives under `doc/book/examples/`. The
chapters include those files directly, so the displayed source and the tested
source are identical.

Run one example from the repository root:

```bash
./target/release/semi-persistent doc/book/examples/03-terms.egg
```

Run all book examples through their test harness:

```bash
cargo test -p semi-persistent-egraph --test egg_tests book_examples
```

The `book_examples` test scans every `.egg` file in the directory. The first six
lines of a file may contain directives such as `;; EXPECT: ok` or
`;; DERIVE_AC_EQS: on`. These lines are comments to the engine binary; the test
harness reads them to select settings and the expected outcome.

[Annex C](C-flag-reference.md) lists every directive and its corresponding
command-line option.
When running an example manually, pass the matching option for any nondefault
directive. An `EXPECT` directive can also state that a parse, sort, or check
failure is the expected test result.
