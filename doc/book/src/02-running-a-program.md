# Running a program

> Chapter contents: the invocation, the anatomy of a program file, which stream
> each kind of output goes to, the exit statuses, and how to run one of this book's
> examples yourself.
>
> Carry over: `v1-draft/01-install.md` sections "Run a program" and "Exit status".
>
> Verify before writing: run the binary on `doc/book/examples/03-terms.egg` and
> paste what it actually prints, including the closing line on stderr. Verify each
> exit status by provoking it: a passing file, a failing `check`, a parse error, a
> sort error.

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

> Table of status and cause: success, failed check, parse error, sort error. State
> that a failed `check` aborting with a nonzero status is the mechanism that makes
> an example file a regression test.

## Running the book's examples

> The path the examples live at, the command to run one, and the `cargo test`
> invocation that runs all of them. Mention the first-six-lines directives exist
> and that chapter 6 lists them, because a reader who opens an example file will
> see them immediately.
