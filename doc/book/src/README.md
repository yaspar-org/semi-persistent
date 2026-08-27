# Introduction

> Chapter contents: what the engine is, what the four parts of the book cover,
> what the reader is assumed to know, and what the book is not.
>
> Carry over: `v1-draft/README.md` has usable text for "The examples" and "What
> this book is not". Its framing paragraphs are about a book that opened on the
> autoformalization problem and must be rewritten: this book opens on the engine
> and reaches autoformalization in Part IV.
>
> Keep this chapter short. Two pages. It is the only place in the book that is
> allowed to describe content instead of delivering it.

## What this is

Semper is a term rewriting and equality saturation engine. Programs can
snapshot and restore its state with semi-persistent `(push)` and `(pop)`, and
can issue anti-unification queries over e-classes. Semper is a command-line
program that reads a text file of S-expression commands in order. Every program
in this book is one such file.

Semper lets a program tag operators with algebraic properties such as
associativity, commutativity, idempotence, an identity element, or a declared
nilpotence order. The engine enforces those properties through automatic term
canonization instead of rewrite rules. For an associative and commutative
operator, children are represented as a sorted multiset. One e-node therefore
represents every reassociation and permutation of that multiset, compressing a
whole family of AC-equivalent terms without enumerating its members.

The engine also answers more than equality questions. An anti-unification query
returns a term that preserves shared structure and marks the remaining
disagreements with `Variants` nodes.

## The four parts

In Part I, we build the binary, write and run a program, and introduce the
commands and flags available from the command line.

In Part II, we explain what the e-graph stores, how saturation runs, how
algebraic declarations change operator representations, and how the three
congruence modes differ.

In Part III, we explain what anti-unification computes, how exact search, graph
search, and their hybrid work, and what an optimal result is optimal over.

In Part IV, we apply the engine to autoformalization. We sample a formalizer
several times, cluster the samples by equality saturation, and anti-unify across
clusters to explain the remaining differences.

## What you need to know already

We assume that you are familiar with first-order terms and rewrite rules. We do
not assume any experience with Semper or with e-graphs, equality saturation, AC
canonization, or anti-unification; we introduce each of them from scratch.

## The examples

Every program shown in this book lives in `doc/book/examples/` and is included
in its chapter directly from that file. The test suite executes every `.egg`
file in the directory.

Each example ends with `check` or `checkau` assertions that state the behavior
the chapter relies on. A change in engine behavior therefore fails a test
instead of silently invalidating the book. Every number, size, ratio, and error
message quoted in the book was captured by running the corresponding file.

## What this book is not

> Carry over from `v1-draft/README.md`. It is not the design documentation: the
> design chapters under `egraph/doc/design/` specify the internals and the book
> links to them where a reader may want the specification. It is not a paper: no
> theorems are proved here, and where the implementation rests on an argument
> rather than a proof the book says so and points at the design chapter that makes
> the argument.
