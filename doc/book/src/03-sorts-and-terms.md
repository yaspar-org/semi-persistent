# Sorts and terms

> Chapter contents: the literal models and their built-in sorts, the grammar of
> declarations and term-building commands, what each command does to the e-graph,
> and how sortchecking rejects a bad term. This is the first half of the language;
> chapter 4 is the second.
>
> Example: `examples/03-terms.egg`. Read it before writing and build the chapter
> around it rather than inventing a new one. Extend it if a section needs a case it
> does not cover.
>
> Sources: design `10-surface-language.md`, `11-sortcheck-and-resolution.md`,
> `13-literal-model.md`, `A1-language-guide.md`.
>
> Carry over: `v1-draft/02-first-program.md` sections "Sorts and operators" and
> "Inserting a term" are accurate and already tied to a running file.

## Literal models

Before declarations are sort-checked, `--types` selects the concrete sorts and
primitive operations available to the program. The default is `bignum`.

| `--types` value | Predeclared sorts |
| --- | --- |
| `bignum` | `bool`, `IBig`, `UBig`, `RBig` |
| `machine` | `bool`, `i64`, `u64`, `f64`, `usize`, `String` |
| `machine,bignum` | All sorts from both groups |

Programs use these sort names directly in declarations. The running example
uses the default model:

```lisp
{{#include ../examples/03-terms.egg:literal-model-declarations}}
```

`Expr` and `Name` are introduced by the program, while `IBig` is supplied by
the selected literal model. Running the same declaration with only
`--types machine` rejects `IBig` as an unknown sort.

Chapter 6 gives the full `--types` flag reference.

## The grammar

The declaration and ground-term fragment of a Semper program has this grammar.
Braces mean zero or more repetitions, brackets mark an optional item, and `|`
separates alternatives.

```text
program       = { command }

command       = declaration
              | insertion
              | "(" "let" name term ")"
              | "(" "union" term term ")"

declaration   = "(" "sort" name ")"
              | "(" decl-kind name "(" { name } ")" name
                    { decl-option } ")"
              | "(" "datatype" name { variant } ")"

decl-kind     = "function" | "constructor"
variant       = "(" name { name } { decl-option } ")"

term          = literal | name | application
application   = "(" operator { term } ")"
insertion     = "(" name { term } ")"

decl-option   = ":cost" unsigned-integer
              | ":unextractable"
              | ":assoc" | ":comm" | ":assoc-comm"
              | ":assoc-comm-idem"
              | ":assoc-left" | ":assoc-right"
              | ":idempotent"
              | ":nilpotent" [ unsigned-integer ]
              | ":identity" term
              | ":cancellative"
              | ":inverse" name
```

An operator may be an ordinary name or a qualified builtin such as `IBig::+`.
Whitespace and `;` comments may appear between tokens. A nullary application
can be written explicitly with parentheses, as in `(x)`. Ground terms contain
no pattern variables; a bare name must resolve to a literal, a nullary operator,
or a name introduced by an earlier `let`.

Chapter 12 defines the algebraic declaration options listed above.
[Annex A](A-full-grammar.md) collects the complete surface grammar, including
patterns, rule actions, query and control commands, and every command option.

## Sorts

`(sort S)` registers an uninterpreted sort named `S`. It introduces only the
sort; it does not create any constants or other terms. The running example
declares `Expr` and `Name` as separate sorts. Semper has no subtyping or implicit
coercions between them.

An operator declaration fixes the sort of every term it builds. In the example,
`(constructor x () Name)` makes `(x)` a `Name`, while
`(function f (Name) Expr)` accepts a `Name` and returns an `Expr`. Therefore
`(f (x))` has sort `Expr`. Each child must have exactly the argument sort
declared for its position, and the outermost operator determines the term's
result sort.

`(datatype T (C S1 ... Sn) ...)` combines a sort declaration with constructor
declarations. It first registers `T`, then treats each variant as
`(constructor C (S1 ... Sn) T)`. Registering `T` first permits recursive
variants that use `T` as an argument. Every other argument sort must already
exist.

## Operators

An operator declaration lists its argument sorts before its result sort:

```lisp
{{#include ../examples/03-terms.egg:operator-declarations}}
```

`add` is binary, `neg` is unary, and the empty argument lists make `x`, `y`,
and `z` nullary operators. For an ordinary operator, the number of declared
argument sorts fixes its arity.

`function` and `constructor` have the same sortchecking, congruence, matching,
and canonization behavior. `constructor` additionally marks the operator as a
term former. Every variant of a `datatype` receives the same marker. The
current extractor does not otherwise prefer constructors over functions.

Two declaration tags control extraction. `:cost n` assigns each node of the
operator a cost of `n`, with a default of 1. `:unextractable` excludes those
nodes from extraction while leaving them in the e-graph and available for
matching. Both tags are accepted on functions and constructors. They affect
which representative `extract` selects, not which terms are equal. Chapter 9
defines the extraction cost model.

The remaining declaration tags assign algebraic properties. Semper enforces
them through automatic term canonization rather than rewrite rules. Chapter 12
defines those properties and their legal combinations.

## Building a term

A ground term enters the e-graph through one of three top-level forms. A bare
application inserts it without naming it. `(let name term)` inserts the term and
binds `name` to its e-class. `(union left right)` inserts both terms and merges
their e-classes.

```lisp
{{#include ../examples/03-building-terms.egg:building-terms}}
```

The three `print-size` commands report:

```text
x: 1
f: 1
total: 2
x: 1
f: 1
g: 1
total: 3
x: 1
f: 1
g: 1
h: 1
total: 4
```

The bare `(f (x))` inserts two e-nodes. The `let` reuses both and inserts only
`(g (f (x)))`, raising the total to three. The `union` likewise reuses
`(f (x))`, inserts `(h (f (x)))`, and raises the total to four. `print-size`
counts e-nodes, so merging the last two nodes into one e-class does not reduce
the total.

`named` is an e-class binding, not an alias for the syntax
`(g (f (x)))`. After the `union`, the same binding denotes the class containing
both `(g (f (x)))` and `(h (f (x)))`. Later commands may use `named` wherever a
ground term is accepted.

## Sortchecking

Semper sort-checks the complete program before executing any command.
Declarations are processed in source order. An operator declaration is rejected
if an argument or result sort is unknown. Registration also validates the
supported shapes and combinations of algebraic tags, including identity sorts
and inverse signatures. Chapter 12 gives those requirements.

Before a ground term is built, Semper resolves its operator and checks its
arity. It then checks the children from the leaves upward, requiring each child
to have exactly the sort declared for its position. Names must resolve to an
earlier `let` binding, a literal, or a nullary operator.

```lisp
{{#include ../examples/03-sort-error.egg:sort-error}}
```

`(x)` has sort `N`, so the inner `(f (x))` has sort `E`. The outer application
of `f` requires an `N`, not an `E`. The program is rejected before execution:

```text
sort error: sort error at 165..172: argument 1 of 'f': expected sort 'N', got 'E'
```

These checks establish that declarations have supported forms and terms are
well-sorted. Algebraic tags remain assertions about the intended
interpretation. Sortchecking can validate that a tag combination is supported,
but it does not prove that the intended operator satisfies the declared laws.
Once accepted, Semper enforces those laws through canonization. Chapter 26
collects this and the other obligations left to the program author.

## Literals

> How literal tokens are classified at the sort expected by an operator, including
> booleans, numbers, and strings. Do not repeat the literal-model table. For the
> book's purposes, literals mainly occur as constructor arguments and as
> `:identity` units such as `(Lit true)`. Keep this short and point at design
> chapter 13.
