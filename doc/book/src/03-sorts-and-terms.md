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

> Three ways in: a bare term at top level, `(let x t)` which also names the class,
> and `(union t1 t2)` which inserts both and asserts they are equal. Show the
> e-node count after each with `print-size` so the reader sees that insertion is
> the thing that grows the graph.
>
> State plainly what `let` binds: an e-class, not a term. This is the distinction
> the whole book rests on and it is cheapest to establish here.

## Sortchecking

> What is checked at declaration time and what at term construction time. Show one
> rejected program and quote the real error text. The example file for it carries
> `;; EXPECT: sort-error`.
>
> State the honest boundary: sortchecking rejects malformed terms and does not check
> that a declared algebraic attribute is true of anything. Chapter 26 collects that.

## Literals

> How literal tokens are classified at the sort expected by an operator, including
> booleans, numbers, and strings. Do not repeat the literal-model table. For the
> book's purposes, literals mainly occur as constructor arguments and as
> `:identity` units such as `(Lit true)`. Keep this short and point at design
> chapter 13.
