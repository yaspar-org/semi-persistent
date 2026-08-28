# Command reference

> Chapter contents: every command the interpreter accepts, in seven groups:
> declaring, building terms, rules, running, asserting, querying, and scoping.
>
> Carry over: `v1-draft/10-commands.md` almost verbatim. It is complete against the
> parser as of this writing and its tables are correct. Two changes are required:
> delete the seven "This section ..." openers it still carries, and renumber every
> cross-reference to the new chapter numbers.
>
> Verify before writing: the command names in `egraph/src/parser.rs`. The set is
> sort, function, constructor, datatype, ruleset, let, union, set, rewrite,
> birewrite, rule, run, check, checkau, antiunify, extract, print-size, print-stats,
> push, pop. If the parser has grown a command since, add it.
>
> This chapter is a reference. It states what each command does and links to the
> chapter that explains it. It does not teach and it does not motivate.

## Symbol declarations and algebraic properties

| Command | Effect |
| --- | --- |
| `(sort S)` | Declare an uninterpreted sort `S`. |
| `(function f (S1 ... Sn) S :tag*)` | Declare an operator with result sort `S`. |
| `(constructor f (S1 ... Sn) S :tag*)` | Declare the operator as a constructor. |
| `(datatype T (C S ... :tag*) ...)` | Declare `T` and one constructor per variant. |
| `(ruleset r)` | Declare a ruleset name for `:ruleset r` and `(run r n)`. |

Algebraic properties are attached to operator declarations and individual
datatype variants as tags. They determine an operator's representation and
required arity. [Chapter 12](12-declaring-algebra.md) gives their laws, legal
combinations, and exact arity rules.

```text
:assoc-comm-idem | :assoc-comm | :assoc | :assoc-left | :assoc-right | :comm
:idempotent | :nilpotent [unsigned-integer] | :identity term
:cancellative | :inverse identifier
:cost unsigned-integer | :unextractable
```

Square brackets mark an optional argument. Tags may be combined in any order.
`:assoc-comm` and `:assoc-comm-idem` are aliases for their corresponding basic
tags. `:cost` and `:unextractable` affect extraction, not equality.

## Building terms

| Command | Effect |
| --- | --- |
| `(let name term)` | Insert `term` and bind `name` to its e-class. |
| `(union left right)` | Insert both terms and merge their e-classes. |
| `(f a b)` | Insert a ground application without naming it. |

A bare operator application at top level is an insertion command. A name
introduced by `let` denotes the resulting e-class and may be used wherever a
ground term is accepted. [Chapter 3](03-sorts-and-terms.md#building-a-term)
explains term construction in detail.

## Rules

> The three rule forms and the action grammar, `:when`, `:subsume`, `:ruleset`. One
> sentence naming the variadic pattern surface, with the link to chapter 13.

## Running

> The four `run` forms including both `:until` shapes. State that saturation is a
> fixpoint of the declared rules and not of the theory.

## Asserting

> Table of the four assertion forms and what each passes on. Keep the caution about
> `(check (!= t1 t2))`: it reports that the engine did not derive equality, which is
> a statement about the declared rules and the active congruence mode, not about
> semantic disequality. Link chapter 14.

## Querying

> Table of the commands that print: `extract`, `antiunify`, `checkau`,
> `print-size`, `print-stats`. The shared anti-unification option grammar as a
> `text` block, with the link to chapters 15 through 18.

## Scoping

> `(push)`, `(push :shrink)`, `(pop)`. One paragraph on what they cost, with the
> link to chapter 8, which is where the mechanism is explained.
