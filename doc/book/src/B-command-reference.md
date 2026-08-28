# Annex B. Command reference

> Annex contents: every command the interpreter accepts, in seven groups:
> declaring, building terms, rules, running, asserting, querying, and scoping.
>
> Use `v1-draft/10-commands.md` only as a checklist of command names. Rebuild the
> reference as compact signatures and links; do not carry over its full declaration,
> rule, anti-unification, or scope explanations.
>
> Verify before writing: the command names in `egraph/src/parser.rs`. The set is
> sort, function, constructor, datatype, ruleset, let, union, rewrite,
> birewrite, rule, run, check, checkau, antiunify, extract, print-size, print-stats,
> push, pop. If the parser has grown a command since, add it.
>
> This annex is a reference. It states what each command does and links to the
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
required arity. [Chapter 4](04-declaring-algebra.md) gives their laws, legal
combinations, and exact arity rules. [Chapter 3](03-sorts-and-terms.md)
defines the extraction tags. Annex A contains the complete declaration grammar.

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

> Give one compact signature row for `rewrite`, `birewrite`, and `rule`, followed
> by links to chapter 5 for semantics and Annex A for the complete pattern,
> action, multiplicity, splice, and comprehension grammar. Do not reproduce that
> grammar here.

## Running

> The four `run` forms including both `:until` shapes. State that saturation is a
> fixpoint of the declared rules and not of the theory.

## Asserting

> Table of the four assertion forms and what each passes on. Keep the caution about
> `(check (!= t1 t2))`: it reports that the engine did not derive equality, which is
> a statement about the declared rules and the active congruence mode, not about
> semantic disequality. Link chapter 11.

## Querying

> Table of the commands that print: `extract`, `antiunify`, `checkau`,
> `print-size`, `print-stats`. Link Annex A for anti-unification option syntax
> and chapters 12 through 15 for behavior; do not repeat the option grammar.

## Scoping

> Table rows for `(push)`, `(push :shrink)`, and `(pop)`, with a link to chapter
> 7. Do not repeat the implementation cost model.
