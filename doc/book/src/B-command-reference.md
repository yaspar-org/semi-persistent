# Annex B. Command reference

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
