# Chapter 10 — Surface Language and Parser

[← Ch 9: Pattern Matching](09-pattern-matching.md) · [Table of Contents](00-table-of-contents.md) · [Ch 11: Sortcheck and Resolution →](11-sortcheck-and-resolution.md)


## Design Philosophy

The engine uses a unified S-expression syntax for all constructs. The key
design decision: the surface syntax does not distinguish operator
kinds. All operator applications use `(op children...)` regardless
of whether the operator is plain, commutative, associative, AC, or
ACI. The operator's registered kind is resolved during sortcheck
(Chapter 11), not during parsing.

As a result, the parser is simple and context-free. It does not need
access to the operator registry. Kind-specific validation (e.g.,
"rest variables are only allowed on variadic operators") happens in
the sortcheck phase, where clear error messages with source spans
can be produced.

Rest variables use `..name` prefix syntax. Multiplicity annotations
use `:k` suffix syntax. Brackets survive only in RHS comprehensions
(`{...}` for set/multiset, `[...]` for sequence).

## LHS Patterns: `SurfacePattern`

```rust
enum SurfacePattern {
    Var(String, Span),
    Lit(String, Span),
    App {
        op: String,
        prefix: Option<(String, Span)>,   // ..pre
        children: Vec<SurfacePatChild>,
        suffix: Option<(String, Span)>,   // ..suf
        span: Span,
    },
}

enum SurfacePatChild {
    Elem(SurfacePattern),
    ElemMult(SurfacePattern, MultSpec),
}
```

`Lit` handles literal constants in patterns (e.g., `42`, `true`).
Literals follow a distinct code path from `Var`: they are resolved to
concrete `@`-prefixed ops during sortcheck, while variables become
pattern bindings.

Rest variables are structurally first/last only. The parser extracts
them into `prefix`/`suffix` fields. A lone `(op ..rest)` places
`rest` in `suffix`.

## RHS Terms: `RhsTerm`

```rust
enum RhsChild {
    Term(RhsTerm),
    Splice(String, Span),                    // ..rest
    SetComp { body, var, src, filter },      // ..{body for v in src}
    MsetComp { body, var, mult, src, filter },
    SeqComp { body, var, src, filter },      // ..[body for v in src]
}
```

Comprehension syntax uses real `{}`/`[]` delimiters.

## Ground Terms: `Term`

```rust
enum Term {
    Lit(String, Span),
    App { op: String, children: Vec<Term>, span: Span },
}
```

## Commands

```
(sort Name)
(function Name (ArgSort...) RetSort [algebra-tags] [extraction-tags])
(constructor Name (ArgSort...) RetSort [algebra-tags] [extraction-tags])
(datatype Name (Ctor ArgSort... [algebra-tags] [extraction-tags])...)
(let name term)
(union term term)
(insert term)
(rewrite lhs rhs [:when (guard...)] [:subsume])
(rule ((pattern...) [:when (guard...)]) ((action...)))
(run N)
(push) (push :shrink) (pop)
(check term) (check (= a b)) (check (!= a b))
(extract term)
```

algebra-tags: `:comm` `:assoc` `:assoc-left` `:assoc-right` `:idempotent`
`:nilpotent [n]` `:identity term` `:cancellative` `:inverse Op`, plus the
pre-combined aliases `:assoc-comm` and `:assoc-comm-idem`.

extraction-tags: `:cost n` (default 1) and `:unextractable`.

## Functions and Constructors

`(function …)` and `(constructor …)` parse to the same command and register the
same operator; the keyword sets one bit. A constructor is a term former: its
nodes carry `FLAG_CONSTRUCTOR`, and it is the declaration form that the
extraction tags are meant for. Every variant of a `(datatype …)` is a
constructor. Congruence, matching, and canonization treat the two identically —
unlike egglog, where `function` is a partial map with a mandatory merge lattice
and `constructor` is the eqsort term former.

The extraction tags are accepted on either form, because extraction is a
property of the operator rather than of the declaration keyword: `:cost n` sets
the per-node cost the extractor charges, and `:unextractable` removes the op's
nodes from the extractor's candidate set (Chapter 16).

---
[← Ch 9: Pattern Matching](09-pattern-matching.md) · [Table of Contents](00-table-of-contents.md) · [Ch 11: Sortcheck and Resolution →](11-sortcheck-and-resolution.md)
