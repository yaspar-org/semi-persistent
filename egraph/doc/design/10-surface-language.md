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
the sortcheck phase, where registry metadata is available. These errors name
the invalid form, but precise source spans are not universal: some top-level
flatten/resolve errors are currently wrapped with `Span::Dummy`.

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
(op term...)  ; a bare top-level term inserts it
(ruleset name)
(rewrite lhs rhs [:when (guard...)] [:subsume] [:ruleset name])
(birewrite lhs rhs [:when (guard...)] [:ruleset name])
(rule (pattern... guard...) (action...) [:ruleset name])
(run [ruleset] N [:until (= a b) | :until (!= a b)])
(push) (push :shrink) (pop)
(check term) (check (= a b)) (check (!= a b))
(extract term)
(antiunify left right [:playouts N] [:algorithm exact|uct]
                     [:cycles sides|sides-current|pair])
(checkau left right [:max_size N] [:playouts N] [:algorithm exact|uct]
                    [:cycles sides|sides-current|pair])
(print-size) (print-size Op)
(print-stats) (print-stats :file "path.json")
```

There is no `(insert term)` command. In a rule head, an application without
the `union` or `set` keyword is an insert action; at the top level, the bare
application itself is the insertion form.

The command language exposes `exact` and `uct` as algorithms. Expansion-time
and rollout-time Exact delegation are separate `AuConfig` library flags
(`hybrid_exact` and `rollout_hybrid`); they are not additional
`:algorithm` spellings in the interpreter.

algebra-tags: `:comm` `:assoc` `:assoc-left` `:assoc-right` `:idempotent`
`:nilpotent [n]` `:identity term` `:cancellative` `:inverse Op`, plus the
pre-combined aliases `:assoc-comm` and `:assoc-comm-idem`.

extraction-tags: `:cost n` (default 1) and `:unextractable`.

`(birewrite a b)` is sugar, expanded by the parser into the two rewrites
`a -> b` and `b -> a`; both sides parse as patterns, and each is read
back as the other direction's right-hand side. A `:mult` annotation has
no right-hand-side spelling, so it is rejected on a birewrite side, and
`:subsume` is rejected because subsuming the node the reverse direction
has to match would make the pair asymmetric.

Rulesets scope which rules a run fires: an untagged rule is in the
default ruleset that `(run N)` runs, and `:ruleset name` puts a rule in
the ruleset that `(run name N)` runs. See Chapter 17 for the run
semantics, the `:until` goal, and the statistics commands.

`:when` and `:subsume` are rewrite tags. A multi-pattern `(rule ...)` places
primitive guard conjuncts directly in its body; after the head, only
`:ruleset` is accepted. The parser rejects `:when` or `:subsume` there rather
than silently ignoring either tag.

## Functions and Constructors

`(function …)` and `(constructor …)` parse to the same command and register the
same operator; the keyword sets one bit. A constructor is a term former: its
nodes carry `FLAG_CONSTRUCTOR`, and it is the declaration form that the
extraction tags are meant for. Every variant of a `(datatype …)` is a
constructor. Congruence, matching, and canonization treat the two identically:
unlike egglog, where `function` is a partial map with a mandatory merge lattice
and `constructor` is the eqsort term former.

The extraction tags are accepted on either form, because extraction is a
property of the operator rather than of the declaration keyword: `:cost n` sets
the per-node cost the extractor charges, and `:unextractable` removes the op's
nodes from the extractor's candidate set (Chapter 16).

---
[← Ch 9: Pattern Matching](09-pattern-matching.md) · [Table of Contents](00-table-of-contents.md) · [Ch 11: Sortcheck and Resolution →](11-sortcheck-and-resolution.md)
