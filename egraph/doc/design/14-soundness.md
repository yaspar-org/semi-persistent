# Chapter 14 — Soundness of Primitive Operations

[← Ch 13: Literal Model](13-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 15: Proof Logging →](15-proof-logging.md)


## Why This Matters

Adding primitive operations (integer addition, boolean negation, etc.)
to an e-graph engine is not free; it introduces a soundness obligation.
The e-graph's correctness depends on the congruence closure invariant:
if inputs are equivalent, outputs must be equivalent. This chapter
explains why the engine's literal architecture satisfies this requirement.

## The Congruence Requirement

E-graph rewriting is sound when all operations respect congruence:
if `a ≡ a'` and `b ≡ b'`, then `f(a, b) ≡ f(a', b')`.

For user-declared operators, congruence is maintained by the rebuild
algorithm (Chapter 5). For primitive literal operations, soundness
requires that the evaluation function is a true mathematical function
, meaning same inputs always produce the same output.

## Why Literal Ops Are Safe

Primitive ops like `IBig::+` operate on interned literal values.
Two e-nodes with the same `LitValId` are identical by construction
(interning deduplicates). The evaluation function maps `(LitValId,
LitValId) → LitVal`, which is then interned to get a `LitValId`.

Since:
1. Interning is deterministic (same value → same id)
2. Evaluation is a pure function (no side effects)
3. Literal nodes have no e-node children (only a `LitValId`)

...congruence is trivially satisfied: literal nodes never need
re-canonization during rebuild.

## The `@`-Prefixed Auto-Lift

Each concrete sort gets an auto-generated operator:

```
@IBig : → IBig     (OpKind::Lit)
```

The auto-lift is the only implicit step. `@IBig(lid)` wraps a `LitValId` into
an e-node. The user never writes `@IBig`; it is inserted by
sortcheck when a literal appears in a term.

## Primitive Op Registration

`LitOpDesc` declares a primitive operation:

```rust
pub struct LitOpDesc<V> {
    pub name: &'static str,
    pub arg_sorts: &'static [&'static str],
    pub ret_sort: &'static str,
    pub eval: fn(&[&V]) -> V,
}
```

The `eval` function receives argument values by reference and returns
the result by value. It is called during RHS application (Chapter 12).

## Checked/Wrapping/Saturating Arithmetic

`MachineModel` offers multiple semantics for integer overflow:

| Op | Behavior |
|----|----------|
| `i64::checked_add` | Returns error on overflow |
| `i64::wrapping_add` | Wraps around |
| `i64::saturating_add` | Clamps to min/max |

The user selects the semantics by choosing the appropriate op name
in their rewrite rules. The model includes all variants.

## `is_truthy`

Used by `:when` guards to interpret a literal value as a boolean:

```rust
fn is_truthy(&self, val: &BignumLit) -> bool {
    match val {
        BignumLit::Bool(b) => *b,
        _ => false,
    }
}
```

Only `Bool(true)` is truthy. All other values (including non-zero
integers) are falsy. This prevents accidental truthiness bugs.

---
[← Ch 13: Literal Model](13-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 15: Proof Logging →](15-proof-logging.md)
