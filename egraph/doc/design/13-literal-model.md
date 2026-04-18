# Chapter 13 — Extensible Literal Model

[← Ch 12: Rule Application](12-rule-application.md) · [Table of Contents](00-table-of-contents.md) · [Ch 14: Soundness →](14-soundness.md)


## The Problem

An e-graph engine needs to handle concrete values (integers, booleans,
strings) alongside symbolic terms. But hardcoding a fixed set of
types would limit extensibility. The engine solves this with the `LitModel`
trait: a pluggable interface that declares concrete sorts, primitive
operations, and their evaluation functions.

The critical design constraint: matching must be read-only. New
literal values are only interned during RHS application, never during
LHS matching or guard evaluation. This is the deferred interning
invariant (see below).

## `LitModel` Trait

```rust
pub trait LitModel {
    type Value: LitVal;
    fn sorts(&self) -> &[LitSortDesc];
    fn ops(&self) -> &[LitOpDesc<Self::Value>];
    fn is_truthy(&self, val: &Self::Value) -> bool;
}
```

Each model declares concrete sorts (IBig, bool, etc.) and primitive
operations (+, -, *, <, etc.) with their evaluation functions.

## Provided Models

| Model | Sorts | Use case |
|-------|-------|----------|
| `BignumModel` | IBig, UBig, RBig, bool, String | Arbitrary precision |
| `MachineModel` | i64, u64, f64, bool, String | Fixed-width with overflow semantics |
| `AllModel` | All of the above | Testing (full sort set) |
| `NiraModel` | Nira (integer-like) | Internal unit tests |

## `LitValStore`

```rust
pub struct LitValStore<L, V, const TRACK: bool> {
    values: Vec<L>,
    index: HashMap<L, V>,
}
```

| Method | Mutates? | Used in |
|--------|----------|---------|
| `intern(value) → V` | Yes | RHS apply, ground term building |
| `get(id) → &L` | No | LHS matching, guard evaluation |
| `try_lookup(&value) → Option<V>` | No | Probing without interning |

## Deferred Interning

The critical invariant: sortcheck and LHS matching never intern.

| Phase | LitValStore | E-graph |
|-------|------------|---------|
| Parse | — | — |
| Sortcheck | — | — |
| Build ground term | `intern` | `add`, `add_lit` |
| LHS matching | read-only | read-only |
| Guard evaluation | read-only | read-only |
| RHS application | `intern` | `add`, `add_lit`, `merge` |

`try_lookup` is the read-only probe: if a pattern requires literal
42 but 42 was never introduced, it returns `None` and the match
fails without polluting the store.

## Sort Architecture

```
Concrete sorts:  IBig, UBig, RBig, bool, String, i64, u64, f64
                 (registered by LitModel::sorts())

Auto-generated:  @IBig : → IBig    (OpKind::Lit, internal)
                 @bool : → bool
                 ...

User-declared:   (datatype Expr (Num IBig) (Add Expr Expr))
                 Num : IBig → Expr  (normal unary op)
```

A literal `42` in the e-graph:

```
@IBig(litval_id_for_42)          ← internal literal node
Num(@IBig(litval_id_for_42))     ← user constructor
```

The `@`-prefixed ops never appear in user syntax. The parser sees `42`
and sortcheck wraps it in the appropriate `@` op.

## No Implicit Bridging

There is no automatic coercion from concrete sorts to user sorts.
If the user writes bare `42` where `Expr` is expected, it is a sort
mismatch error. The user must explicitly write `(Num 42)`.

---
[← Ch 12: Rule Application](12-rule-application.md) · [Table of Contents](00-table-of-contents.md) · [Ch 14: Soundness →](14-soundness.md)
