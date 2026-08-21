# Chapter 13 — Extensible Literal Model

[← Ch 12: Rule Application](12-rule-application.md) · [Table of Contents](00-table-of-contents.md) · [Ch 14: Soundness →](14-soundness.md)


## The Problem

An e-graph engine needs to handle concrete values (integers, booleans,
strings) alongside symbolic terms. But hardcoding a fixed set of
types would limit extensibility. The engine solves this with the `LitModel`
trait: a pluggable interface that declares concrete sorts, primitive
operations, and their evaluation functions.

The critical design constraint is narrower and operational: LHS matching and
LHS predicate-guard evaluation are read-only. They never intern literal
values. RHS evaluation, ground-term construction, and construction of a
declared algebraic identity may intern values.

## `LitModel` Trait

```rust
pub trait LitModel {
    type Value: LitVal;
    fn sorts(&self) -> &[LitSortDesc<Self::Value>];
    fn ops(&self) -> &[LitOpDesc<Self::Value>];
    fn sort_of(val: &Self::Value) -> &'static str;
    fn parse_as(&self, sort_name: &str, token: &str) -> Option<Self::Value>;
    fn is_truthy(val: &Self::Value) -> bool;
}
```

Each model declares concrete sorts (IBig, bool, etc.) and primitive
operations (+, -, *, <, etc.) with their evaluation functions.

## Provided Models

| Model | Sorts | Use case |
|-------|-------|----------|
| `BignumModel` | bool, IBig, UBig, RBig | Arbitrary precision |
| `MachineModel` | bool, i64, u64, f64, usize, String | Machine and string operations |
| `AllModel` | All of the above | Testing (full sort set) |
| `NiraModel` | bool, IBig, RBig | Internal unit tests |

## `LitValStore`

```rust
pub struct LitValStore<L, V, const TRACK: bool> {
    log: AppendOnlyVec<L, V::Index, TRACK>,
    index: HashMap<L, V::Index>,
}
```

The append-only log is the source of truth and its positions are literal ids.
The hash map is a derived lookup index. Restore normally removes only the
entries for the truncated suffix; for a sufficiently large suffix it clears
and rebuilds the index from the surviving log.

| Method | Mutates? | Used in |
|--------|----------|---------|
| `intern(value) → V` | Yes | RHS apply, ground term building |
| `get(id) → &L` | No | LHS matching, guard evaluation |
| `try_lookup(&value) → Option<V>` | No | Probing without interning |

## Read-Only Matching Boundary

Ordinary term and rule sortchecking classifies literal tokens without
interning them. `sortcheck_program` as a whole is nevertheless not read-only:
it registers declarations against the live e-graph, and an AC `:identity`
declaration builds its ground unit immediately. If that unit contains a
literal, declaration handling interns it.

| Phase | LitValStore | E-graph |
|-------|------------|---------|
| Parse | — | — |
| Ordinary term/rule sortcheck | — | read registry metadata |
| Declaration registration | may `intern` an identity literal | register metadata; identity may `add` |
| Build ground term | `intern` | `add`, `add_lit` |
| LHS matching | read-only | read-only |
| LHS predicate guard | read-only | read-only |
| RHS application | `intern` | `add`, `add_lit`, `merge` |

`try_lookup` is available as a read-only interner probe. The current literal
pattern path instead scans the relevant `@sort` bucket and compares each
candidate node's stored payload in `CheckLit`; it likewise performs no
insertion.

## Sort Architecture

```
Concrete sorts:  IBig, UBig, RBig, bool, String, i64, u64, f64, usize
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

The `@`-prefixed ops never appear in user syntax. Sortcheck classifies `42` as
a value and sort in `CTerm::Lit`; ground-term construction later selects the
sort's `@` op and builds the literal node.

## No Implicit Bridging

There is no automatic coercion from concrete sorts to user sorts.
If the user writes bare `42` where `Expr` is expected, it is a sort
mismatch error. The user must explicitly write `(Num 42)`.

---
[← Ch 12: Rule Application](12-rule-application.md) · [Table of Contents](00-table-of-contents.md) · [Ch 14: Soundness →](14-soundness.md)
