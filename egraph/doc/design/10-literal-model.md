# Chapter 10 — Extensible Literal Model

[← Ch 9: Saturation](09-saturation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 11: Extraction →](11-extraction.md)

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
pub trait LitModel: 'static {
    type Value: LitVal;
    fn sorts(&self) -> &[LitSortDesc<Self::Value>];
    fn ops(&self) -> &[LitOpDesc<Self::Value>];
    fn sort_of(val: &Self::Value) -> &'static str;
    fn parse_as(&self, sort_name: &str, token: &str) -> Option<Self::Value>;
    fn parse_any(&self, token: &str) -> Option<(&'static str, Self::Value)>;
    fn find_op(&self, name: &str) -> Option<&LitOpDesc<Self::Value>>;
    fn is_lit_sort(&self, name: &str) -> bool;
    fn is_truthy(val: &Self::Value) -> bool;
}
```

`parse_as`, `parse_any`, `find_op`, and `is_lit_sort` have default bodies that scan
`sorts()` or `ops()`; a model supplies `Value`, `sorts`, `ops`, `sort_of`, and
`is_truthy`.

Each model declares concrete sorts (IBig, bool, etc.) and primitive
operations (+, -, *, <, etc.) with their evaluation functions.

## Provided Models

| Model | Sorts | Use case |
|-------|-------|----------|
| `BignumModel` | bool, IBig, UBig, RBig | Arbitrary precision; the CLI default (`--types bignum`) |
| `MachineModel` | bool, i64, u64, f64, usize, String | Machine and string operations |
| `AllModel` | All of the above | Full sort set (`--types machine,bignum`) |
| `NiraModel` | bool, IBig, RBig | Internal unit tests |

## `LitValStore`

```rust
pub struct LitValStore<L, V, const TRACK: bool> {
    map: SpUniqueMap<L::Key, L, V::Index, TRACK>,
}
```

The store is a verified semi-persistent map in its unique-keys discipline
(`SpUniqueMap`; the key types come from the container crate's `literal-types`
feature): its append-only value log is the source of truth and the log
positions are the literal ids; its index is the map's own, maintained through
the verified insert/restore transitions (restore unwinds the discarded suffix,
no hand-rolled rebuild heuristic). Interning is `try_intern`: one hash of the
canonical key decides membership and appends on a miss, and the discipline
guarantees the log never holds a shadowed literal. Mark and restore go through
the session's history.

Keys are **canonical**, not bit-compared values. `LitVal` carries an
associated `Key` type and `key()`, produced from each payload type by the
`CanonicalKey` trait, which maps a value to the representation under which
value equality is key equality (the map's key-model requirement):

| payload | key | why |
|---|---|---|
| `bool`, `i64`, `u64`, `usize`, `String`, `BigInt`, `BigUint` | itself | structural `Eq`/`Hash` is value identity |
| `OrderedFloat<f64>` | `CanonicalF64` | the fold `OrderedFloat` already applies (±0.0 and all NaNs identified), pinned by the container crate's compliance tests, so interning keeps the identity the e-graph had; the bit-exact `BitsF64` is the documented alternative |
| `BigRational` | `CanonicalRational` | gcd-reduced, sign-normalized pair; `Ratio::new_raw` can reach `2/4`, which `BigRational::eq` conflates with `1/2` while its hash may not |

`define_litval!` takes the key enum's name and generates it from the
variants' canonical keys (`MachineLitKey`, `BignumLitKey`, `AllLitKey`);
`NiraLitVal` has `NiraLitKey` by hand.

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
[← Ch 9: Saturation](09-saturation.md) · [Table of Contents](00-table-of-contents.md) · [Ch 11: Extraction →](11-extraction.md)
