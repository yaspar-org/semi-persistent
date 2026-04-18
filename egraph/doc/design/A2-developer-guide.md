# Developer Guide: Extending the Literal Model

[← Language Guide](A1-language-guide.md) · [Table of Contents](00-table-of-contents.md) · [Future Work →](A3-future-work.md)


This chapter explains how to add new builtin sorts and primitive
operations to the engine. The extension point is the `LitModel` trait,
which declares concrete value types, their operations, and how
literal tokens in source code map to typed values.

## The `LitModel` Trait

```rust
pub trait LitModel: 'static {
    type Value: LitVal;
    fn sorts(&self) -> &[LitSortDesc<Self::Value>];
    fn ops(&self) -> &[LitOpDesc<Self::Value>];
    fn sort_of(val: &Self::Value) -> &'static str;
    fn is_truthy(val: &Self::Value) -> bool;
    fn parse_as(&self, sort_name: &str, token: &str) -> Option<Self::Value>;
}
```

A model declares concrete sorts via `sorts()`, primitive operations
via `ops()`, a sort classifier via `sort_of()`, a truthiness
predicate for conditional evaluation, and a `parse_as()` method that
tries to parse a token as a value of a specific sort (with a default
implementation that delegates to the sort's parser). The `Value`
associated type is the runtime representation of all literal values
(typically an enum).

## Defining a New Builtin Sort

Each `LitSortDesc` names a concrete sort and provides a parser:

```rust
pub struct LitSortDesc<V> {
    pub name: &'static str,
    pub parse: fn(&str) -> Option<V>,
}
```

When the model is loaded, each sort is registered in the
`SortRegistry`. An internal `@`-prefixed operator is auto-generated
for each concrete sort (e.g., `@IBig`, `@bool`). These operators
create literal e-nodes that wrap a `LitValId` pointing into the
`LitValStore`.

To add a new sort (say, fixed-point decimals):

1. Add a variant to your `Value` enum: `Decimal(rust_decimal::Decimal)`.
2. Add a `LitSortDesc` with name `"Decimal"` and a parser that
   recognizes decimal literals (e.g., `"3.14d"`).
3. The engine auto-generates `@Decimal` and handles interning.

## Defining New Primitive Operations

Each `LitOpDesc` declares a monomorphic operation:

```rust
pub struct LitOpDesc<V> {
    pub name: &'static str,
    pub arg_sorts: &'static [&'static str],
    pub ret_sort: &'static str,
    pub eval: fn(&[&V]) -> V,
}
```

Operations are monomorphic: one entry per concrete signature. For
example, integer addition and rational addition are separate
operations:

```rust
LitOpDesc {
    name: "IBig::+",
    arg_sorts: &["IBig", "IBig"],
    ret_sort: "IBig",
    eval: |args| ibig_add(args[0], args[1]),
}
```

The qualified `Sort::op` naming convention eliminates ambiguity when
multiple numeric types are in scope.

At model load time, each `LitOpDesc` is registered as a real `OpId`
in the `OpRegistry`. The first `builtin_count` OpIds correspond to
model operations, providing a direct bridge from OpId to eval
function at runtime.

## How Builtins Are Lifted into the E-Graph

A literal value like `42` in source code flows through several
stages:

1. The parser sees `42` as a raw string token.
2. Sortcheck calls `LitModel::parse_as(sort_name, "42")` to
   classify the token as `IBig(42)`. No interning occurs.
3. When the interpreter builds the ground term, it interns the value
   into the `LitValStore` (idempotent) and creates a literal e-node:
   `@IBig(litval_id_for_42)`.
4. A user constructor like `(Num 42)` becomes two e-nodes:
   `@IBig(litval_id)` and `Num(@IBig(litval_id))`.

The `@`-prefixed operators never appear in user syntax. They are
internal nodes that wrap literal values so they can participate in
the e-graph's hash-consing and union-find.

## Deferred Interning Invariant

Sortcheck and LHS matching never intern new values into the
`LitValStore`. This invariant ensures that pattern compilation is a
pure descriptive step with no side effects on the e-graph.

| Phase | LitValStore | E-graph |
|-------|------------|---------|
| Parse | untouched | untouched |
| Sortcheck | untouched | untouched |
| Build ground term | `intern` | `add`, `add_lit` |
| LHS matching | read-only (`get`, `try_lookup`) | read-only |
| RHS application | `intern` | `add`, `add_lit`, `merge` |

`try_lookup` is the read-only probe: if a pattern requires literal
42 but 42 was never introduced, the probe returns `None` and the
match fails without polluting the store.

## Soundness Guarantees

The engine's primitive operations are sound by default. Every operation
that can fail (overflow, division by zero, lossy conversion) panics
rather than silently producing a wrong result. This prevents the
engine from deriving false equalities.

Wrapping and saturating variants use Rust's standard method names
(`wrapping_add`, `saturating_mul`, etc.) and require explicit opt-in.
Arbitrary-precision types (IBig, RBig) cannot overflow. Operations
that would produce unrepresentable results (e.g., `sqrt` on
rationals) are not provided.

When implementing a new `eval` function, the same principle applies:
if the operation can produce an incorrect result for some inputs, it
should panic rather than return a wrong value. The engine's
correctness depends on every derived equality being sound.

## Provided Models

| Model | Sorts | Use case |
|-------|-------|----------|
| `BignumModel` | bool, IBig, UBig, RBig | Arbitrary precision, sound by construction |
| `MachineModel` | bool, i64, u64, f64, usize, String | Fixed-width with checked overflow; strings backed by Rust `String` |
| `AllModel` | All of the above | Testing |

## Example: Adding a Custom Sort

Suppose you want to add a `Color` sort with RGB values:

```rust
enum MyValue {
    // ... existing variants ...
    Color(u8, u8, u8),
}

// In your LitModel implementation:
fn sorts(&self) -> &[LitSortDesc] {
    &[
        // ... existing sorts ...
        LitSortDesc {
            name: "Color",
            parse: |s| parse_color(s),  // e.g., "#FF0000"
        },
    ]
}

fn ops(&self) -> &[LitOpDesc<MyValue>] {
    &[
        // ... existing ops ...
        LitOpDesc {
            name: "Color::red",
            arg_sorts: &["Color"],
            ret_sort: "IBig",
            eval: |args| extract_red(args[0]),
        },
    ]
}
```

Users can then write:

```
(sort Pixel)
(function Fg (Color) Pixel)
(let p (Fg #FF0000))
```

The engine handles interning, hash-consing, and pattern matching
automatically.

---
[← Language Guide](A1-language-guide.md) · [Table of Contents](00-table-of-contents.md) · [Future Work →](A3-future-work.md)
