# Abstract Domains Proof Status

Last refreshed: 2026-09-25.

## Current result

```text
cargo verus verify
1254 verified, 0 errors
```

The project source contains no executable `admit()` or `assume()` calls. CI
enforces that policy with a source scan and runs ordinary Verus verification.
The pinned `vstd` dependency contains admitted specifications; global
`--no-cheating` fails while compiling `vstd` before reaching this crate. Those
dependency specifications, Verus, and the solver remain part of the trust
boundary.

Enabled executable widths:

- `d8` (`u8`)
- `d16` (`u16`)
- `d32` (`u32`)
- `d64` (`u64`)

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. Do not describe `u128` as an enabled or
verified executable instance. The CRT implementation uses verified `u128`
intermediates for the four enabled widths; this does not enable `d128`.

The separate Rust mirror suite contains 38 tests:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

The CRT suite calls the actual executable helpers and contains 4 passing tests,
one for each enabled width:

```text
cargo test -p semi-persistent-abstract-domains --test crt
```

It covers normalized inputs, compatible and incompatible constraints, and LCM
overflow with a representable solution (including `MAX`) or no representable
solution. The 38 mirror tests and 4 CRT tests pass; the universal helper
contracts are established by Verus.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
| L4 | Shared GCD/CRT helpers | explicit contracts verified at all four enabled widths; exact CRT results and overflow handling |
| L4 | `Congruence` | representation, membership semantics, and normalization implemented; constructor/normalization contracts, refinement, join/meet/arithmetic, and shared Bottom integration remain follow-up work |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `ReducedProduct` | `reduce`, `add` |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. `ReducedProduct::add` composes the four component containment
postconditions and then applies the proved containment of `reduce`.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
Unum conversions/arithmetic helpers, and ReducedProduct bitwise operations,
subtraction, multiplication, division, shifts, joins, meets, and negation.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.

### Shared arithmetic helpers

The helpers remain inside `abstract_domain!` in `domains.rs` for use by
Congruence and future Strided Interval operations.

- `gcd` proves `is_gcd`, including `gcd(0, 0) = 0`, using the Euclidean-step lemma.
- `extended_gcd` proves the GCD, Bézout identity, and coefficient bounds.
- `crt_compatible` checks residue compatibility modulo the GCD. Supporting
  lemmas prove that common solutions imply compatibility and incompatible
  constraints have no common integer solution.
- `checked_lcm` returns the exact LCM when it fits in `$uint`; `None` proves
  that the exact LCM exceeds the width's maximum. Both inputs must be positive.
- `crt_merge` accepts positive moduli and normalizes the input residues.
  Its result distinguishes the following cases:

| Result | Verified guarantee |
| --- | --- |
| `Merged { modulus, residue }` | The modulus is the exact LCM, the residue is canonical, and the class represents exactly all common integer solutions. |
| `Incompatible` | There is no common integer solution. |
| `ModulusOverflow { wide_residue }` | The inputs are compatible and the exact LCM exceeds `MAX`. The canonical common residue is computed in `u128`; a representable value is a common solution exactly when it equals `wide_residue`. |

In the overflow case, `wide_residue <= MAX` identifies the unique representable
solution; otherwise the representable intersection is empty. The executable
arithmetic is verified to avoid overflow. These helpers handle regular modular
constraints only; Singleton, Bottom, and interval bounds belong to callers.

### Congruence

`Congruence` uses canonical representations for Singleton
(`modulus = 0, residue = x`) and Top (`modulus = 1, residue = 0`).
It defines membership semantics through the `has` specification and the
executable `contains` method, with a postcondition connecting
`contains` to `has`. Residue normalization is also implemented. `constant`,
`top`, and `normalize` do not yet carry semantic postconditions; their
implementation is not a proof of those domain-level properties.

The Rust mirror suite includes a finite membership oracle covering 1,024
small input combinations, plus tests for compatible and incompatible
congruence classes. These finite tests are not a universal proof
of the domain's operations.

Refinement, join, meet, arithmetic transfers, and shared Bottom integration are
not yet implemented. The Bottom representation remains pending design review;
this work introduces no domain-specific Bottom encoding.
