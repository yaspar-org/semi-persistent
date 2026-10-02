# Abstract Domains Proof Status

Last refreshed: 2026-10-02.

## Current result

```text
cargo verus verify
1235 verified, 0 errors
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
verified executable instance.

The separate Rust mirror suite contains 32 tests:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |

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


## Wrapped Domain port

`wrapped::Wrapped<W: Word>` uses the shared Domain and BotOr interface, one
instance per u8/u16/u32/u64 width. Private construction establishes wf; full-circle
arcs become Top. Nonemptiness, canonical representation, executable constant,
semantic is_top and modular-distance membership are verified. All Domain
operations prove their shared gamma soundness contracts. Meet also proves Bot iff
its exact intersection is empty. Join/meet precision and symmetry are tested;
no conventional lattice-law claim is made. Widen uses a cardinality-doubling
threshold with Top fallback; a verified postcondition additionally guarantees
that the result is unchanged, Top, or at least twice the previous cardinality.

The crate has 68 passing tests (32 mirrors, 3 shared-interface tests, 13 oracle
self-tests, 7 Wrapped core tests, 7 Wrapped arithmetic tests, 6 division/remainder tests), with one ignored doctest. u8 membership
and constructor canonicality are exhaustive; binary operations sample endpoints
and enumerate all concrete values for those pairs. Four-width boundaries and
actual BotOr lifting are covered. See testing/wrapped-oracle.md for details.
Arith<Signed<W>> and Arith<Unsigned<W>> implement modular add/sub/neg with
universal gamma containment proofs. Exact results are checked by exhaustive u8
arc negation, exhaustive singleton pairs and sampled arc pairs with exhaustive
concrete operands. General exactness is not a separate formal postcondition.
DivRem for both signed and unsigned semantics is implemented with splitting at
zero and the signed half-circle. Exact partition membership, coverage of all
pieces, magnitude conversion, signed quotient/remainder correspondence and
universal result containment are verified. The zero classifier proves exact
Never/Always cases, with Bot iff Always. The signed MIN/-1 operation wraps.
Quotient/remainder covers can overapproximate; no optimal-precision theorem is
claimed. Bitwise/shift/cast/comparison transfer traits remain future shared
interface work, as listed in domain-traits.md. No 128-bit Word support is claimed.
