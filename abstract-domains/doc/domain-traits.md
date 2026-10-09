# Domain traits: the shared interface for abstract domains

This document fixes the interface that every abstract domain in this crate
implements when its lattice operations are available. New domains and ports
of existing ones follow it. The code is in
`src/lattice.rs`, `src/word.rs`, `src/semantics.rs` and `src/transfer.rs`. The
two reference domains are `src/interval.rs` (machine words) and
`src/interval_z.rs` (unbounded integers).

## 1. Principles

1. **Bottomless domains, external bottom.** A domain value always denotes a
   nonempty set. Unreachability is `BotOr::Bot`, outside the domain. Anything
   that can produce the empty set returns `BotOr<Self>`: meet, backward
   refinement, reduction, and division whose divisors are all zero. A domain
   has no `is_bottom` or `empty` flag and no `Bottom` variant.
2. **Canonical representation.** `wf` admits exactly one value per
   concretization, and every leaf domain proves `lemma_canonical` in its
   `Canonical` impl. A `reduce::Product` is the exception: it is `Domain` but
   not `Canonical` (doc/reduced-product.md, "Products are not canonical"). Structural
   equality is then set equality, so a fixpoint test cannot miss
   stabilization and a join cannot lose precision on an equivalent encoding.
   An enum with a payload per case is preferred over a flag next to fields
   that the flag makes meaningless.
3. **Soundness contracts against `gamma`.** Every exec operation states that
   the concrete behaviour is contained in the concretization of the result.
   A contract that restates the implementation (`ensures r == join_spec(..)`)
   does not count.
4. **Machine domains store machine words.** They are generic over `W: Word`
   (u8..u128), use no big integers, and have their own internal top. Big
   integers are used only by unbounded domains.
5. **One carrier, several semantics.** A machine word is a bit pattern.
   Signed and unsigned are two semantics of the operators, not two domain
   instances.

## 2. Lattice (`lattice.rs`)

```rust
pub trait Domain: Sized {
    type C;                                   // concrete values
    spec fn wf(&self) -> bool;                // representation invariant
    spec fn gamma(&self, c: Self::C) -> bool;
    fn dup(&self) -> Self;                    // no Copy bound: big numbers
    fn top() -> Self;
    fn leq(&self, o: &Self) -> bool;          // true ==> gamma inclusion
    fn join(&self, o: &Self) -> Self;         // any sound upper bound
    fn meet(&self, o: &Self) -> BotOr<Self>;  // Bot ==> disjoint
    fn widen(&self, o: &Self) -> Self;        // covers self and o; see below
}
pub trait Canonical: Domain {
    proof fn lemma_nonempty(&self);           // bottomless
    proof fn lemma_canonical(a: &Self, b: &Self); // same gamma ==> a == b
}
pub enum BotOr<D> { Bot, Val(D) }
```

`BotOr<D>` lifts `leq`, `join`, `meet`, `widen`, `top` and `dup` with the same
contracts.

The contracts follow Verasco's `AdomLib.v` (`leb_correct`, `join_correct`,
`meet_correct`, `widen_incr`). Join is not required to be least: wrapped
intervals have no least upper bound (Navas et al. 2012; Gange et al. 2015).
**Widening.** In `self ∇ o`, `self` is the previous iterate and `o` the new
one. Callers test stabilization with `leq` and call `widen` only when `o`
escapes `self`, so `widen` need not detect the fixpoint itself. The contract
asks only that the result cover both arguments, which `join` satisfies; going
beyond `o` is permitted, not required, because requiring it means fixing a
termination measure, and that measure differs per domain. As in Verasco,
analysis termination comes from fuel (`CsharpminorIter.v`), and Jourdan's
thesis notes that termination is not needed for soundness. A domain with long
ascending chains should still go beyond `o` on the unstable bounds (to the end
of the range for intervals, doubling the arc for wrapped intervals, to the
next threshold) and document the measure it uses.

## 3. Words (`word.rs`)

`Word` gives generic code what it needs about a native unsigned integer:

- **Spec side:** `view() -> nat`, `modulus()`, `from_int(i) = i mod 2^N`, and
  lemmas for bounds, injectivity and `from_int`.
- **Spec side:** also `bits()`, with `modulus() == pow2(bits())`.
- **Exec side:** `zero`, `one`, `max`, `half`, `bit_width`, comparisons,
  `checked_add`, `checked_sub`, `checked_mul`, `wrapping_add`, `wrapping_sub`,
  `neg_nonzero`, `udiv`, `urem`, `trailing_zeros` (the 2-adic valuation,
  stated as `tz_spec`: `x = q * 2^t` with `q` odd) and `mulmod`.

`impl_word!` discharges the obligations once per width, for u8, u16, u32, u64
and u128. `signed_view` is the two's-complement reading.

**No wider type.** No operation needs an integer wider than `W`: products are
either checked (`checked_mul`) or reduced (`mulmod`), and a gcd with 2^N is
`2^min(trailing_zeros(m), bits)`. This is what makes u128 a `Word`. Up to u64,
`mulmod` multiplies in the next native type; for u128 it multiplies natively
when `m < 2^64` and otherwise doubles and adds over the bits of the second
operand, keeping every intermediate value below `m` (about 460 ns on an M4 Pro,
against 13 ns for u64). vstd specifies `trailing_zeros` up to u64; the u128
version splits the word into two u64 halves.

Width-specific facts go in the trait as lemmas proved in `impl_word!`. They are
not re-proved inside domain code. Domains that need `by (bit_vector)`
reasoning (Tnum, bitwise transfers) will extend `Word` with bitwise lemmas in
the same way. The per-width `abstract_domain!` stamping in `domains.rs` is the
pattern being replaced.

## 4. Semantics (`semantics.rs`)

A `Semantics` names a value type `V` and gives the spec meaning of `zero`,
`is_zero`, `add`, `sub`, `neg`, `mul`, `div` and `rem`.

| marker        | `V`   | arithmetic | division |
|---------------|-------|------------|----------|
| `Unsigned<W>` | `W`   | wrapping mod 2^N | unsigned |
| `Signed<W>`   | `W`   | wrapping mod 2^N | truncated on two's complement (MIN / -1 wraps) |
| `Euclid`      | `int` | exact | Euclidean (Verus `/`, SMT-LIB `div`) |
| `Trunc`       | `int` | exact | truncated toward zero (C, Rust) |

This follows Jourdan's machine-integer layer (thesis ch. 5). Operators that
commute with reduction mod 2^N (add, sub, mul, neg, and, or, not) mean the same
thing in both signednesses. The others (division, remainder, comparisons,
right shift) depend on signedness. Here that distinction lives in the
semantics a transfer trait is indexed by, not in the domain type.

## 5. Transfer functions (`transfer.rs`)

A transfer trait is `Trait<S: Semantics>: Domain<C = S::V>`, and a domain
implements it once per semantics it supports.

- `Arith<S>`: `add`, `sub`, `neg`. Their contract is
  `gamma(x) ∧ gamma'(y) ⟹ r.gamma(S::add(x, y))`.
- `Mul<S>`: `mul`, with the same contract shape.
- `DivRem<S>`: `contains_zero`, `div`, `rem`. Division returns
  `(BotOr<Self>, DivZero)`, with `DivZero::{Never, Maybe, Always}`:
  - the value covers every quotient by a **nonzero** divisor;
  - `Never` ⟹ the divisor excludes 0;
  - `Always` ⟹ the divisor is `{0}`;
  - the value is `Bot` ⟺ the flag is `Always`.

  The flag is the division-by-zero alarm. An analyzer reports `Maybe` and
  `Always` as alarms and continues with the value.

Planned next, with the same shape:

- `Compare<S>`: forward comparisons, plus backward refinement returning
  `BotOr<(Self, Self)>`.
- `Bitwise`.
- `Shift<S>`.
- `Cast`: truncation, zero extension and sign extension between widths.
- `Product<A, B>` with `reduce -> BotOr`: done in `reduce.rs`, see
  doc/reduced-product.md.

## 6. Reference domains

**`Interval<W>`** (`interval.rs`) has private `lo`/`hi` with `lo <= hi`;
`new` returns `None` otherwise. It implements:

- `Domain` and `Canonical`, with a proved `lemma_canonical`, and an exact
  `meet_exact`;
- Cousot widening;
- `Arith<Unsigned<W>>`: add and sub exact when no result wraps or every
  result wraps once, top otherwise;
- `Mul<Unsigned<W>>`: `[lo * o.lo, hi * o.hi]` when no product wraps, top
  otherwise;
- `DivRem<Unsigned<W>>`: precise division `[lo / d.hi, hi / d.lo']`;
  remainder `[lo - q * d.hi, min(hi - q * d.lo', d.hi - 1)]` when every
  quotient is the same `q` (which makes it exact on singletons and the
  identity when `hi < d.lo`), `[0, min(hi, d.hi - 1)]` otherwise;
- `DivRem<Signed<W>>`: sound placeholder (top plus the exact zero flag).

**`IntervalZ`** (`interval_z.rs`) has `enum Lo { NegInf, Fin(IBig) }` and
`enum Hi { Fin(IBig), PosInf }`, private fields, and `lo <= hi` when both are
finite. It has an internal top `[-inf, +inf]`, so it needs no Verasco `t+⊤`
lift. It implements:

- `Domain` and `Canonical`, with Cousot widening and an exact `meet_exact`;
- `Arith<Euclid>` and `Arith<Trunc>`, both exact;
- `DivRem<Euclid>` and `DivRem<Trunc>` as sound placeholders (top plus the
  exact zero flag).

`tests/domain_traits.rs` checks both domains at runtime against brute-force
concretization.

**`Congruence<W>`** (`congruence.rs`, PR #106) currently supplies the semantic
core only: private canonical fields, `wf`, unsigned `gamma`/`has`, executable
membership, normalized constructors, and inherent `lemma_nonempty` and
`lemma_canonical` with the same obligations as `Canonical`. A progression must
have at least two representable members; otherwise it normalizes to a
singleton. `tests/congruence.rs` exhaustively checks the real u8 implementation.
Its full `impl Domain` is deferred to #114 because this trait requires
`leq`, `join`, `meet`, and `widen`; no placeholder lattice operations or
arithmetic transfers are supplied by the semantic core.

## 7. Trust

Machine domains add nothing to the trust boundary. `IBig` (`ibig.rs`) is a
thin wrapper over `num_bigint::BigInt`. Its trusted items are:

| item | kind | justification |
|------|------|---------------|
| `IBig` | `external_body` struct | opaque; `view()` is its only spec observer |
| `from_i64`, `to_i64`, `dup`, `le`, `is_zero`, `add`, `neg` | `external_body` fns | one-line calls to `num-bigint` / `num-traits` whose contract is the integer operation |
| `axiom_view_injective` | axiom | `BigInt` is normalized sign-magnitude, and `view` is the only observer |

Every new `IBig` operation must be added to this table. A rational
counterpart (`RBig` over `num_rational::BigRational`) must normalize before
it can claim injectivity. Un-normalized rationals falsify it.

## 8. Porting checklist

- [ ] Payload struct or enum with no bottom flag and no `Bottom` variant. Empty results are `BotOr::Bot`.
- [ ] `wf` is canonical and `lemma_canonical` is proved in `impl Canonical`. Enumerate small widths to confirm there is one value per set.
- [ ] Fields are private, and constructors establish `wf`.
- [ ] Generic over `W: Word`, one instance per width (not per signedness). No `IBig` in a machine domain.
- [ ] `impl Domain`, with `top`, `leq`, `join`, `meet -> BotOr` and `widen` stated against `gamma`.
- [ ] Transfer traits for each semantics the domain supports. Division uses `DivZero`.
- [ ] Explicit `#[trigger]`s, not `#![auto]`.
- [ ] Exhaustive u8 runtime test against brute force.

## 9. Relation to Verasco

| | Verasco | here |
|---|---|---|
| bottom | external `t+⊥` (`botlift`: `Bot \| NotBot`) | `BotOr<D>` |
| top | internal in machine domains; `t+⊤` (`toplift`) for ideal Z domains | internal everywhere; `IntervalZ` represents `[-inf, +inf]` |
| lattice contracts | soundness (`AdomLib.v`) | the same |
| canonicity | not required | required (`lemma_canonical`), after Laporte's note on same-concretization representatives (thesis §3.3.3) |
| machine integers | ideal Z domains plus a translation layer (`IdealEnvToMachineEnv`) | word-level domains, with signedness in `Semantics` |
| termination | fuel | fuel; widening is soundness-only |

References:

- J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy, D. Pichardie. *A
  Formally-Verified C Static Analyzer.* POPL 2015 (source distribution
  verasco-1.3).
- J.-H. Jourdan. *Verasco: a Formally Verified C Static Analyzer.* PhD thesis,
  Université Paris Diderot, 2016.
- V. Laporte. *Verified Static Analyzes for Low-Level Languages.* PhD thesis,
  Université Rennes 1, 2015.
- P. Cousot, R. Cousot. POPL 1977.
- P. Granger. *Static analysis of arithmetical congruences.* 1989.
- J. A. Navas, P. Schachte, H. Søndergaard, P. J. Stuckey. *Signedness-Agnostic
  Program Analysis.* APLAS 2012.
- G. Gange et al. *Interval Analysis and Machine Arithmetic.* TOPLAS 2015.
- G. Balakrishnan, T. Reps. CC 2004.
