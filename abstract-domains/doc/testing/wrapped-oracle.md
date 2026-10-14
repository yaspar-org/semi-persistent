# Wrapped interval verification and oracle tests

## Public interface

`wrapped::Wrapped<W: Word>` is a single domain per bit width. The current Word
instances are u8, u16, u32 and u64. Signed interpretation uses the same bit
patterns; signedness belongs to transfer semantics, not a second domain type.
No u128 Word implementation is currently provided.

The private representation is Top or a nonempty clockwise arc. `new(lo, hi)`
converts every full-circle arc to Top; callers cannot construct a raw arc.
`constant` is executable. `wf` excludes full-circle arcs, and `lemma_canonical`
proves that equal concretizations of well-formed values imply structural equality.
`is_top` is equivalent to containing the entire universe for well-formed values.

Membership compares clockwise distances from lo. Distance is x-lo when x>=lo
and 2^N-lo+x otherwise: the nonnegative modular distance, including wraparound.
`contains` proves equivalence to `Domain::gamma`. `lemma_nonempty` proves that
all well-formed inner values contain a concrete word. Empty results and lifted
operations use the shared `lattice::BotOr`, not a domain-specific wrapper.

## Domain operations

`leq`, `join`, `meet` and `widen` implement the shared Domain contracts against
gamma. Join chooses the smaller covering arc; split meet preserves both exact
intersection components and chooses their smaller cover. Equal-size choices use
the unsigned lower endpoint. These operations are not ordinary lattice joins
and meets; associativity and monotonicity must not be assumed.

Meet additionally proves Bot if and only if the exact intersection is empty.
Widen leaves contained inputs unchanged. Otherwise it accepts the joined arc only
when cardinality at least doubles, and jumps to Top for smaller growth. Thus an
unstable step increases cardinality by at least a factor of two, capped at 2^N;
the measure is the number of remaining doublings. Besides shared soundness,
the implementation formally proves that each result is unchanged, Top, or at
least twice the previous cardinality. Growth is also runtime-tested.

## Modular arithmetic

Both `Arith<Unsigned<W>>` and `Arith<Signed<W>>` provide add, sub and neg.
Addition sums clockwise spans: if the combined span cannot fit a word, the
result is Top; otherwise the endpoints are added modulo the word modulus and
the constructor canonicalizes a full-circle result. Negation reverses and
negates the endpoints. Subtraction adds the negated right operand. The
implementation uses checked native arithmetic and never overflows a host integer.
Signed and unsigned operations are proved to agree on the resulting bit patterns.
All enabled arithmetic transfers prove universal containment against gamma.

Seven arithmetic tests exercise actual transfers: negation over every u8 arc,
all u8 singleton pairs, 4,225 sampled abstract pairs with all concrete operand
pairs, and boundaries at all four widths. Expected sets use Rust wrapping
operations over independently enumerated input sets. They check exact sets,
not only containment. These finite tests are not a universal exactness proof.

## Division and remainder

`DivRem<Unsigned<W>>` and `DivRem<Signed<W>>` classify the divisor as Never,
Maybe or Always zero. Only an all-zero divisor produces Bot. `contains_zero`
is exact. Zero divisors are excluded from quotient/remainder computation and
reported through the flag.

Inputs split into up to four non-wrapping pieces at zero and the signed
half-circle. Both the membership of each piece and coverage of the original
input are proved. Unsigned pieces use the existing verified linear Interval
transfers. Signed pieces convert to magnitude intervals, compute the unsigned
operation, and restore the sign: quotient uses operand-sign XOR, remainder uses
the dividend sign. MIN/-1 follows the shared wrapping semantics. The final
result is a deterministic join of all piece-pair results.

The reuse of Interval remainder bounds and the final single-arc cover can add
spurious values. Remainder is not claimed exact even for every singleton pair.
Six tests check all u8 singleton operand pairs, 4,225 sampled abstract pairs
with exhaustive concrete operands, exact zero flags, and boundaries at all four
widths. Expected signed values use Rust wrapping_div/wrapping_rem; division by
zero is checked separately. These tests check containment for general results.

## Tests and limits

- 13 independent oracle self-tests cover small model widths, reference operations
  and sparse u32 cases. They are not production arithmetic verification.
- The production membership test enumerates all 65,536 u8 endpoint pairs and
  every u8 value. It checks the same bits under signed reinterpretation and
  records one canonical representation per concrete set, including Top.
- The operation test covers 66,049 ordered pairs from 16 sampled endpoints plus
  Top, checking all 256 values per pair. It checks containment, exact leq,
  Bot iff disjoint, symmetry, minimum covering cardinality via an independent
  longest-gap oracle, and widening growth. This is not every possible u8 pair.
- A split-intersection regression and actual shared BotOr lifting are exercised.
- Four-width boundary tests include constants, sign boundaries and full circles.

```sh
cargo test -p semi-persistent-abstract-domains
cargo verus verify --manifest-path abstract-domains/Cargo.toml
```

Use the versions pinned by the repository. Proof totals and scope are recorded
in `doc/proof-status.md`. The implemented shared interfaces are Domain, Arith
and DivRem. Bitwise, Shift, Cast and Compare are listed as future shared traits
in domain-traits.md; this port does not introduce competing interfaces for them.
