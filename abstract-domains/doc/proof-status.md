# Abstract Domains Proof Status

Last refreshed: 2026-11-02.

## Current result

`cargo verus verify` reports 0 errors; CI runs it on every pull request. This
file does not record the number of verified items, because every change to the
crate moves it.

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

`ExecTnum<W>`, `ExecAnum<W>` and `ExecUnum<W>` are proved once for every
`W: BitWord`, and `u128` is a `BitWord`, but no `d128` alias or test exercises
them at u128.
Only generic code over `W: Word` exercises `u128`: `Word`, the shared
GCD/CRT helpers, `Interval<W>`, `Wrapped<W>` and `Congruence<W>`. The
arithmetic helpers compute in `W`; they do not use widened intermediates.

The separate Rust mirror suite can be run with:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

The CRT/helper suite calls the real shared `arithmetic` implementation:

```text
cargo test --test crt
```

The tests cover all five word widths, GCD properties, machine-modulus GCD
values and exponents, and exact finite CRT outcomes. The exhaustive u8 oracle
precomputes each input class by testing all 256 concrete values, then compares
bitset intersections against the helper for all 532,701,120 unordered pairs of
the 32,640 normalized positive-modulus descriptions (including duplicate finite
singleton encodings). Separate checks exercise every raw u8 residue with six
partner classes in both operand orders. The full oracle remains enabled in
debug tests and CI; it is neither ignored nor gated on release builds.

The u128 cases distinguish LCM overflow, candidate multiplication overflow,
candidate addition overflow, and a candidate equal to `MAX`. An independent
`num-bigint` oracle checks boundary grids, deterministic full-width samples,
and long Euclidean chains from consecutive Fibonacci numbers. Arbitrary-precision
arithmetic is confined to tests and erased mathematical proofs.

To time the same exhaustive oracle in release mode without changing coverage:

```text
cargo test -p semi-persistent-abstract-domains --release --test crt exhaustive_u8_crt_intersections -- --exact
```

The `Domain`-trait suite (`doc/domain-traits.md`'s convention) instead calls
the real executable code directly and checks it against brute-force
concretization on samples of `u8` values, with no hand-written
reimplementation to drift out of sync:

```text
cargo test -p semi-persistent-abstract-domains --test domain_traits
```

The reduced-product suite checks the reduction protocol (`src/reduce.rs`) and
the fact records against brute-force concretization at `u8`, plus `u128`
instances (`doc/reduced-product.md`):

```text
cargo test -p semi-persistent-abstract-domains --test reduced_product
```

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum<W>`, `ExecAnum<W>`, `ExecUnum<W>` for every `W: BitWord`; `Interval<W>` for every `W: Word` | every method verifies its stated contract; containment scope is listed below |
| L4 | `ExecTnum<W>` as a domain | `Domain` (sound `leq`; `meet` returns `BotOr` and holds exactly the common members), `Canonical` (`lemma_nonempty`, `lemma_canonical` proved) and `Refine` with `Facts<W>`; reduces in a `Product` |
| L4 | Shared GCD/CRT helpers | shared mathematical proofs, deterministic GCD, modular inverse, exact finite CRT and machine-modulus GCD verified |
| L4 | `Congruence<W>` | generic canonical `Domain`; exact refinement/meet, LUB join, join-based widen, and sound unsigned add/sub/neg |
| L4 | `StridedInterval<W>` (`strided.rs`), ported onto the shared `Domain`/`Word` traits from `doc/domain-traits.md` | `wf` is canonical (`lemma_canonical` proved); `leq`/`join`/`meet`/`widen` implemented; not yet in a `Product` |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `constant`, `bw_or`, `bw_and`, `bw_xor`, `bw_not`, `bw_and_not`, `add`, `neg`, `sub`, `mul`, `divrem_g`, `divrem`, `join`, `meet`, `rsh`, `lsh`, `rshi`, `lshi` |
| `ExecAnum` | `constant`, `top`, `add`, `sub`, `neg`, `mul`, `mul_precise`, `div_const`, `bw_and`, `bw_or`, `bw_xor`, `bw_not`, `lshi`, `rshi`, `join`, `meet`, `from_etn`, `to_etn` |
| `ExecUnum` | `constant`, `top`, `add`, `neg`, `sub`, `mul`, `from_interval`, `from_ean`, `to_ean`, `to_etn` |
| `Interval<W>` | every operation: `Domain`, `meet_exact`, `add`, `sub`, `neg`, `mul`, `div`, `rem`, `and`, `or`, `xor`, `not`, `shl`, `shr` |
| `Congruence<W>` | exact `refines`/`leq`/`meet`, LUB `join`, `widen`, unsigned `add`/`sub`/`neg` |
| `StridedInterval<W>` | `new`, `constant`, `leq` (sound and complete), `join`, `meet`, `widen`; precision caveats below |

The `ExecUnum` proofs use the `BitWord` bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. `neg` reflects through 2^W with the same fields, by the L2
`Unum::complement_admitted`; the conversions use `Unum::to_anum_sound` and
`Unum::submask_admitted`, and `to_etn` goes through `ExecAnum::to_etn`. #123 removed `ReducedProduct`, whose `reduce` and `add` carried
containment theorems; `reduce::Product` replaces it.

The other executable methods of `ExecTnum`, `ExecAnum` and `ExecUnum` are
helpers (`min_val`, `max_val`, `is_const`, `meet_m`, `range_tn`, `chop_to`,
`ones_mask`) whose postconditions state their exact result.

### StridedInterval

`StridedInterval<W>` (`src/strided.rs`) is ported onto the shared
`Domain`/`Word`/`lattice::BotOr` interface fixed by `doc/domain-traits.md`
(added in #116), whose reference ports are `Interval<W>` and `IntervalZ`
(`interval.rs`, `interval_z.rs`). Every machine-word domain, including
`ExecTnum`, `ExecAnum` and `ExecUnum`, is now generic over `W`; `domains.rs`
only names them at each width.

`wf` is canonical: `stride == 0 <==> lo == hi`, and when `stride > 0`,
`(hi - lo) % stride == 0`. Unlike the pre-port representation, `(0,7,7)`,
`(2,7,7)`, and `(5,7,7)` are no longer three legal encodings of `{7}` --
only `(0,7,7)` is well-formed, and `lemma_canonical` proves that any two
wf values with the same concretization are the same value. `leq`, `join`,
`meet`, and `widen` are all proved sound against `gamma`, and `leq` is
also proved complete (`b <==> gamma(self) ⊆ gamma(o)`). `new` exports
exactly which set it builds, and `constant(c)` builds `{c}`. No other
contract states optimality or exactness. Known precision gaps, none of
which is a soundness bug:

- `meet` is not proved exact: its `Val` contract only says the result
  contains the intersection. It is exact (and `Bot` exactly when the
  intersection is empty) when one operand is a singleton or one stride
  divides the other, which includes `meet(top(), x) == x`; the tests
  check this on a sample of u8 values. When neither stride divides
  the other, `meet` clips the larger-stride operand to the common bounds,
  which may keep points off the other grid and may return a value for an
  empty intersection. `meet` is commutative in all cases.
- When both operands share a nonzero stride and residue class, `join`
  is the least upper bound but **not** the exact union --
  widening the range can span a gap neither operand covers. `join(si(3,
  2,8), si(3,14,17))` claims `11`, which is in neither operand
  (`strided_join_same_residue_is_not_always_exact` in
  `tests/domain_traits.rs` pins this down after "the same-stride join is
  exact" was flagged as a misleading claim in review). `join` is exact
  in some cases, for example two distinct singletons (a two-point set has
  no gap) and `{4} ⊔ (2,0,10) = (2,0,10)`. In general `join` keeps the
  bounds `[min lo, max hi]` and uses an operand's stride when it divides
  the other stride and the distance between the `lo`s, else stride 1.
- `widen` keeps the join's stride and moves an unstable bound to the last
  grid point before the end of the range rather than to 0/MAX, which
  would usually be off the grid. On `i = 0; while i < 200 { i += 4 }` it
  reaches `(4,0,252)`, and one decreasing iteration gives `(4,0,200)`
  (`strided_widen_keeps_the_stride`).

The tight join stride is `gcd(s1, s2, |lo1 - lo2|)` (Balakrishnan &
Reps), and the exact meet for non-dividing strides needs CRT. Both come
from the `gcd`/`crt_merge` helpers in #112, which has not landed yet.
Arithmetic transfers and reduction into a `Product` are still open.

### Shared arithmetic helpers

`src/arithmetic.rs` owns the shared foundation; the width-independent `int`/
`nat` proofs are not instantiated by `abstract_domain!`. Runtime code uses
only the upstream `Word` interface, with no `Word64` bound, conversion bridges,
or wider integer arithmetic. The generic APIs support u8/u16/u32/u64/u128.
The measured widening internal to upstream `Word::mulmod` remains unchanged.

- `gcd_spec` is deterministic and recursive, decreasing on the second operand.
  `gcd<W>` is unchanged and returns exactly this specification. Shared proofs
  establish divisibility of both inputs, Euclidean-step correctness, uniqueness,
  divisibility maximality, symmetry and associativity, including zero inputs.
- A private iterative extended-Euclid helper computes the inverse of `m1/g`
  modulo `n = m2/g`. Only one coefficient per Euclidean state is stored at
  runtime, reduced with `mulmod` and modular subtraction. Loop invariants prove
  the GCD, coefficient congruences and decreasing remainders. Signed Bézout
  witnesses exist only in erased ghost code. Modulus one is handled explicitly.
- `crt_merge<W>` retains its public signature, requires **positive moduli**,
  and accepts unreduced residues. Its unchanged `wf` and `has` contracts exactly
  describe all representable common solutions. `checked_mul` computes the LCM,
  `mulmod` computes `k`, and `checked_mul`/`checked_add` construct the candidate.
  Proofs establish that the mathematical candidate is the least nonnegative
  solution and is strictly below the exact LCM, without executing either in a
  wider type. Candidate overflow therefore means `Empty`; LCM overflow alone
  does not. A representable candidate is a `Singleton` if the LCM overflows or
  adding the LCM cannot reach a second representable member.

| Result | Verified finite-word meaning |
| --- | --- |
| `Class { modulus, residue }` | `0 < modulus`, `residue < modulus`, and `residue + modulus < W::modulus()`; the class contains at least two words and is exactly the intersection. |
| `Singleton { value }` | Exactly one representable common solution, whether the LCM overflows the word or merely cannot reach a second member from the residue. |
| `Empty` | No representable common solution, including incompatible constraints and compatible classes whose least solution exceeds `MAX`. |

Callers no longer inspect a widened residue or reconstruct overflow cases.
Congruence's modulus-zero constants must be handled **before** calling CRT.
The helper stays independent of `BotOr`; Congruence meet maps its result.
The unused `crt_compatible` and `checked_lcm` executables were removed after
checking callers; their necessary mathematical facts remain shared. There are
no existential GCD result specifications or `#![auto]` shortcuts in this module.
Unrelated pre-existing domain proofs retain their existing annotations.

`gcd_machine_modulus<W>(m) -> W` now requires `m.view() > 0` and computes
`gcd(m, m.neg_nonzero())`, proved equal to `gcd(m, 2^bits)`. It retains the exact
GCD and divisibility guarantees with `r.view()` replacing the old u128 cast.

`gcd_machine_modulus_exponent<W>(m) -> u32` is total and uses `trailing_zeros`.
Its contract states `pow2(result) == gcd_spec(m.view(), W::modulus())`, with
`result == bits` for zero and `result < bits` otherwise. Thus zero at u128 is
represented by exponent 128, never by an ordinary word pretending to hold
2^128. `lemma_gcd_pow2` proves this interpretation from the valuation contract.
`lemma_wrapping_congruence` remains unchanged and covers negative integers too.

The runtime `ExtendedGcd`/`extended_gcd` API and the unused `gcd_wide`,
`mul_wide`, and `granger_modulus` helpers were removed after checking production
callers on the available branches and the dependent PRs. Their old tests were
adapted to the retained GCD API and new modular/CRT behavior; tests specific to
removed widened products were retired. Public ghost/spec Bézout and CRT lemmas,
including `is_extended_gcd` and `lemma_crt_solution_class_exact`, remain available.

The shared-helper change adds no multiplication transfer or reduced-product
integration. Congruence `Refine` with `Facts.c` and grid reduction are now
implemented separately, with export soundness, refinement preservation,
no growth, and well-formedness proved. No proof bypasses or new trusted items
were introduced.

### Congruence

`src/congruence.rs` implements the domain as `Congruence<W: Word>`
(with the bound on its implementation). Fields are private. The existing
`domains::d8/d16/d32/d64::Congruence` names are aliases of the generic type.
The canonical representation is:

- Singleton: `modulus = 0, residue = x`.
- Progression: `0 < modulus`, `residue < modulus`, and
  `residue + modulus < W::modulus()` in mathematical arithmetic.
- Top: the unique progression `(1, 0)`.

`gamma` (also exposed as `has`) interprets words as unsigned finite-width
values. A singleton contains exactly its residue; a progression contains
exactly the words whose remainder modulo its modulus is its residue.
`contains` is proved equivalent to both specifications. This is set membership,
not a signed or wrapping arithmetic transfer semantics. Equivalently, `gamma`
is the integer congruence restricted to the finite unsigned word range.
Wrapping arithmetic can lose exactness: at u8, adding 1 to `(3, 0)` produces
`{0, 1, 4, ..., 253}`, since 255 wraps to 0. Any congruence containing both
0 and 1 is Top, so the best congruence abstraction is Top. A no-wrap condition
can preserve the integer-congruence precision; uniform-wrap cases also preserve
the stride. Mixed-wrap cases can still lose precision as described below.

`new(m, r)` normalizes a raw class: for `m = 0` it denotes `{r}`, otherwise
it denotes `{x | x % m = r % m}`. The constructor proves preservation of the
raw class through `raw_has` and establishes `wf`. It uses `Word::urem` and
`checked_add`; when the normalized residue plus the modulus is not
representable, it returns a singleton.
For example, `Congruence::<u8>::new(201, 200)` has the same canonical pair as
`constant(200)`. `constant` and `top` have semantic and representation contracts.
The constructor also exposes all three canonical results through the public
`modulus()` and `residue()` accessors: the input constant, the reduced class
when its second member fits, or the collapsed constant otherwise.
Constructed values implement `Clone, Copy`; `clone` proves structural equality.
There is no identity `normalize` method.
`is_top` and `as_constant` recognize exactly the universal and singleton sets.
`same` uses two field comparisons and proves both structural and gamma equality.

Public `lemma_residue_member` witnesses the residue; `lemma_member_decomposition` gives
its least-member bound, quotient decomposition, and the gap to any later member.
Public `lemma_second` constructs the representable second member. These methods
state their contracts with public spec accessors. Public `lemma_next` supplies
the gap fact using the same accessors, requiring only reduction rather than
full canonicality so it also applies before singleton collapse.
`lemma_nonempty` follows from residue membership. `lemma_canonical` proves
that equal gamma sets of well-formed values imply structural equality: residues are the
least members, and nonconstant steps are determined by the second members.
Both use the common `Canonical` proof obligations as inherent methods, without
proof bypasses or changes to the trust boundary.

Congruence implements `Domain<C = W>`, `Canonical`, and `Arith<Unsigned<W>>` on this carrier.
There is no internal bottom: exact meet returns `BotOr::Bot` iff the
intersection is empty. Positive-modulus inputs use the shared CRT helper;
constants are handled before calling it. Nonempty results are canonical.

`refines` and `Domain::leq` decide semantic containment exactly. Join uses
`gcd(gcd(s1, s2), abs(r1-r2))`; its contract proves both upper-bound properties
and containment in **every** common upper bound. The proof uses canonical
first/second members to force stride divisibility, then the shared GCD
maximal-divisibility lemmas. `widen` calls join. For a fixed finite word
universe there are finitely many canonical sets, so ascending chains
stabilize; the interface itself requires only upper-bound soundness.

`max_member` proves membership and an upper bound on every represented word.
It uses `W::max()`, `wrapping_sub`, and `urem`. Join computes the unsigned
residue distance in `W`; arithmetic has no widened intermediates or conversion
bridges and supports `Congruence<u128>`.

Addition starts with `wrapping_add` and one stride GCD. Its extreme-member
`checked_add` checks distinguish no wrapping, uniform wrapping, and mixed
wrapping. Direct subtraction starts with `wrapping_sub`, one stride GCD,
and corresponding `checked_sub` checks. Uniform cases retain the stride;
mixed cases use the nonzero `gcd_machine_modulus` helper. The zero-stride
case means both operands are constants and returns before calling that helper;
there is no attempt to represent the machine modulus as a word. The exponent
helper remains available for clients needing to represent that zero-input GCD.
The shared helper performs its own necessary machine-modulus GCD only in the
mixed case; subtraction does not construct an intermediate abstract negation.

Negation is direct subtraction from zero. When zero is absent, every member
wraps uniformly and the stride survives. In particular, u8 `neg(3Z+1)` gives
`3Z`, and `neg(5Z+3)` gives `5Z+3`. The inherent and `Arith<Unsigned<W>>`
contracts explicitly prove modulus zero and the exact unsigned result residue
for constant add/sub/neg, in addition to unchanged universal soundness.

This implementation chooses a sound fallback for mixed-wrapping add/sub:
when results cross a wrap boundary, it uses `gcd(stride, 2^N)`, where
`stride = gcd(s1, s2)` and `N` is the word width. The
`lemma_wrapping_congruence` proof guarantees soundness, but the fallback
does not guarantee optimal precision or implement full split-range stride
analysis. No-wrap and uniform-wrap cases retain the stride, as described above.
For example, at u8, `new(129, 0) + constant(127)` returns Top, while the
concrete result set is `{127, 0}` and its best congruence abstraction is
`new(127, 0)`. `neg(new(129, 0))` has the same limitation.
The rank/stabilization theorem, signed arithmetic instance, and meet containment
fast path remain permitted follow-ups. Multiplication and division are deferred.
Quantified proofs use explicit triggers; these operations add no trusted items.

The Congruence runtime suite checks:

- All 65,536 raw u8 pairs against all 256 words, including normalization,
  nonemptiness, canonical invariants, and unique representation of all 16,640 sets.
- All 16,640 canonical u8 classes for exact maximum, negation soundness,
  and optimal negation when zero is absent.
- All 65,536 u8 constant operand pairs for exact add/sub, and all constants
  for exact negation in the unary oracle.
- All 16,640 canonical classes against all 256 constants (4,259,840 pairs),
  checking every concrete member for add and both subtraction orders, and
  comparing uniform-wrap precision against an independent best-class oracle.
- A 99-description boundary-focused family for exact refinement/meet,
  LUB join against **all 16,640 possible canonical upper bounds**, widen,
  and add/sub over every concrete operand pair. This does not enumerate all
  pairs of nonconstant canonical abstract inputs.
- Trait and inherent API regressions at u8/u16/u32/u64/u128, external Bottom,
  constants/top, singleton collapse, CRT outcomes, and existing width aliases.
  u128 arithmetic tests include bit 64, bit 127, MAX, zero, and wrapping.

Verification uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.

The finite-height/rank theorem remains future lattice work; this domain does
not yet prove the termination bound for join-based widening.

### Congruence lattice verification

`src/congruence_laws.rs` verifies structural idempotence, commutativity,
associativity, top/bottom identity and absorption for meet and join (ten laws).
The private generic verification harnesses cover every `W: Word`, including
u128. They call existing Congruence operations through local copies of the `BotOr` meet/join
cases in `lattice.rs` to retain exact intersection and
LUB contracts, which the general `Domain` interface intentionally does not
require. Canonical uniqueness lifts semantic equality to structural equality;
nonemptiness distinguishes values from bottom. No arithmetic algorithms,
existing contracts, or trust assumptions are changed.

The `small_model_transfers_and_lattice_laws` oracle enumerates all 81 raw descriptions with
modulus/residue in `0..=8`, all 6,561 ordered input pairs, and all 256 concrete
u8 values (including wrapping results). It checks canonicalization, exact
refinement/intersection, join/widen containment, and add/sub/neg containment
using concrete bitsets. All ordered triples (with repetition) of deduplicated canonical states from
that family plus bottom check the actual `BotOr` meet/join associativity; unary and
binary checks cover the other eight laws. Existing full-u8 normalization,
negation, boundary, and all-canonical-upper-bound tests remain in place.
The oracle is exhaustive within its stated input model, not over every pair
or triple of all 16,640 canonical u8 classes.

### Grid rounding

`src/grid.rs` rounds a word onto the grid of a congruence `(r, m)`:
`{x | x % m == r}`, or `{r}` when `m == 0`. These helpers are the
interval/congruence grid step of `Facts::normalize`
(`doc/reduced-product.md`). `round_up(x, r, m)`
returns the smallest grid point `>= x` and `round_down(x, r, m)` the
largest grid point `<= x`. Both contracts state optimality, not only
membership: no grid point lies strictly between `x` and the result.
`None` means no grid point exists on that side within `W`, so both
functions return `None` where the arithmetic would wrap. They are generic
over `W: Word` and compute only with `urem`, `checked_add` and
`checked_sub`. The tests check them against brute force on every
well-formed `(x, r, m)` at `u8`, and on hand-computed boundary cases at
`u128`:

```text
cargo test -p semi-persistent-abstract-domains --test grid
```

### Facts congruence field

`Facts<W>` (`src/facts.rs`) has a congruence field `c` next to the unsigned
bounds `u`, and `γ` is the intersection of the two. `reduced` states that both
bounds of `u` lie on the grid of `c` and that a single value is a constant
congruence; `normalize` establishes it with `round_up` and `round_down`, and
returns `Bot` exactly when the fields share no value. `lemma_canonical`
proves that reduced records with the same concretization are equal: the
bounds are the least and greatest members, and past one value the modulus is
the gap to the second member. The singleton case reduces both ways: a
constant `c` collapses `u` to that value, and a single-value `u` makes `c`
constant, also in `from_interval`. So `from_interval` sets `c` to top only
when `u` has two or more values. `join`, `widen` and `meet` apply the grid
step after the field-wise operation; `leq` is field-wise. `from_parts(u, c)`
builds the reduced record of two facts. `contains_zero` now checks both
fields, because its contract is exact. Unsigned add/sub/neg in `facts_ops.rs`
now compute both `u` and `c`, combined by `lift_parts` through `from_parts`.
The contracts prove sound arithmetic and well-formedness; an empty field
intersection permits the helper's Top fallback. The existing mixed-wrap GCD
fallback is unchanged, with no general arithmetic optimality claim.
Multiplication, division, and remainder retain their interval transfers.

The tests check `from_parts` and `normalize` against concrete sets on u8
intervals with bounds near the ends of the range, small moduli and the sign
bit, crossed with constants, every class of modulus up to 20 and a few large
moduli: the result is exact, its bounds are the extreme members, each set
has one representation, and a normalized record is a fixpoint. They also check meet, refine, join, widen and `leq` against sets
on reduced records, the examples of `doc/reduced-product.md`, and boundary
cases at `u128`:

```text
cargo test -p semi-persistent-abstract-domains --test facts_congruence
```

## Wrapped widening and shared-facts refinement

The moving-bound widening proves containment and the termination condition:
the result is unchanged, Top, or has at least twice the previous cardinality.
Public size bounds and `lemma_size_monotone` support use of that measure by
callers. Endpoint advance/retreat lemmas and the constructor's exact size
contract connect native wrapping operations to the cardinality proof.
`Refine` proves preservation of the intersection with `Facts<W>` and no growth
outside the input. Split intersections fall back to the original arc when their
single-arc cover would grow outside it. `wrapped_refine` checks fact export,
refinement stability, and product reduction against concrete u8 membership.

## Sign over mathematical integers

`Sign` is the seven nonempty sign sets over `int`; `BotOr<Sign>` supplies the
eighth, empty state. Its representation is canonical, and `leq`, `join`, and
`meet` are exact with respect to `gamma`. `Arith<Euclid>` and `Arith<Trunc>`
prove universal containment for negation, addition, and subtraction; `Mul` is
also proved for both integer semantics. The Sign domain exports bounds through
`FactsZ` and its `Refine` implementation proves that it preserves every jointly
represented value and never grows the Sign component.

`DivRem<Euclid>` and `DivRem<Trunc>` have sound zero classification and
universally proved containment contracts. Truncated division and remainder use
the dividend-sign rule; Euclidean remainder is `Zero` for a zero dividend and
`PosOrZero` otherwise; Euclidean division handles both positive and negative
divisors. The Sign runtime suite checks all 7-by-7 abstract category
pairs against concrete values from `[-12, 12]`, including exact quotient and
remainder sign categories, lattice exactness, flags, and FactsZ refinement
no-growth.
