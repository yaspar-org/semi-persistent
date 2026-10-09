# Abstract Domains Proof Status

Last refreshed: 2026-10-08.

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

Enabled legacy macro-domain widths:

- `d8` (`u8`)
- `d16` (`u16`)
- `d32` (`u32`)
- `d64` (`u64`)

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. This is separate from generic `W: Word`
code: `Word`, the shared GCD/CRT helpers, and `Interval<W>` support u128.
The arithmetic helpers compute in `W`; they do not use widened intermediates.

The separate Rust mirror suite contains 32 tests:

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

Its 12 tests cover all five word widths, GCD properties, machine-modulus GCD
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

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
| L4 | Shared GCD/CRT helpers | shared mathematical proofs, deterministic GCD, modular inverse, exact finite CRT and machine-modulus GCD verified |
| L4 | `Congruence<W>` | generic unsigned semantics, canonical normalization, nonemptiness and canonicality proved; full `Domain` implementation deferred to the later lattice PR |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. #123 removed `ReducedProduct`, whose `reduce` and `add` carried
containment theorems; `reduce::Product` replaces it.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
and Unum conversions/arithmetic helpers.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.

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
No conversion into `BotOr<Congruence<W>>` or Congruence meet is implemented here.
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
including `is_extended_gcd` and `crt_solution_class_exact`, remain available.

Downstream coordination:

- #114 must consume the nonzero machine-modulus helper's `W` result directly,
  remove its conversion bridges, and prove the nonzero precondition. Zero is
  represented through the exponent helper when needed. Congruence migration,
  the CRT trigger improvement and uniform-wrap work remain in #114.
- #118 must rebase onto updated #114, remove its temporary `Word64` trait and
  bounds, and add `Congruence<u128>` regressions.
- #124's StridedInterval code uses the unchanged `gcd`, `crt_merge`, and
  `CrtMergeResult` APIs. Its inherited arithmetic implementation, helper tests,
  and documentation must be reconciled with this version when rebasing.

No Congruence domain migration, multiplication transfer, or reduced-product
integration is implemented here. No proof bypasses or new trusted items were
introduced.

### Congruence

`src/congruence.rs` implements the semantic core as `Congruence<W: Word>`
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
not a signed or wrapping arithmetic transfer semantics.

`new(m, r)` normalizes a raw class: for `m = 0` it denotes `{r}`, otherwise
it denotes `{x | x % m = r % m}`. This raw-input interpretation differs from
applying the old `has` to an unreduced, malformed pair (which could be empty).
The constructor proves preservation of the raw class through `raw_has` and
establishes `wf`. It uses `Word::urem` and `checked_add`; when the normalized
residue plus the modulus is not representable, it returns a singleton.
For example, `Congruence::<u8>::new(201, 200)` has the same canonical pair as
`constant(200)`. `constant` and `top` have semantic and representation contracts.
`normalize()` on a constructed value is proved to be identity.

`lemma_nonempty` witnesses the residue. `lemma_canonical` proves that equal
gamma sets of well-formed values imply structural equality: residues are the
least members, and nonconstant steps are determined by the second members.
Both use the common `Domain` proof obligations as inherent methods, without
proof bypasses or changes to the trust boundary.

PR #106 deliberately does **not** implement `Domain`: the current trait also
requires `leq`, `join`, `meet`, and `widen`. Those belong to #114; shared
GCD/extended-GCD/CRT helpers are supplied by #112 as described above. Neither
PR implements those Congruence operations or arithmetic transfers. Congruence has no internal bottom;
future empty results will use the existing external `BotOr` architecture.

`cargo test --test congruence` passes 4 tests against the real implementation.
The exhaustive oracle checks all 65,536 raw u8 pairs against all 256 words,
including normalization, nonemptiness, canonical invariants, and unique
representation of all 16,640 distinct sets. Other cases cover constant/top,
singleton collapse, second-member boundaries, all four word widths and legacy
aliases. The old six Congruence mirror tests were replaced by this target.

`cargo test` passes 47 integration tests: 8 CRT/helper, 4 Congruence,
3 reference-domain and 32 mirror tests (0 failures; 1 unrelated doctest ignored).
The verification count above uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.
