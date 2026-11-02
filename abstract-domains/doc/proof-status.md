# Abstract Domains Proof Status

Last refreshed: 2026-10-01.

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

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. Do not describe `u128` as an enabled or
verified executable instance.

The separate Rust mirror suite can be run with:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

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
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
| L4 | `StridedInterval<W>` (`strided.rs`), ported onto the shared `Domain`/`Word` traits from `doc/domain-traits.md` | `wf` is canonical (`lemma_canonical` proved); `leq`/`join`/`meet`/`widen` implemented; not yet in a `Product` |
| L4 | `Congruence<W>` | generic unsigned semantics, canonical normalization, nonemptiness and canonicality proved; full `Domain` implementation not yet available |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `StridedInterval<W>` | `new`, `constant`, `leq` (sound and complete), `join`, `meet`, `widen`; precision caveats below |

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

`StridedInterval<W>` (`src/strided.rs`) is ported onto the shared
`Domain`/`Word`/`lattice::BotOr` interface fixed by `doc/domain-traits.md`
(added in #116), whose reference ports are `Interval<W>` and `IntervalZ`
(`interval.rs`, `interval_z.rs`). Until every domain is migrated, the crate
has two coexisting shapes for machine-word domains: the legacy per-width macro
stamping in `domains.rs` (`ExecTnum`, `ExecAnum`, `ExecUnum`, the old
`Interval`) and the new generic-over-`W` shape. The two
are independent; nothing here claims anything about the legacy macro
types' status beyond what the Layer table already says.

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

### Congruence

`src/congruence.rs` implements the semantic core as `Congruence<W: Word>`
(with the bound on its implementation). Fields are private. This implementation adds
`domains::d8/d16/d32/d64::Congruence` as aliases of the generic type.
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
can preserve the integer-congruence precision.

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
Both use the common `Domain` proof obligations as inherent methods, without
proof bypasses or changes to the trust boundary.

Congruence has no internal bottom; empty results use the existing external
`BotOr` architecture.

`cargo test --test congruence` passes against the real implementation.
The exhaustive oracle checks all 65,536 raw u8 pairs against all 256 words,
including normalization, nonemptiness, canonical invariants, and unique
representation of all 16,640 distinct sets. Other cases cover constant/top,
singleton collapse, second-member boundaries, all four word widths and width
aliases. The oracle also checks the canonical query helpers against the sets.

`cargo test` passes the integration tests (0 failures; an unrelated doctest ignored).
Verification uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.

The finite-height/rank theorem remains future lattice work; this semantic core
does not yet prove the termination bound for join-based widening.
