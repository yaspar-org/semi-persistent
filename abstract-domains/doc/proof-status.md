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
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval` at four enabled widths | every method verifies its stated contract; containment scope is listed below |
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
not a signed or wrapping arithmetic transfer semantics. Equivalently, `gamma`
is the integer congruence restricted to the finite unsigned word range.
Wrapping arithmetic can lose exactness: at u8, adding 1 to `(3, 0)` produces
`{0, 1, 4, ..., 253}`, since 255 wraps to 0. Any congruence containing both
0 and 1 is Top, so the best congruence abstraction is Top. A no-wrap condition
can preserve the integer-congruence precision; arithmetic is outside this PR.

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

Public `residue_member` witnesses the residue; `member_decomposition` gives
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

PR #106 deliberately does **not** implement `Domain`: the current trait also
requires `leq`, `join`, `meet`, and `widen`. Those belong to #114; shared
GCD/extended-GCD/CRT helpers belong to #112. This PR adds neither those
operations nor arithmetic transfers. Congruence has no internal bottom;
future empty results will use the existing external `BotOr` architecture.

`cargo test --test congruence` passes 4 tests against the real implementation.
The exhaustive oracle checks all 65,536 raw u8 pairs against all 256 words,
including normalization, nonemptiness, canonical invariants, and unique
representation of all 16,640 distinct sets. Other cases cover constant/top,
singleton collapse, second-member boundaries, all four word widths and width
aliases. The oracle also checks the canonical query helpers against the sets.

`cargo test` passes 39 integration tests: 4 Congruence, 3 reference-domain,
and 32 mirror tests (0 failures; 1 unrelated doctest ignored).
Verification uses the repository-pinned Verus
`0.2026.09.20.aef82ed`, matching the pinned `vstd` dependency.

The finite-height/rank theorem remains future lattice work; this semantic core
does not yet prove the termination bound for join-based widening.
