# Reduced products for e-class analysis

This note explains the reduction protocol, lists the planned work, and says
how to tell when a piece is done. It is not a status page: the state of the code is what
`cargo verus verify` and `tests/reduced_product.rs` check.

## Start here

This change adds to main the reduction protocol (`src/reduce.rs`), the fact
records `Facts<W>` and `FactsZ` (`src/facts.rs`, `src/facts_ops.rs`,
`src/facts_z.rs`), the Boolean value `Bool4` (`src/bool4.rs`), the
`Compare<S>` trait (`src/transfer.rs`), and a brute-force harness
(`tests/common/mod.rs`, `tests/reduced_product.rs`). Every planned transfer
already exists as a stub that verifies.

One rule holds everywhere: every operation stays sound at every step. A stub
that returns top is sound; a precise transfer replaces it only with a proof.
Precision is either proved or reported as a measured percentage.


## Why a product of canonical domains is not canonical

Each leaf domain is **canonical**: two values with the same concretization are
equal. `Interval` has exactly one representation of {3, …, 7}, namely
`[3, 7]`. That is what lets the e-graph detect a change with `==`, and treat
`Bot` as "empty".

A product means the intersection: γ(a, b) = γ(a) ∩ γ(b). Many different pairs
have the same intersection. Take `x : u8`, Interval × Congruence:

| Pair | γ |
|---|---|
| `[0, 10] × 4ℤ+3` | {3, 7} |
| `[3, 10] × 4ℤ+3` | {3, 7} |
| `[3, 7] × 4ℤ+3` | {3, 7} |
| `[1, 9] × 4ℤ+3` | {3, 7} |

Each component is canonical, but the pair is not. Each interval is a valid
representation of its own set; the redundancy appears only once the two are
intersected. Two consequences for the e-graph:

- **Change detection fails:** a class whose value goes from
  `[0,10] × 4ℤ+3` to `[3,7] × 4ℤ+3` looks changed under `==`, but nothing
  was learned.
- **Emptiness goes undetected:** `[10, 11] × 4ℤ+1` is empty (no value from 10
  to 11 is ≡ 1 mod 4), yet neither component is `Bot`.

The pair should be reduced to its tightest form, `[3, 7] × 4ℤ+3`, and the
empty pair should become `Bot`. That requires each domain to learn from the
other, and that exchange is what the reduction protocol does.

## Canonical facts

Writing a reduction for every pair of domains costs n(n−1)/2 functions and
proofs. Following Verasco (Jourdan et al., POPL 2015, §7), every domain of a
sort instead talks to one shared **fact record**. For bit-vectors, that record
is `Facts<W>`:

- `u`: unsigned bounds, today
- `c`: congruence, planned
- `bits`: known bits, `nonzero`, and the other planned fields

Each field is a canonical domain. The record's `normalize` reduces the fields
against each other: for example, it clips `u` to the grid of `c`. After
`normalize`, the record has exactly one representation per set it can
express, so **the record is canonical**. It returns `Bot` exactly when the
facts contradict each other.

That is why an e-class stores the record and not a product: change detection
and conflict detection only work on canonical values. A BitVec(W) class
carries a `Facts<W>`, an Int class a `FactsZ`, a Bool class a `Bool4`.

## The reduction protocol

A domain joins by implementing `Refine`, which has two operations:

- **`to_channel`:** write what it knows into a record, or return `Bot` when
  the domain value is empty. This must be sound: every value of the domain
  satisfies the record.
- **`refine(f)`:** tighten itself using a record. It keeps every value that
  `f` allows, and never grows.

One round of `Product::reduce`:

1. Each component calls `to_channel`.
2. The records are met (exact intersection) and normalized.
3. Each component calls `refine` with the result.

Rounds repeat until nothing changes or the fuel runs out. The proved theorem
is γ(reduce(p)) == γ(p): fuel changes how tight the representation is, never
what it means.

The example, with the record `{u, c}`:

1. **`to_channel`:**
   - The interval writes `{u: [0, 10], c: ⊤}`.
   - The congruence writes `{u: [3, 255], c: 4ℤ+3}`, where 3 and 255 are the
     smallest and largest members.
2. **Meet:** `{u: [3, 10], c: 4ℤ+3}`.

   **`normalize`:** it rounds 3 up to the grid (it stays 3) and 10 down to the
   grid (it becomes 7), giving `{u: [3, 7], c: 4ℤ+3}`.
3. **`refine`:** the interval becomes `[3, 7]`, and the congruence stays
   `4ℤ+3`.

All four pairs from the table reduce to `[3, 7] × 4ℤ+3`. For the empty pair
`[10, 11] × 4ℤ+1`, `normalize` rounds 10 up to 13 and 11 down to 9. Since
13 > 9, it returns `Bot`.

## The limit, and why fields matter

Reduction is only as precise as the record. With today's record `{u}` alone:

- The congruence can only write `u = [3, 255]`.
- The meet gives `[3, 10]`, and the round stops there.
- `[3, 10] × 4ℤ+3` and `[3, 7] × 4ℤ+3` remain two different fixpoints with
  the same γ.
- `[10, 11] × 4ℤ+1` is never reported as `Bot`.

So the rule: **a domain is exact in the product only once its facts are a
field of the record.** Until then, it can still sit in a `Product` and refine
through `to_channel` and `refine`, which is sound and helps precision. But the
e-graph's guarantees (change detection by `==`, conflicts as `Bot`) hold only
for what the record can express.

## Machine integers: reason over ℤ, compute in `W`

A sign domain over machine words looks forced to answer top: `Pos + Pos` can
overflow and wrap to a negative or zero value, so a sound transfer cannot
promise `Pos`. That is sound, but the domain then carries no information.

The domains in this crate split each machine operation into two steps.

1. **Ideal step.** Compute the operation on mathematical integers. There is no
   overflow case: `Pos + Pos = Pos`, `[a, b] + [c, d] = [a + c, b + d]`.
2. **Wrap step.** Interpret the ℤ result against the static range of the
   machine type, [0, 2^W − 1] unsigned or [−2^(W−1), 2^(W−1) − 1] signed. The
   machine result is the ℤ result modulo 2^W, mapped back into the range:
   - **Fits:** the ℤ result lies inside the range; nothing changes.
   - **Shifted:** it lies inside one copy `range + k·2^W`; subtracting `k·2^W`
     is exact.
   - **Crosses a boundary:** the result is top, or a wrapped interval (#120).

**ℤ is the specification, `W` is the implementation.** The two steps describe
what the result means; proofs state them with `int`, which costs nothing at
run time. The run-time code computes only in `W` and tells the cases apart
with `checked_add` and `checked_sub`. `Interval<W>::add`
(src/interval.rs) is the template: `checked_add` on the upper bounds decides
whether any sum overflowed, `checked_add` on the lower bounds decides whether
every sum overflowed, and `wrapping_add` computes the shifted bounds.

**The wrap step needs magnitudes.** Sign alone has none, so on its own it
cannot decide that `Pos + Pos` fits; its best machine-word answer is
`NonZero`. The interval in the same product supplies the magnitudes. At signed
8 bits with x, y ∈ [1, 50], the ideal sum is in [2, 100], which fits, so it
stays `Pos`. With x, y ∈ [1, 100], the ideal sum [2, 200] crosses 127 and
wraps to [−128, −56] ∪ [2, 127], whose sign is `NonZero`.

- **Int sort (`FactsZ`):** ℤ has no range, so the wrap step does not exist.
  Sign over ℤ is exact and becomes the `nz` field of `FactsZ`.
- **BitVec(W) sort (`Facts<W>`):** wrapping is the defined semantics, so every
  transfer takes both steps; sign information on bit-vectors is the planned
  signed-bounds field `s`.

## Integer representation

The domain's carrier decides which integers its run-time code may use.

| Carrier | Domains | Run-time integers |
|---|---|---|
| `W: Word` (BitVec sort) | `Interval<W>`, `Facts<W>`, `Congruence<W>`, `StridedInterval<W>`, `Wrapped<W>`, the planned `bits` and `s` fields | `W` only, through `Word` |
| `int` (Int sort) | `IntervalZ`, `FactsZ`, the planned ℤ-congruence and `IntervalQ` | `IBig`, because bounds exceed every machine type |
| no integers | `Bool4`, Sign over ℤ (a set of `{Neg, Zero, Pos}`) | none |

A machine-word domain does not convert to `u128` or `i128`, does not call a
`to_u64` bridge, and does not allocate. The modulus 2^W does not fit in `W`,
which is the usual reason to widen, but the run-time code never needs it:
`checked_*` detects overflow, `wrapping_*` computes modulo 2^W, and
`trailing_zeros` stands for a power of two by its exponent.

The one exception is a measured one. `Word::mulmod` multiplies in the next
wider type, because the same-width double-and-add loop is slower: at u64 it
takes 83.4 ns against 23.3 ns on full-range operands, and at u32 39.6 ns
against 0.9 ns (`cargo run --release --example mulmod_width`). At u64 it
first tries `checked_mul`, which takes 1.4 ns when both operands are below
2^32. A domain that wants another exception adds a benchmark like
examples/mulmod_width.rs and cites its numbers.

## Other design decisions

**`Domain` states soundness; `Canonical` states nonemptiness and canonicity.**
Every leaf domain and every fact record implements `Canonical`; `Product`
does not, for the reasons above.

**`meet` does not reduce; merges call `meet_reduce(o, fuel)`.** A `Domain`
impl that calls `reduce` depends on a function whose contract mentions that
impl, and Verus rejects the definition as a cycle. `Product::meet` is
therefore componentwise, and `meet_reduce` is the merge. The same cycle is
why `Interval::meet_exact` duplicates the body of `meet`.

**`Compare<S>` is fixed now.** Comparisons are planned over words and over ℤ, and the e-graph calls them through one interface.
`Semantics` gained `lt` and `le` (unsigned, two's complement, or integer
order), and `Compare<S>` has forward `lt`, `le`, `eq` into `Bool4` and
backward `assume_lt`, `assume_le`, `assume_eq(o, t)`. A backward result keeps
every operand pair whose comparison equals `t` and never grows an operand.

## How the domains plug into the e-graph

The integration design is
[egraph/doc/future/eclass-analysis.md](../../egraph/doc/future/eclass-analysis.md).
Nothing in it is implemented yet; this section says what it asks of your code.
[eclass-analysis-walkthrough.md](../../egraph/doc/future/eclass-analysis-walkthrough.md)
follows one program through the analysis and shows the `Facts<u8>` record
stored for each class after every command.

**Four events change a value.** *Make*: a node `f(c1, …, cn)` enters a class
and its forward transfer evaluates `f` on the children's values. *Merge*: two
classes become one, and the value is the meet followed by reduction.
*Child refinement*: a child's value shrinks, and every parent node's forward
transfer runs again. *Parent refinement*: a class's value shrinks, and each of
its nodes runs a backward transfer that refines its children. An empty meet
during a merge is a conflict: the asserted equalities have no model.

**Derived merges need equal singletons**
([§8](../../egraph/doc/future/eclass-analysis.md#8-merges-derived-from-abstract-values)).
The analysis merges two classes only when both values are the same singleton:
equal abstract values are not enough, because `x ∈ [0, 10]` and
`y ∈ [0, 10]` hold for `x = 1, y = 2`. An empty meet between two classes
proves a disequality, not a merge. The derived merges are constants, decided
Booleans, decided `ite`, inverse facts such as `sub(a, b) = {0} ⟹ a = b`, and
guarded rewrites.

**Storage.** `ClassData` gets one handle, `abs: Option<AbsRef>`, that points
into a semi-persistent pool per sort, the same pattern as `min_row` and
`min_pool`. `push` and `pop` roll the values back with the classes.

**Choosing domains per sort.** Three options: (A) domains belong to the
literal model; (B) user sorts declare `:interp` and `:domains`, which the
design proposes; (C) named profiles as sugar over B.

```lisp
(sort Int  :interp int          :domains (interval congruence nonzero))
(sort BV32 :interp (bitvec 32)  :domains (ubounds sbounds congruence bits))
(sort Expr)                                       ; uninterpreted: no analysis
```

`:domains` is a bit mask over the fields of one record type. A disabled field
stays at top, which is always sound.

**Three tiers of propagation.** Tier 1 maps a symbol to a library operator
with verified forward and backward transfers:
`(function bvadd (BV32 BV32) BV32 :interp bvadd)`. For a class with value `R`
containing `ite(c, t, e)`: if `R ⊓ val(e)` is empty, `c` is true and
`val(t) := val(t) ⊓ R`; symmetrically for `t`; both empty is a conflict.
Tier 2 needs no mechanism: `(rewrite (clamp x lo hi) (ite (lt x lo) lo …))`
puts `clamp` in a class with an `ite`, and tier 1 propagates through it.
Tier 3 is trusted, like a rewrite: `(function hash (BV32) BV32 :range (0
1023))` and `(rule (…) ((refine r (interval 0 99))))`, fired again only when
a semi-naive delta shows that a matched class changed.

**Termination.** Each class has a budget of strict changes per `run`
iteration. Every step keeps a sound value, so the budget costs precision,
never soundness, as fuel does inside `reduce`.

**What this means for your work.**

- Tier 1 is exactly the forward and backward transfers in the planned work. A
  transfer missing from the library is a symbol the e-graph cannot propagate
  through.
- The `ite` rule needs `Bool4` and disjointness detected by meet. An exact
  meet that finds `Bot` decides a branch; a loose join or widening costs
  nothing here, because merges never join. Prioritize exact meets and
  reductions over join and widen.
- The singleton test (`as_constant`, which each record will expose) must be
  exact: a false "singleton" merges two classes that some model separates.
  An exact meet that detects emptiness is what produces disequalities and
  conflicts.
- Canonical values make change detection by `==` work. A field whose `wf`
  admits two representations of one set schedules spurious work on every
  merge.

## Product details

**`Channel: Canonical`** is the trait of a fact record. `meet_exact` is the
field-wise intersection and returns a `pre_wf` record (each field well
formed); `normalize` makes it `wf` (fields mutually reduced) with
`γ(normalize(f)) == γ(f)`. Every record implements `Refine` for itself.
`Product` implements `Arith`, `Mul`, `DivRem` and `Compare` componentwise and
does not reduce: the caller reduces once at the root, with `reduce` or
`meet_reduce`. Reducing inside every transfer would run a reduction at every
nesting level, which the root's round already subsumes.

**More than two domains.** `Product<A, B>` implements `Refine` itself, so a
component can be a product, and nesting combines any number of domains. Three
macros in reduce.rs write the nesting for you:

```rust
use semi_persistent_abstract_domains::{product, product_pat, product_type};
// iv(lo, hi) is Interval::new(lo, hi).expect("lo <= hi"), as in the tests.
type P = product_type![Interval<u8>, Facts<u8>, Interval<u8>]; // Product<I, Product<F, I>>
let p: P = product!(iv(10, 200), Facts::from_interval(iv(0, 100)), iv(50, 255));
if let BotOr::Val(product_pat!(a, b, c)) = p.reduce(REDUCE_FUEL) {
    // a, b and c all describe [50, 100]
}
```

A product's `to_channel` is the normalized meet of its components' records,
and `Bot` when they contradict each other; its `refine(f)` refines each
component by `f`. One round of the outer `reduce` therefore computes the meet
of the records of all leaves and refines every leaf by it: each domain
receives what every other domain knows, at any nesting depth, and an inner
product whose components contradict each other makes the round return
`Bot`. A round costs one `to_channel` and one `refine` per leaf. The `reduce`
theorem is proved for every `A` and `B` that implement `Refine`, so it covers
nested products with no extra proof, and adding a domain costs one `Refine`
impl against the channel, not one reduction per pair.
`n_ary_products_reduce_in_one_round` in tests/reduced_product.rs checks
products of 2, 3, 4 and 5 intervals and fact records on 2000 random u8
inputs: after one round every leaf equals the intersection of all inputs, and
the result is `Bot` exactly when that intersection is empty. Nesting calls
`normalize` once per level per round where a flat product would call it once;
it changes no result.

**A product is for computing, the record is what a class stores.** An e-class
stores its sort's fact record, never a `Product`, because the record is
`Canonical` and a product is not. A domain
that is not yet a field of the record computes inside a product, and the
e-graph keeps only the record that the product's `to_channel` returns.

**#123 removed the earlier `ReducedProduct`.** The crate's first commit
generated one `ReducedProduct { tnum, anum, interval, unum }` per width from
u8 to u64, with a reduction written by hand for exactly those four
components; exec_tnum.rs held a u64 copy and a `TnumInterval`. Neither
implemented the `Domain` traits or had a u128 instance, and nothing outside
the crate used them. Tnum, Anum and Unum stay, but join `Product` only after
they are ported to the shared interface: a `Word` type parameter, `BotOr` as
the only bottom (no empty representation of their own), `Canonical`, and
`Refine` against `Facts<W>`. `ExecTnum<W>` is ported (#108): its `meet`
returns `BotOr`, `to_channel` writes `[val, val | mask]` to `u`, and `refine`
meets with the Tnum of `u`'s range, so `Product<Interval<W>, ExecTnum<W>>`
reduces. Anum and Unum are not ported yet.

## How to extend

**Add a field to `Facts` (`src/facts.rs`).**

1. Add the field, its closed spec accessor, and its `wf` to `pre_wf` and its
   `gamma` to `gamma`.
2. Extend `dup`, `top`, `leq`, `join`, `widen`, `meet` and `meet_exact`
   field-wise. Every constructor sets the field to top, so every existing
   `to_channel` stays sound and every `refine` keeps its contract.
3. Add the propagation step to `normalize` and its condition to `reduced`,
   and prove `lemma_canonical`. Keep the split: `pre_wf` for field-wise
   validity, `wf` for agreement between fields.
4. Extend the transfers in `facts_ops.rs` with the field's own result.
5. Test: `normalize` over every u8 value of the field, and meet and refine on
   samples against brute force.

**Make a standalone domain a `Refine` component.** Implement `Domain`,
then `Refine` with `F = Facts<W>`: `to_channel` builds a record from the facts
the domain implies (top elsewhere), normalizes it, and wraps it in
`BotOr::Val`; `refine` meets the
domain with the fields it can read. `impl Refine for Interval<W>` in
`facts.rs` is the template. `Product<YourDomain, Facts<W>>` then reduces.

**Replace a stub transfer.** Change the body, keep the trait contract, and
prove it. Then measure: call `check_binop_u8`, `check_cmp_u8` or
`check_assume_u8` from `tests/common/mod.rs` with your samples and a best
abstraction `alpha`, print `pct_non_optimal()`, and quote the number with the
test name in your PR.

## Observations that shape the work

- **Strided is reduced Interval × Congruence** (Granger 1989), so Strided
  becomes the grid step of `normalize`, not a field.
- **Sign over ℤ is an interval plus a nonzero bit.** Every sign value except
  `!= 0` is an interval; `!= 0` is the top interval with the bit set.
- **Wrapped is almost covered by unsigned plus signed bounds.** Their
  intersection expresses every arc except one that crosses both 0 and
  2^(W−1).

## Planned work

**Acceptance**, for every piece of work:

1. `cargo verus verify -- --trace` in `abstract-domains` reports 0 errors,
   and `--time-expanded` shows no function above 10 s.
2. `grep -nE 'admit\(|assume\(|external_body'` finds nothing in the changed
   files.
3. Every new exec function states soundness against `gamma` in its `ensures`.
4. `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets --
   -D warnings`, and `cargo test -p semi-persistent-abstract-domains`, with
   and without `--all-features`, pass.
5. A u128 instance exists and a test exercises it.
6. No document records a number of verified items. The count changes with
   every merge, so docs state "0 errors" and CI checks it.
7. Every precision claim is proved or reported as a measured percentage from
   `tests/common/mod.rs`, naming the test that prints it.
8. The run-time code of a machine-word domain computes in `W` with `Word`
   operations: no `IBig` and no wider integer type, unless a benchmark in the
   repository shows the wider type is faster (see "Integer representation").

**BitVec lattice and reduction.** Files: `src/facts.rs`,
`src/congruence.rs` (new), `src/sbounds.rs` (new). Builds on #106, #112,
#114, #118 (Congruence) and #109 (Strided).

- *First:* port Congruence to the #117 `Word` primitives (`checked_mul`,
  `mulmod`, `trailing_zeros`; no u128 or i128 helpers). Add it to `Facts` as
  field `c`, with the interval and congruence grid step in `normalize`;
  reuse the `clip` code of #109.
- *Later:* the signed-bounds field `s` and the unsigned and signed step;
  known bits against bounds; congruence against low bits.

**BitVec transfers.** Files: `src/facts_ops.rs`, `src/tnum_w.rs` (new).
Builds on #108 (interval transfers) and #120 (Wrapped).

- *First:* `Compare<Unsigned<W>>` and `Compare<Signed<W>>` for `Facts<W>` on
  the `u` field, forward and backward, replacing the stubs; and bvand, bvor,
  bvxor, bvnot and the shifts from #108.
- *Later:* extract, concat, zero_extend, sign_extend; the known-bits field
  `bits` as a generic Tnum over `Word`; Wrapped (#120) as a `Refine`
  component.

**Int and Bool.** Files: `src/facts_z.rs`, `src/bool4.rs`,
`src/congruence_z.rs` (new). Builds on #111 (IntervalZ) and #121 (Sign).

- *First:* `Compare<Euclid>` and `Compare<Trunc>` for `FactsZ`, forward and
  backward, replacing the stubs; the nonzero field `nz`, which is where Sign
  over ℤ from #121 lands; `Bool4::ite` with its backward rule.
- *Later:* the ℤ-congruence field; precise `+ − * div mod abs` under
  `Euclid` and `Trunc`; a rational interval domain `IntervalQ`, which the
  Herbie benchmark's stripped interval analysis needs
  ([herbie.deviations.md](../../doc/benchmarks/ledgers/herbie.deviations.md)
  §1).

**Dependencies.** The congruence field `c` comes first, because the BitVec
transfers and the later reduction steps read it; until then transfers are
written against `u`. The BitVec and Int comparisons share `Compare<S>` and
`Semantics::lt`/`le`, so a change to those signatures needs a review covering
both.

**Starting numbers.** `cargo verus verify` reports 0 errors; the slowest
new function takes 9 ms. On 98 reduced `Product<Interval<u8>,
Interval<u8>>` values (9,604 pairs, `product_transfers_sound_and_measured`),
add, sub and udiv are optimal on every pair, urem is non-optimal on 10.1% and
mul on 52.2%. The `Compare` stubs on the 36 grid `Facts<u8>` values
(`facts_compare_stubs_sound_and_measured`) are non-optimal on 41.7% of
forward bvult pairs, 25.6% of bvslt pairs and 33.0% of `=` pairs, and on
53% to 66% of backward cases. Answering top is optimal whenever both truth
values occur, so these numbers measure the samples as much as the stubs.

**Out of scope.** The e-graph integration (storage, the merge hook,
propagation and its budget, surface syntax, derived merges) is designed in
[egraph/doc/future/eclass-analysis.md](../../egraph/doc/future/eclass-analysis.md).

## References

- J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy, D. Pichardie. *A
  Formally-Verified C Static Analyzer.* POPL 2015, §7.
- P. Granger. *Static analysis of arithmetical congruences.* 1989.
- doc/domain-traits.md for `Domain`, `Canonical`, `Word` and `Semantics`.
