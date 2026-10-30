# Domain registry: the engine-facing API of abstract-domains

[Domain traits](../domain-traits.md) |
[Reduced products](../reduced-product.md) |
[Proof status](../proof-status.md) |
[E-class analysis](../../../egraph/doc/future/eclass-analysis.md)

**Status**: task specification for PR #4 of 4; nothing in it is implemented.
The acceptance tests are `tests/registry.rs`, ignored until the PR lands.
Every code site the PR changes carries a `TODO(abs-domain-registry)` comment,
listed in §8.

## 1. What the PR delivers

The e-graph names carriers, domains and operators by string. The crate offers
Rust types and traits. The registry is the one module that maps the first to
the second, in `src/registry.rs`. It adds no abstract domain and no transfer
proof of its own.

| Deliverable | Content |
|---|---|
| carrier table | `int`, `bool`, `(bitvec N)` for N in {8, 16, 32, 64, 128}; any other N is top-only |
| domain table | 8 (carrier, name) pairs, each a bit of the sort's domain mask |
| value entry | a fixed-size `Copy` encoding per carrier, with `encode`, `decode`, `top` |
| lattice API | `meet`, `reduce`, conflict as `BotOr::Bot`, `as_constant` |
| operator table | 48 `:interp` operators with carrier signature, forward and backward transfer |
| `ite` | forward and backward transfer, composed from `Bool4`, `join` and `meet` |
| zero divisors | the SMT-LIB result for a zero divisor, joined onto the `DivRem` result |
| masked records | `normalize` and `reduced` on `Facts<W>` and `FactsZ` take the domain mask |

A name whose field or transfer is missing still resolves. Its domain bit is
reported unavailable, and its transfer returns top forward and the operands
backward. Both answers are sound, so sibling #1 validates every name today.
The missing fields and transfers are the planned work of
[reduced-product.md](../reduced-product.md), not this PR.

## 2. Carriers and domains

`Word` (src/word.rs) has 5 instances: u8, u16, u32, u64 and u128. `Facts<W>`
and `Interval<W>` are generic over `Word`, so all 5 widths are native
carriers. The disabled `d128` macro instance in src/domains.rs concerns the
old per-width domains only.

| `:interp` | Carrier | Record | `Semantics` |
|---|---|---|---|
| `bool` | Bool | `Bool4` | none |
| `int` | Int | `FactsZ` | `Euclid` (SMT-LIB `div`, `mod`) |
| `(bitvec 8)` ... `(bitvec 128)` | BitVec(W), W in u8..u128 | `Facts<W>` | `Unsigned<W>`, `Signed<W>` by operator |
| `(bitvec N)`, N not in {8, 16, 32, 64, 128} | top-only | none | none |

A top-only carrier has entry size 0. Every registry function returns top on
it, and `as_constant` returns `None`. A `Bits<N>` word type for all widths up
to 128 is the later step of eclass-analysis §5.

A domain set is a bit mask over the fields of the carrier's record
(eclass-analysis §5, "Implementation of a domain set"). The record keeps every
field. A disabled field stays at top and its reduction steps are skipped.

| Carrier | Name | Bit | Field | Backing type | Status |
|---|---|---|---|---|---|
| Int | `interval` | 0 | `FactsZ.itv` | `IntervalZ` (src/interval_z.rs) | exists |
| Int | `congruence` | 1 | `FactsZ.c` | `CongruenceZ`, planned src/congruence_z.rs | missing |
| Int | `nonzero` | 2 | `FactsZ.nz` | `bool`; Sign over ℤ from #121 lands here | missing |
| BitVec | `ubounds` | 0 | `Facts<W>.u` | `Interval<W>` (src/interval.rs) | exists |
| BitVec | `sbounds` | 1 | `Facts<W>.s` | planned src/sbounds.rs | missing |
| BitVec | `congruence` | 2 | `Facts<W>.c` | `Congruence<W>` (#118), port to `Word` planned in src/congruence.rs | missing |
| BitVec | `bits` | 3 | `Facts<W>.bits` | Tnum over `Word`, planned src/tnum_w.rs | missing |
| Bool | `bool` | 0 | the whole value | `Bool4` (src/bool4.rs) | exists |

3 of 8 domains exist. `bits` has a verified per-width ancestor: `ExecTnum` in
src/domains.rs, at u8..u64, with containment proofs for `bw_or`, `bw_and`,
`bw_xor`, `add`, `join` and `meet` (proof-status.md). It is not a `Domain`
and not generic over `Word`. PR #108 ports `ExecTnum`, `ExecAnum` and
`ExecUnum` to `impl<W: Word>`; the registry targets that form.

The default set of each carrier enables every available field. `:domains ()`
disables the analysis of a sort.

## 3. Value entry format

The class-layer pool (sibling #2) stores one entry per class as opaque bytes.
An entry is `Copy`, has a size fixed by the carrier, and never denotes the
empty set. Bytes are equal exactly when concretizations are equal, because
every record is `Canonical` and `encode` is injective.

| Carrier | Fields encoded | Bytes today (`u` / `itv` only) | Bytes with every field |
|---|---|---|---|
| Bool | `Bool4` | 1 | 1 |
| BitVec(u8) | `u`, `s`, `c`, `bits`, 2 words each | 2 | 8 |
| BitVec(u16) | same | 4 | 16 |
| BitVec(u32) | same | 8 | 32 |
| BitVec(u64) | same | 16 | 64 |
| BitVec(u128) | same | 32 | 128 |
| Int | `itv` as 2 × i64, `c` as 2 × i64, `nz` as 1 byte | 16 | 40 (33, padded to 8) |
| top-only | none | 0 | 0 |

**Int bounds.** `IntervalZ` holds `IBig` bounds, which are not `Copy`. The
entry stores each bound as an `i64`. `i64::MIN` as a lower bound means −∞ and
`i64::MAX` as an upper bound means +∞. A bound outside the range rounds
outward to the infinite bound on its side, which is sound. The conversion
uses the trusted `IBig::to_i64` and `IBig::from_i64` that exist today, so it
adds nothing to the trust ledger (domain-traits.md §7). Eclass-analysis §4
proposes `i128`, which needs 2 new trusted `IBig` functions (§9).

**Congruence words.** The table counts 2 words for `c`. Over `W` the modulus
2^N does not fit in `W`, so the encoding stores it by its exponent or another
form the congruence port fixes (§9).

## 4. Operators

Columns: carrier signature; forward and backward transfer, with the trait
that provides it. Status: **exists** (verified, nontrivial), **stub**
(verified, answers top or keeps the operands), **missing** (no code). S is
any carrier other than top-only. BV is BitVec(W).

| Name | Signature | Forward | Fwd status | Backward | Bwd status |
|---|---|---|---|---|---|
| `+` | (Int, Int) → Int | `Arith<Euclid>::add` on `FactsZ` | exists | none | missing |
| `-` (binary) | (Int, Int) → Int | `Arith<Euclid>::sub` | exists | none | missing |
| `-` (unary) | (Int) → Int | `Arith<Euclid>::neg` | exists | none | missing |
| `*` | (Int, Int) → Int | no `Mul<Euclid>` on `IntervalZ` or `FactsZ` | missing | none | missing |
| `div` | (Int, Int) → Int | `DivRem<Euclid>::div`, top plus zero flag | stub | none | missing |
| `mod` | (Int, Int) → Int | `DivRem<Euclid>::rem`, top plus zero flag | stub | none | missing |
| `abs` | (Int) → Int | none | missing | none | missing |
| `<` | (Int, Int) → Bool | `Compare<Euclid>::lt` | stub | `assume_lt` | stub |
| `<=` | (Int, Int) → Bool | `Compare<Euclid>::le` | stub | `assume_le` | stub |
| `>` | (Int, Int) → Bool | `lt` with operands swapped | stub | `assume_lt` swapped | stub |
| `>=` | (Int, Int) → Bool | `le` with operands swapped | stub | `assume_le` swapped | stub |
| `not` | (Bool) → Bool | `Bool4::not`, exact | exists | none | missing |
| `and` | (Bool, Bool) → Bool | `Bool4::and`, exact | exists | none | missing |
| `or` | (Bool, Bool) → Bool | `Bool4::or`, exact | exists | none | missing |
| `xor` | (Bool, Bool) → Bool | none; `not(eq)` composes | missing | none | missing |
| `=>` | (Bool, Bool) → Bool | none; `or(not a, b)` composes | missing | none | missing |
| `=` on Bool | (Bool, Bool) → Bool | `Bool4::eq`, exact | exists | none | missing |
| `=` on Int, BV | (S, S) → Bool | `Compare::eq` | stub | `assume_eq` | stub |
| `distinct` | (S, S) → Bool | `not` of `Compare::eq` | stub | `assume_eq` with `t` negated | stub |
| `ite` | (Bool, S, S) → S | none; `Bool4` and `Domain::join` compose | missing | none; the eclass-analysis §6 table, from `meet` | missing |
| `bvadd` | (BV, BV) → BV | `Arith<Unsigned<W>>::add` on `Facts<W>` | exists | none | missing |
| `bvsub` | (BV, BV) → BV | `Arith<Unsigned<W>>::sub` | exists | none | missing |
| `bvneg` | (BV) → BV | `Arith<Unsigned<W>>::neg` | exists | none | missing |
| `bvmul` | (BV, BV) → BV | `Mul<Unsigned<W>>::mul` | exists | none | missing |
| `bvudiv` | (BV, BV) → BV | `DivRem<Unsigned<W>>::div`, plus all ones for a zero divisor | exists | none | missing |
| `bvurem` | (BV, BV) → BV | `DivRem<Unsigned<W>>::rem`, plus `x` for a zero divisor | exists | none | missing |
| `bvsdiv` | (BV, BV) → BV | `DivRem<Signed<W>>::div`, top plus zero flag | stub | none | missing |
| `bvsrem` | (BV, BV) → BV | `DivRem<Signed<W>>::rem`, top plus zero flag | stub | none | missing |
| `bvsmod` | (BV, BV) → BV | none; `Semantics` has no floor remainder | missing | none | missing |
| `bvand` | (BV, BV) → BV | no `Bitwise` trait; `ExecTnum::bw_and` per width | missing | none | missing |
| `bvor` | (BV, BV) → BV | no `Bitwise`; `ExecTnum::bw_or` per width | missing | none | missing |
| `bvxor` | (BV, BV) → BV | no `Bitwise`; `ExecTnum::bw_xor` per width | missing | none | missing |
| `bvnot` | (BV) → BV | no `Bitwise`; `ExecTnum::bw_not` proves `wf` only | missing | none | missing |
| `bvshl` | (BV, BV) → BV | no `Shift<S>` trait | missing | none | missing |
| `bvlshr` | (BV, BV) → BV | no `Shift<S>` | missing | none | missing |
| `bvashr` | (BV, BV) → BV | no `Shift<S>` | missing | none | missing |
| `bvult` | (BV, BV) → Bool | `Compare<Unsigned<W>>::lt` | stub | `assume_lt` | stub |
| `bvule` | (BV, BV) → Bool | `Compare<Unsigned<W>>::le` | stub | `assume_le` | stub |
| `bvugt` | (BV, BV) → Bool | `lt` swapped | stub | `assume_lt` swapped | stub |
| `bvuge` | (BV, BV) → Bool | `le` swapped | stub | `assume_le` swapped | stub |
| `bvslt` | (BV, BV) → Bool | `Compare<Signed<W>>::lt` | stub | `assume_lt` | stub |
| `bvsle` | (BV, BV) → Bool | `Compare<Signed<W>>::le` | stub | `assume_le` | stub |
| `bvsgt` | (BV, BV) → Bool | `lt` swapped | stub | `assume_lt` swapped | stub |
| `bvsge` | (BV, BV) → Bool | `le` swapped | stub | `assume_le` swapped | stub |
| `extract` | (BV M) → BV N | no `Cast` trait | missing | none | missing |
| `concat` | (BV M, BV N) → BV M+N | no `Cast` | missing | none | missing |
| `zero_extend` | (BV M) → BV M+K | no `Cast` | missing | none | missing |
| `sign_extend` | (BV M) → BV M+K | no `Cast` | missing | none | missing |

| Direction | Exists | Stub | Missing | Total |
|---|---|---|---|---|
| forward | 13 | 18 | 17 | 48 |
| backward | 0 | 14 | 34 | 48 |

`bvadd`, `bvsub`, `bvneg` and `bvmul` read `Unsigned<W>`. They commute with
reduction mod 2^N, so the result also holds under `Signed<W>`
(domain-traits.md §4). `and`, `or`, `+` and `distinct` are n-ary in SMT-LIB;
the table lists the binary form (§9).

**Zero divisors.** The `DivRem` contract excludes zero divisors and reports
them in the `DivZero` flag. SMT-LIB defines `bvudiv x 0` as all ones,
`bvurem x 0` as `x`, `bvsdiv x 0` as −1 for x ≥ 0 and 1 otherwise, and
`bvsrem x 0` as `x`. When the flag is `Maybe` or `Always`, the registry joins
that value onto the quotient. The BitVec operators are then total, so their
forward transfer never returns `Bot`.

## 5. API

Every signature in this section is a **proposal**. The student fixes the final
form and records the changes here.

```rust
// Carriers (§2).
pub enum Width { W8, W16, W32, W64, W128 }
pub enum Carrier { Bool, Int, BitVec(Width), TopOnly { bits: u32 } }
pub fn carrier_of_bitvec(bits: u32) -> Carrier;          // TopOnly unless native

// Domain names and masks (§2).
pub struct DomainSet(u8);                                // bit i: field i of the record
pub enum NameError { Unknown, WrongCarrier(Carrier) }
pub fn domain_bit(c: Carrier, name: &str) -> Result<u8, NameError>;
pub fn domain_available(c: Carrier, bit: u8) -> bool;    // false for a missing field
pub fn default_domains(c: Carrier) -> DomainSet;

// Values and entries (§3).
pub enum Value { Bool(Bool4), Int(FactsZ), Bv8(Facts<u8>), Bv16(Facts<u16>),
                 Bv32(Facts<u32>), Bv64(Facts<u64>), Bv128(Facts<u128>), Top }
pub fn entry_size(c: Carrier) -> usize;
pub fn encode(c: Carrier, v: &Value, out: &mut [u8]);   // out.len() == entry_size(c)
pub fn decode(c: Carrier, bytes: &[u8]) -> Value;
pub fn top(c: Carrier) -> Value;

// Lattice (§6).
pub fn meet(c: Carrier, m: DomainSet, a: &Value, b: &Value) -> BotOr<Value>;
pub fn reduce(c: Carrier, m: DomainSet, a: &Value) -> BotOr<Value>;
pub enum Const { Bool(bool), Int(IBig), Bv(u128) }
pub fn as_constant(c: Carrier, a: &Value) -> Option<Const>;

// Operators (§4).
pub enum Op { Add, Sub, Neg, Mul, Div, Mod, Lt, Le, Gt, Ge, Eq, Distinct, Ite,
              Not, And, Or, Xor, Implies, BvAdd, BvSub, /* one per row of §4 */ }
pub enum OpError { Unknown, Signature }
pub fn op(name: &str, args: &[Carrier]) -> Result<(Op, Carrier), OpError>;
pub fn forward(op: Op, m: DomainSet, args: &[Value]) -> Value;
pub fn backward(op: Op, m: DomainSet, result: &Value, args: &[Value])
    -> BotOr<[Value; 3]>;                                // arity at most 3 (ite)
```

Conflict detection has no function of its own. A stored entry is never empty,
because every record is bottomless (`Canonical::lemma_nonempty`). A conflict
is the `Bot` result of `meet`, `reduce` or `backward`.

## 6. Contracts

Every function in `src/registry.rs` except the string tables lives inside
`verus!` and states its contract against the records' `gamma`. Write
`γ(v)` for the concretization of a `Value` over the carrier's concrete values
(`bool`, `int`, `W`), and `⟦op⟧` for the SMT-LIB meaning of an operator. The
mask enters through a predicate `wf_masked(m)`: the record is `pre_wf`, every
disabled field is top, and the enabled fields are mutually reduced.

| Function | Contract | Built on |
|---|---|---|
| `top(c)` | `wf_masked(m)`; every concrete value is in `γ` | `Domain::top` |
| `encode`, `decode` | `decode(encode(v)) == v` for BitVec and Bool; `γ(v) ⊆ γ(decode(encode(v)))` for Int, with equality when every finite bound lies in (−2^63, 2^63 − 1) | the field accessors |
| `meet(a, b)` | `Bot` ⟹ `γ(a) ∩ γ(b) = ∅`; `Val(r)` ⟹ `wf_masked(m)` and `γ(a) ∩ γ(b) ⊆ γ(r)`; with every field enabled, `γ(r) = γ(a) ∩ γ(b)` | `Channel::meet_exact`, `normalize` |
| `reduce(a)` | `Bot` ⟺ `γ(a) = ∅`; `Val(r)` ⟹ `γ(r) = γ(a)` and `wf_masked(m)` | `Channel::normalize` |
| canonicity | `wf_masked(m)` on `a` and `b` and `γ(a) = γ(b)` ⟹ `a == b`, so byte equality is set equality | `Canonical::lemma_canonical` |
| `as_constant(a)` | `Some(k)` ⟹ `γ(a) = {k}`; `None` ⟹ `γ(a)` has 2 or more elements | the new record `as_constant` |
| `forward(op, x̄)` | for all `xᵢ ∈ γ(aᵢ)`: `⟦op⟧(x̄) ∈ γ(r)` | `Arith`, `Mul`, `DivRem`, `Compare`, `Bool4` |
| `backward(op, R, ā)` | `γ(a′ᵢ) ⊆ γ(aᵢ)`; every `x̄` with `xᵢ ∈ γ(aᵢ)` and `⟦op⟧(x̄) ∈ γ(R)` has `xᵢ ∈ γ(a′ᵢ)`; `Bot` ⟹ no such `x̄` | `Compare::assume_*`, `meet` |

`as_constant` must be exact in the `Some` direction. A false singleton merges
two classes that some model separates (eclass-analysis §8). A missed
singleton costs a derived merge, never soundness.

**No new trust.** `src/registry.rs` contains no `external_body`, `assume`,
`admit` or `axiom`, and the ledger in domain-traits.md §7 is unchanged. The
name tables (`domain_bit`, `op`) are plain Rust outside `verus!`, because
Verus has limited `&str` support. A wrong name mapping binds a symbol to the
wrong `⟦op⟧`, which the verified contracts cannot see. The runtime tests check
each name against a concrete reference implementation of the operator.

## 7. How the siblings consume it

| Sibling | Calls | Purpose |
|---|---|---|
| #1 abs-surface-syntax | `carrier_of_bitvec`, `domain_bit`, `domain_available`, `default_domains`, `op` | resolve `:interp` on sorts and functions, validate `:domains`, check operator signatures, warn on an unavailable domain or a top-only width |
| #2 abs-class-storage | `entry_size`, `encode`, `decode`, `top` | size one pool per sort, write `top` for a new class, compare entries by bytes for change detection; `containers` sees bytes only |
| #3 abs-saturation-engine | `meet`, `reduce`, `forward`, `backward`, `as_constant` | the 4 events of reduced-product.md: make and child refinement run `forward`, merge runs `meet` then `reduce`, parent refinement runs `backward`; `Bot` is a conflict; `as_constant` drives derived merges |

The mask is per sort, not per entry. #1 stores it in the sort descriptor, and
#3 passes it to every lattice and transfer call.

## 8. Change sites

Each row is a `TODO(abs-domain-registry)` comment in the code. Line numbers
are those on this branch.

| File:line | Change | § |
|---|---|---|
| src/lib.rs:41 | add `pub mod registry;` and name it in the module doc | §5 |
| src/facts.rs:32 | add fields `s`, `c`, `bits` to `Facts<W>` | §2 |
| src/facts.rs:33 | fixed-width `Copy` encoding of `Facts<W>` with a round-trip proof | §3 |
| src/facts.rs:44 | `reduced` and `normalize` take the domain mask | §6 |
| src/facts.rs:63 | add `as_constant` to `Facts<W>` | §5 |
| src/facts_z.rs:22 | add fields `c`, `nz` to `FactsZ` | §2 |
| src/facts_z.rs:23 | i64 bound encoding with outward rounding, no new trust | §3 |
| src/facts_z.rs:51 | add `as_constant` to `FactsZ` | §5 |
| src/facts_z.rs:150 | `normalize` and `reduced` take the domain mask | §6 |
| src/facts_z.rs:263 | add `Mul<Euclid>` for `FactsZ` (Int `*`) | §4 |
| src/facts_z.rs:278 | Int `div`, `mod`: placeholder, zero-divisor value | §4 |
| src/facts_z.rs:313 | replace the `Compare<Euclid>` stub | §4 |
| src/facts_ops.rs:83 | `Bitwise` and `Shift` impls and backward transfers for `Facts<W>` | §4 |
| src/facts_ops.rs:104 | SMT-LIB zero-divisor values for `bvudiv`, `bvurem` | §4 |
| src/facts_ops.rs:122 | `bvsdiv`, `bvsrem` placeholder; `bvsmod` missing | §4 |
| src/facts_ops.rs:140 | replace the `Compare<Unsigned<W>>` stub | §4 |
| src/facts_ops.rs:169 | replace the `Compare<Signed<W>>` stub | §4 |
| src/transfer.rs:63 | backward traits for `Arith`, `Mul`, `DivRem` | §4 |
| src/transfer.rs:111 | `Bitwise`, `Shift<S>`, `Cast` traits | §4 |
| src/bool4.rs:119 | `ite` and backward connectives on `Bool4` | §4 |
| src/interval.rs:578 | `Compare<Unsigned<W>>`, `Compare<Signed<W>>` on `Interval<W>` | §4 |
| src/interval_z.rs:140 | `IntervalZ` bounds stored as i64 in the entry | §3 |
| src/interval_z.rs:520 | `Mul<Euclid>`, `Compare<Euclid>` on `IntervalZ` | §4 |
| src/word.rs:28 | bitwise and shift operations and lemmas on `Word` | §4 |
| src/word.rs:706 | the 5 native widths; other N top until `Bits<N>` | §2 |
| src/semantics.rs:24 | meanings of bitwise ops, shifts, `bvsmod`, zero divisors | §6 |
| src/domains.rs:266 | `bits` uses the `Word` port of `ExecTnum` (#108) | §2 |

27 sites in 11 files. The sites at §3, §5 and §6, and the `ite` and
zero-divisor parts of §4, belong to this PR. The others are planned work that
the registry reports as unavailable or top until it lands.

## 9. Decisions left to the student

| Decision | Options | Constraint |
|---|---|---|
| entry type | one `Value` enum with a byte encoding (§5); or one `Copy` entry type per carrier, generic over `W` | the pool sees bytes of fixed size per sort |
| Int bounds | i64 with existing trusted conversions; i128 with 2 new trusted `IBig` functions; an `IBig` side arena (eclass-analysis §4) | i128 or the arena must add rows to the trust ledger; measure how often a bound saturates |
| congruence over `W` | modulus by exponent; modulus as `W` with a reserved code for 2^N | fixed by the congruence port; the entry size follows |
| masked records | `normalize` takes the mask and skips steps; or a `restrict(m)` after each call | `wf_masked(m)` must make byte equality set equality |
| Int `div`, `mod` by zero | top; a fresh value per class | SMT-LIB leaves the value unspecified, so top is the sound choice |
| n-ary operators | the registry folds `and`, `or`, `+`, `distinct`; or #1 desugars them to binary | the fold must keep the forward contract |
| `reduce` fuel | none (record `normalize` is complete); a fuel argument as in `Product::reduce` | the contract is `γ(r) = γ(a)` for every fuel |
| top-only carriers | entry size 0; or no pool for the sort (`abs: None`) | agree with #2 |
| name tables | `match` on `&str` outside `verus!`; a generated table | each name is tested against a reference implementation |

## 10. Acceptance criteria

1. `cargo verus verify` in `abstract-domains` reports 0 errors, and
   `--time-expanded` shows no function above 10 s.
2. `grep -nE 'admit\(|assume\(|external_body|axiom'` finds nothing in
   src/registry.rs. The trust ledger in domain-traits.md §7 is unchanged,
   unless §9 chooses i128 and the PR adds its rows.
3. Every exec function of the registry inside `verus!` states the contract of
   §6 in its `ensures`.
4. The 24 tests of tests/registry.rs lose their `#[ignore]` and pass. The
   bodies check brute force at u8 with tests/common/mod.rs, and
   `u128_instance_is_exercised` runs the 128-bit carrier.
5. `forward_transfers_are_sound_on_u8_pairs` prints `pct_non_optimal` per
   operator, and the PR description quotes the numbers with the test name.
6. `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets --
   -D warnings`, and `cargo test -p semi-persistent-abstract-domains`, with
   and without `--all-features`, pass.
7. The PR removes every `TODO(abs-domain-registry)` it resolves, and its
   description lists the remaining rows of §8.

## 11. Links

- [domain-traits.md](../domain-traits.md): `Domain`, `Canonical`, `Word`,
  `Semantics`, transfer traits, trust ledger.
- [reduced-product.md](../reduced-product.md): fact records, `Channel`,
  `Refine`, the 4 events, planned work.
- [proof-status.md](../proof-status.md): which `ExecTnum` operations have
  containment proofs.
- [eclass-analysis.md](../../../egraph/doc/future/eclass-analysis.md): §4
  storage, §5 domain sets and widths, §6 tier 1 transfers and `ite`, §8
  derived merges.
- tests/registry.rs: the acceptance tests.
- SMT-LIB 2.6, theories `Ints`, `Core` and `FixedSizeBitVectors`, and logic
  `QF_BV` for the zero-divisor values.
