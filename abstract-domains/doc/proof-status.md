# Abstract Domains Proof Status

**880 verified, 1 error** (exp_128 rlimit), **13 admits** (all in L4 domains.rs)

---

## L1 — Bit primitives (`bools.rs`, `tbit.rs`, `nats.rs`)

All proved. No admits.

### bools.rs — Bit type
- `Bit::full_add` — 3-input full adder, carry + sum

### tbit.rs — TBit (tristate bit)
- `has`, `join`, `meet`, `add_carry`, `add`, `xor`, `or`, `and`, `and_not`
- All soundness lemmas proved

### nats.rs — Infinite bitstring operations (50 proof fns)
- **Bit access**: `hd_tl`, `hd_cons`, `bit_zero`, `bit_tl`, `bit_cons`, `eq_from_bits`
- **Bitwise**: `or_bit`, `xor_bit`, `and_bit`, `and_not_bit`, `mapd_bit`, `mapd_hd_tl`
- **Arithmetic**: `nat_add_carry_correct`, `nat_add_correct`, `nat_add_or`, `disj_bits`, `disj_zero`, `disj_cons`
- **Exponentiation**: `exp_pos`, `exp_8`, `exp_16`, `exp_32`, `exp_64`, `exp_128` ⚠️ rlimit, `exp_concrete`, `exp_eq_pow2`
- **Chopping**: `chop_bit`, `chop_idem`, `chop_disj`, `chop_mapd`, `chop_nat_add`, `chop_nat_mul`, `chop_nat_add_pow2`, `chop_id`, `chop_is_mod`
- **Shift**: `chop_lsh`, `lsh_plus`, `rsh_plus`, `lsh_is_times2`, `lsh_exp`, `rsh_div`
- **Misc**: `xor_ones_complement`, `all_ones_covers`, `all_ones_has`, `all_ones_r_bit`, `bit_exp`, `len_bound`

---

## L2 — Abstract domains over infinite bitstrings

All proved. No admits.

### tnum.rs — Tnum (32 proof fns)
- **Membership**: `has_equiv`
- **Bitwise soundness**: `or_sound`, `and_sound`, `and_not_sound`, `xor_sound`, `bitwise_inv`
- **Shift soundness**: `rsh_sound`, `lsh_sound`, `lshi_sound`, `rshi_sound`
- **Lattice**: `join_sound`, `meet_sound`
- **Add**: `add_carry_sound`, `add_carry_zero`, `add_carry_val_zero`, `add_sound`, `add_bitwise_eq`, `add_inv`, `add_inv_carry`, `add_bitwise_inv`
- **Mul**: `times_b_inv`, `mul_bit_sound`, `chop_sound`
- **Extension**: `tn_ext`

### anum.rs — Anum (19 proof fns)
- **Core**: `from_tnum_sound`, `add_sound`, `add_zero`, `tnum_has_from_anum`
- **Mul**: `mul_step_sound`, `tnum_mul_sound`, `mul_step_r`, `mul_step_anum_sound`, `mul_anum_sound`
- **Div**: `div_const_sound`

### unum.rs — Unum (10 proof fns)
- **Add**: `add_sound`, `add_bounded_sound`
- **Mul**: `mul_sound`, `mul_bounded_sound`
- **Misc**: `offset_bounded`, `offset_from_bound`, `chop_sound`, `to_anum_sound`, `carry_out_c_overflow`

### div.rs — Tnum division/subtraction (12 proof fns)
- `has_bounds`, `join_inv`, `max_has`
- `sub_const_sound`, `lsh_or_tb_sound`, `div_const_sound`
- `neg_tn_sound`, `sub_sound`, `sub_inv`, `div_sound`

---

## L3 — Chopped (bounded-width) domains (`chopped.rs`)

All proved. No admits.

### ChoppedTnum (10 proof fns)
- **Bitwise**: `or_inv`, `and_inv`, `xor_inv`
- **Arithmetic**: `add_sound`, `add_inv`, `mul_sound`
- **Shift**: `rsh_sound`, `lsh_sound`
- **Lattice**: `join_sound`, `meet_sound`

### ChoppedAnum (2 proof fns)
- `add_sound`, `div_const_sound`

### ChoppedUnum (2 proof fns)
- `add_sound`, `mul_sound`

---

## L4 — Executable machine-word domains (`domains.rs`)

Macro-generated for u8, u16, u32, u64, u128.

### Bridge lemmas ✅
- `bridge_add(a, b)` — `wrapping_add(a,b) as nat == chop(nat_add(a as nat, b as nat), W)`
- `bridge_mul(a, b)` — `wrapping_mul(a,b) as nat == chop(nat_mul(a as nat, b as nat), W)`

### ExecTnum — 6 admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | `wf()` | ✅ proved |
| `bw_not`, `bw_and_not` | `wf()` | ✅ proved |
| `neg`, `sub`, `rsh`, `lsh` | `wf()` | ✅ proved |
| `mul` | `wf()` | ✅ proved |
| `bw_or` | `wf()`, `r.has(c1 \| c2)` | ❌ admit (bitwise bridge) |
| `bw_and` | `wf()`, `r.has(c1 & c2)` | ❌ admit (bitwise bridge) |
| `bw_xor` | `wf()`, `r.has(c1 ^ c2)` | ❌ admit (bitwise bridge) |
| `add` | `wf()`, `r.has(wrapping_add)` | ❌ admit (bitwise bridge + bridge_add) |
| `join` | `wf()`, `self/t.has ⟹ r.has` | ❌ admit (bitwise bridge) |
| `meet` | `wf()`, `both.has ⟹ r.has` | ❌ admit (bitwise bridge) |

### ExecAnum — 3 admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | — | ✅ proved |
| `to_etn` | `wf()` | ✅ proved |
| `ones_mask` | `r >= n` | ✅ proved |
| `top_has` | `top().has(n)` | ❌ admit (standalone) |
| `add` | `r.has(wrapping_add)` | ❌ admit (overflow + L2) |
| `div_const` | `r.has(c / d)` | ❌ admit (L3 connection) |

### ExecUnum — 2 admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | — | ✅ proved |
| `to_etn` | `wf()` | ✅ proved |
| `top_has` | `top().has(n)` | ✅ proved |
| `add` | `r.has(wrapping_add)` | ❌ admit (bridge_add + L3) |
| `mul` | `r.has(wrapping_mul)` | ❌ admit (bridge_mul + L3) |

### Interval — fully proved ✅

| Operation | Ensures | Status |
|-----------|---------|--------|
| `top_has` | `top().has(x)` | ✅ |
| `add` | `r.has(wrapping_add)` (no-overflow guard) | ✅ |
| `meet` | `both.has ⟹ r.has` | ✅ |
| `join` | `self/t.has ⟹ r.has` | ✅ |
| `div_const` | `r.has(c / d)` | ✅ |

### ReducedProduct — 2 admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | `wf()` | ✅ proved |
| `bw_or/and/xor`, `sub`, `mul`, `div_const`, `rsh`, `lsh`, `join`, `meet`, `neg` | `wf()` | ✅ proved |
| `reduce` | `wf()`, `self.has ⟹ r.has` | ❌ admit (compose components) |
| `add` | `wf()`, `r.has(wrapping_add)` | ❌ admit (component adds + reduce) |

---

## Key blocker: the native-to-spec bitwise bridge

Every L4 `has` spec is defined via L2 types over `nat` bitstrings (e.g. `ExecTnum::has(x) == to_tn().has(x as nat)`). But the L4 *computations* use native `$uint` ops (`^`, `|`, `&`, `wrapping_add`). To connect the two we need:

1. **`bit_is_native_bit(n: $uint, i: nat)`** — `bit(n as nat, i) == ((n >> i) & 1 == 1)` for `i < W`. Per-bit bridge from spec `bit()` to native bit extraction. Provable `by(bit_vector)`.
2. **`native_xor(a, b: $uint)`** — `bw_xor(a as nat, b as nat) == (a ^ b) as nat` via `eq_from_bits` + `bit_is_native_bit` + `xor_bit`.
3. **`native_or(a, b: $uint)`**, **`native_and(a, b: $uint)`**, **`native_not(a: $uint)`** — same pattern.

Once these exist in the macro, every L4 proof can rewrite native ops into spec ops and delegate to L2/L3 soundness. This unlocks all 13 admits — the 6 ExecTnum ones directly, and the ExecAnum/ExecUnum/ReducedProduct ones indirectly (their `has` definitions expand to Tnum/Anum/Unum `has` over `nat`, which need the bridge to relate to the native fields).

The prototype `bit_IsRustBit` in `exec_tnum.rs` (u64-only) proved the approach works. Now generalized into the macro for all 5 widths (commit 3bd4ba8).

## Critical path to zero admits

1. ~~**Bitwise bridge**~~ — ✅ DONE. `bit_is_native_bit`, `native_xor`, `native_or`, `native_and` proved for all 5 widths.
2. **ExecAnum::top_has** (#7) — standalone, needs `exp_concrete` + `all_ones_has`. Quickest win.
3. **ExecTnum bitwise/lattice** (#1–6) — use `native_xor`/`native_or`/`native_and` + L2 soundness.
4. **ExecAnum::add** (#8) — overflow→`top_has`, non-overflow via L2 `Anum::add_sound`.
5. **ExecAnum::div_const** (#9) — connect to L3 `ChoppedAnum::div_const_sound`.
6. **ExecUnum::add/mul** (#10–11) — `bridge_add`/`bridge_mul` + L3 `ChoppedUnum::add_sound`/`mul_sound`.
7. **ReducedProduct::reduce** (#12) — compose component narrowing proofs.
8. **ReducedProduct::add** (#13) — compose component adds + reduce soundness.

---

## Progress log

### 2026-04-08 — Baseline established
- Reset to clean b7a91f6 (821 verified, 0 errors).
- Added all 13 L4 soundness `ensures` with `admit()` placeholders.
- Commit 2850e9c: 825 verified, 1 error (exp_128 rlimit), 13 admits.
- Proved bitwise bridge: `bit_is_native_bit`, `native_xor`, `native_or`, `native_and` for all 5 widths.
- Commit 3bd4ba8: 880 verified, 1 error, 13 admits.

### 2026-04-09 — 9 admits eliminated
- Added `chop_bw_xor`, `chop_bw_or`, `chop_bw_and_not` to nats.rs (closure identity workaround).
- Added `native_and_not` bridge lemma, `ExecTnum::wf_inv`, `ExecTnum::to_chopped` helpers.
- Added `ExecAnum::has_eq_uint` bridge (nat-level has ↔ uint-level predicate).
- Strengthened `ones_mask` ensures: `r & (r+1) == 0` (proves 2^k - 1 form).
- Proved ExecTnum: `bw_or`, `bw_and`, `bw_xor`, `join`, `meet`, `add` — all 6 admits eliminated.
- Proved ExecAnum: `top_has`, `add` (with overflow→top), `div_const` — all 3 admits eliminated.
- Fixed `exp_128` rlimit, `field_admits_add_carry` rlimit, `by(compute_only)` recursion depth.
- 4 admits remaining: ExecUnum(add, mul), ReducedProduct(reduce, add).
