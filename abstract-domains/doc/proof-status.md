# Abstract Domains Proof Status

**939 verified, 0 errors**, **3 admits** (all in L4 `ExecUnum`: `add`, `from_interval`, `mul`)

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

### ExecTnum — no admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | `wf()` | ✅ proved |
| `bw_not`, `bw_and_not` | `wf()` | ✅ proved |
| `neg`, `sub`, `rsh`, `lsh` | `wf()` | ✅ proved |
| `mul` | `wf()` | ✅ proved |
| `bw_or` | `wf()`, `r.has(c1 \| c2)` | ✅ proved |
| `bw_and` | `wf()`, `r.has(c1 & c2)` | ✅ proved |
| `bw_xor` | `wf()`, `r.has(c1 ^ c2)` | ✅ proved |
| `add` | `wf()`, `r.has(wrapping_add)` | ✅ proved |
| `join` | `wf()`, `self/t.has ⟹ r.has` | ✅ proved |
| `meet` | `wf()`, `both.has ⟹ r.has` | ✅ proved |

### ExecAnum — no admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | — | ✅ proved |
| `to_etn` | `wf()` | ✅ proved |
| `ones_mask` | `r >= n` | ✅ proved |
| `top_has` | `top().has(n)` | ✅ proved |
| `add` | `r.has(wrapping_add)` | ✅ proved |
| `div_const` | `r.has(c / d)` | ✅ proved |

### ExecUnum — 3 admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | — | ✅ proved |
| `to_etn` | `wf()` | ✅ proved |
| `top_has` | `top().has(n)` | ✅ proved |
| `add` | `r.has(wrapping_add)` | ❌ admit (bridge_add + L3) |
| `mul` | `r.has(wrapping_mul)` | ❌ admit (bridge_mul + L3) |
| `from_interval` | `iv.has(c) ⟹ r.has(c)` | ❌ admit (interval→unum embedding) |

### Interval — fully proved ✅

| Operation | Ensures | Status |
|-----------|---------|--------|
| `top_has` | `top().has(x)` | ✅ |
| `add` | `r.has(wrapping_add)` (no-overflow guard) | ✅ |
| `meet` | `both.has ⟹ r.has` | ✅ |
| `join` | `self/t.has ⟹ r.has` | ✅ |
| `div_const` | `r.has(c / d)` | ✅ |

### ReducedProduct — no admits

| Operation | Ensures | Status |
|-----------|---------|--------|
| `constant`, `top` | `wf()` | ✅ proved |
| `bw_or/and/xor`, `sub`, `mul`, `div_const`, `rsh`, `lsh`, `join`, `meet`, `neg` | `wf()` | ✅ proved |
| `reduce` | `wf()`, `self.has ⟹ r.has` | ✅ proved |
| `add` | `wf()`, `r.has(wrapping_add)` | ✅ proved |

---

## Remaining work

Three admits remain, all in `ExecUnum`:

1. **`ExecUnum::add`** — needs bridge between native `wrapping_add` and L3 `ChoppedUnum::add_sound`.
2. **`ExecUnum::mul`** — needs bridge between native `wrapping_mul` and L3 `ChoppedUnum::mul_sound`.
3. **`ExecUnum::from_interval`** — needs embedding lemma showing the constructed Unum covers every element of the source interval.

---

## Progress log

### 2026-04-18 — Current state
- **939 verified, 0 errors, 3 admits**. Verification clean via `cargo verus verify` in 2m 20s.
- Verus pinned to `0.2026.04.12.f1166c4`, vstd to `=0.0.0-2026-04-12-0118`.
- CI switched to `cargo verus verify -- --trace`; `verify-all.sh` kept for local per-module iteration.
- Renamed `Bit::T/F` → `Bit::t/f`, `bit_IsRustBit` → `bit_is_rust_bit`, `accV/accM` → `acc_v/acc_m` to eliminate snake_case warnings.
- Remaining work: 3 admits in `ExecUnum` (`add`, `mul`, `from_interval`).
