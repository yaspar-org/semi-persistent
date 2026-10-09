// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Machine words, generic over the width.
//!
//! Domains over machine integers are written once, generic over `W: Word`, and
//! store native words (`u8`..`u128`). Specifications read a word through
//! `view()` as a `nat`, which is ghost and erased. Width-specific facts are
//! proof obligations of this trait, discharged once per width by `impl_word!`.
//!
//! A word is a bit pattern. Signedness is not a property of the carrier; it is
//! chosen by the operation semantics (`semantics::Unsigned` / `semantics::Signed`),
//! so there is one domain instance per width, not one per signedness.
//!
//! No operation needs a type wider than `W`: products are either checked
//! (`checked_mul`) or reduced (`mulmod`), and gcds with 2^N use 2-adic
//! valuations (`trailing_zeros`). This is what lets `u128` be a `Word`.
// Lemma imports are used only by proof code, which is erased outside Verus.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::*;

verus! {

pub trait Word: Sized + Copy {
    /// Width in bits.
    spec fn bits() -> nat;

    /// 2^bits.
    spec fn modulus() -> nat;

    /// Unsigned reading of the bit pattern.
    spec fn view(self) -> nat;

    /// The word whose unsigned reading is `i mod 2^bits`.
    spec fn from_int(i: int) -> Self;

    proof fn lemma_modulus()
        ensures
            Self::modulus() >= 256,
            Self::modulus() % 2 == 0,
            Self::modulus() == pow2(Self::bits()),
            8 <= Self::bits() <= 128,
    ;

    proof fn lemma_view_bounded(self)
        ensures
            self.view() < Self::modulus(),
    ;

    proof fn lemma_view_injective(a: Self, b: Self)
        ensures
            a.view() == b.view() ==> a == b,
    ;

    proof fn lemma_from_int(i: int)
        ensures
            Self::from_int(i).view() == i % (Self::modulus() as int),
    ;

    fn zero() -> (r: Self)
        ensures
            r.view() == 0,
    ;

    fn one() -> (r: Self)
        ensures
            r.view() == 1,
    ;

    fn max() -> (r: Self)
        ensures
            r.view() == Self::modulus() - 1,
    ;

    fn le(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() <= o.view()),
    ;

    fn lt(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() < o.view()),
    ;

    fn eq(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() == o.view()),
    ;

    /// Addition when it does not wrap.
    fn checked_add(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(s) => s.view() == self.view() + o.view(),
                None => self.view() + o.view() >= Self::modulus(),
            },
    ;

    /// Subtraction when it does not wrap.
    fn checked_sub(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(s) => s.view() == self.view() - o.view(),
                None => self.view() < o.view(),
            },
    ;

    /// `modulus - self` for a nonzero word.
    fn neg_nonzero(self) -> (r: Self)
        requires
            self.view() != 0,
        ensures
            r.view() == Self::modulus() - self.view(),
    ;

    fn udiv(self, o: Self) -> (r: Self)
        requires
            o.view() != 0,
        ensures
            r.view() == self.view() / o.view(),
    ;

    fn urem(self, o: Self) -> (r: Self)
        requires
            o.view() != 0,
        ensures
            r.view() == self.view() % o.view(),
    ;

    fn bit_width() -> (r: u32)
        ensures
            r as nat == Self::bits(),
    ;

    /// 2^(bits-1), the boundary between the two signed halves.
    fn half() -> (r: Self)
        ensures
            r.view() == Self::modulus() / 2,
    ;

    fn wrapping_add(self, o: Self) -> (r: Self)
        ensures
            r == Self::from_int(self.view() as int + o.view() as int),
    ;

    fn wrapping_sub(self, o: Self) -> (r: Self)
        ensures
            r == Self::from_int(self.view() as int - o.view() as int),
    ;

    /// Multiplication when it does not wrap.
    fn checked_mul(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(p) => p.view() == self.view() * o.view(),
                None => self.view() * o.view() >= Self::modulus(),
            },
    ;

    /// The 2-adic valuation: `self = q * 2^r` with `q` odd, or `bits` for 0.
    fn trailing_zeros(self) -> (r: u32)
        ensures
            self.view() == 0 ==> r as nat == Self::bits(),
            self.view() != 0 ==> (r as nat) < Self::bits() && tz_spec(self.view(), r as nat),
    ;

    /// `(self * o) mod m`, without a wider type.
    fn mulmod(self, o: Self, m: Self) -> (r: Self)
        requires
            m.view() > 0,
        ensures
            r.view() == (self.view() * o.view()) % m.view(),
    ;

    /// Bitwise operators on the bit pattern.
    spec fn and(self, o: Self) -> Self;

    spec fn or(self, o: Self) -> Self;

    spec fn xor(self, o: Self) -> Self;

    spec fn not(self) -> Self;

    /// The smallest `2^k - 1` at or above `self`.
    spec fn ones_above(self) -> Self;

    fn bit_and(self, o: Self) -> (r: Self)
        ensures
            r == self.and(o),
    ;

    fn bit_or(self, o: Self) -> (r: Self)
        ensures
            r == self.or(o),
    ;

    fn bit_xor(self, o: Self) -> (r: Self)
        ensures
            r == self.xor(o),
    ;

    fn bit_not(self) -> (r: Self)
        ensures
            r == self.not(),
    ;

    /// `ones_above`, by smearing the leading one downwards.
    fn smear(self) -> (r: Self)
        ensures
            r == self.ones_above(),
    ;

    proof fn lemma_and_le(a: Self, b: Self)
        ensures
            a.and(b).view() <= a.view(),
            a.and(b).view() <= b.view(),
    ;

    proof fn lemma_or_ge(a: Self, b: Self)
        ensures
            a.view() <= a.or(b).view(),
            b.view() <= a.or(b).view(),
    ;

    /// Operands at most `m` have no bit above `m`'s leading one.
    proof fn lemma_below_ones_above(a: Self, b: Self, m: Self)
        requires
            a.view() <= m.view(),
            b.view() <= m.view(),
        ensures
            m.view() <= m.ones_above().view(),
            a.or(b).view() <= m.ones_above().view(),
            a.xor(b).view() <= m.ones_above().view(),
    ;

    proof fn lemma_not(a: Self)
        ensures
            a.not().view() == Self::modulus() - 1 - a.view(),
    ;

    /// The word as a shift amount, when it is below the width.
    fn to_shift(self) -> (r: Option<u32>)
        ensures
            match r {
                Some(k) => k as nat == self.view() && (k as nat) < Self::bits(),
                None => self.view() >= Self::bits(),
            },
    ;

    /// Logical right shift.
    fn shr(self, k: u32) -> (r: Self)
        requires
            (k as nat) < Self::bits(),
        ensures
            r.view() == self.view() / pow2(k as nat),
    ;

    /// Left shift when it does not wrap.
    fn checked_shl(self, k: u32) -> (r: Option<Self>)
        requires
            (k as nat) < Self::bits(),
        ensures
            match r {
                Some(s) => s.view() == self.view() * pow2(k as nat),
                None => self.view() * pow2(k as nat) >= Self::modulus(),
            },
    ;
}

/// `x = q * 2^t` with `q` odd.
pub open spec fn tz_spec(x: nat, t: nat) -> bool {
    x % pow2(t) == 0 && (x / pow2(t)) % 2 == 1
}

proof fn lemma_pow2_word(bits: nat)
    requires
        bits == 8 || bits == 16 || bits == 32 || bits == 64 || bits == 128,
    ensures
        bits == 8 ==> pow2(bits) == 0x100,
        bits == 16 ==> pow2(bits) == 0x1_0000,
        bits == 32 ==> pow2(bits) == 0x1_0000_0000,
        bits == 64 ==> pow2(bits) == 0x1_0000_0000_0000_0000,
        bits == 128 ==> pow2(bits) == 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff + 1,
{
    lemma2_to64();
    if bits == 128 {
        lemma_pow2_adds(64, 64);
    }
}

/// A nonzero multiple of 2^t below 2^bits has t < bits.
proof fn lemma_tz_lt_bits(x: nat, t: nat, bits: nat)
    requires
        x > 0,
        x < pow2(bits),
        x % pow2(t) == 0,
    ensures
        t < bits,
{
    lemma_pow2_pos(t);
    if t >= bits {
        if t > bits {
            lemma_pow2_strictly_increases(bits, t);
        }
        lemma_small_mod(x, pow2(t));
    }
}

/// vstd specifies `trailing_zeros` only up to u64: split into two halves.
fn tz_u128(x: u128) -> (r: u32)
    ensures
        x == 0 ==> r == 128,
        x != 0 ==> r < 128 && tz_spec(x as nat, r as nat),
{
    let lo = (x % 0x1_0000_0000_0000_0000u128) as u64;
    let hi = (x / 0x1_0000_0000_0000_0000u128) as u64;
    proof {
        lemma2_to64();
        lemma_fundamental_div_mod(x as int, pow2(64) as int);
        lemma_div_is_ordered(x as int, u128::MAX as int, pow2(64) as int);
        assert(u128::MAX as int / 0x1_0000_0000_0000_0000int == u64::MAX as int) by (compute_only);
    }
    if lo != 0 {
        let t = tz_u64(lo);
        proof {
            let p = pow2(t as nat);
            lemma_pow2_pos(t as nat);
            lemma_pow2_adds(t as nat, (64 - t) as nat);
            let k = pow2((64 - t) as nat);
            lemma_pow2_pos((64 - t) as nat);
            assert(x as int == hi * pow2(64) + lo);
            assert((hi * k) * p == hi * pow2(64)) by (nonlinear_arith)
                requires
                    pow2(64) == p * k,
            ;
            lemma_fundamental_div_mod(lo as int, p as int);
            let lq = lo as int / p as int;
            assert(x as int == (hi * k + lq) * p) by (nonlinear_arith)
                requires
                    x as int == (hi * k) * p + lo,
                    lo == lq * p + lo as int % p as int,
                    lo as int % p as int == 0,
            ;
            lemma_mod_multiples_basic(hi * k + lq, p as int);
            lemma_div_multiples_vanish(hi * k + lq, p as int);
            lemma_pow2_unfold((64 - t) as nat);
            assert((hi * k + lq) % 2 == lq % 2) by {
                let k2 = pow2((64 - t - 1) as nat);
                assert(hi * k == 2 * (hi * k2)) by (nonlinear_arith)
                    requires
                        k == 2 * k2,
                ;
                lemma_mod_multiples_vanish(hi * k2, lq, 2);
            }
        }
        t
    } else if hi != 0 {
        let t = tz_u64(hi);
        proof {
            let p = pow2(t as nat);
            lemma_pow2_pos(t as nat);
            lemma_pow2_adds(64, t as nat);
            assert(x as int == hi * pow2(64));
            lemma_fundamental_div_mod(hi as int, p as int);
            let hq = hi as int / p as int;
            assert(x as int == hq * (pow2(64) * p)) by (nonlinear_arith)
                requires
                    x as int == hi * pow2(64),
                    hi == hq * p + hi as int % p as int,
                    hi as int % p as int == 0,
            ;
            lemma_mod_multiples_basic(hq, (pow2(64) * p) as int);
            lemma_div_multiples_vanish(hq, (pow2(64) * p) as int);
        }
        64 + t
    } else {
        128
    }
}

/// `(a * b) mod m` for operands below 2^32, computed in u64. For u8, u16 and
/// u32 one widening product measured 0.9 ns against 39.6 ns for a u32
/// double-and-add loop (examples/mulmod_width.rs), so these widths widen.
fn mulmod_via_u64(a: u64, b: u64, m: u64) -> (r: u64)
    requires
        a < 0x1_0000_0000,
        b < 0x1_0000_0000,
        m > 0,
    ensures
        r < m,
        r as int == (a * b) % (m as int),
{
    proof {
        lemma_mul_upper_bound(a as int, 0xffff_ffff, b as int, 0xffff_ffff);
        lemma_mod_bound((a * b) as int, m as int);
    }
    (a * b) % m
}

/// `(a * b) mod m` for u64 operands, computed in u128.
fn mulmod_via_u128(a: u64, b: u64, m: u64) -> (r: u64)
    requires
        m > 0,
    ensures
        r < m,
        r as int == (a * b) % (m as int),
{
    proof {
        lemma_mul_upper_bound(a as int, u64::MAX as int, b as int, u64::MAX as int);
        lemma_mod_bound((a * b) as int, m as int);
    }
    ((a as u128) * (b as u128) % (m as u128)) as u64
}

/// `(a * b) mod m` for u64: the native product when it fits, else the u128
/// product. The u128 product stays because the same-width double-and-add loop
/// is slower: 83.4 ns against 23.3 ns on full-range operands, and 39.4 ns
/// against 1.4 ns when both operands are below 2^32, where the `checked_mul`
/// path applies (examples/mulmod_width.rs).
fn mulmod_u64(a: u64, b: u64, m: u64) -> (r: u64)
    requires
        m > 0,
    ensures
        r < m,
        r as int == (a * b) % (m as int),
{
    match a.checked_mul(b) {
        Some(p) => {
            proof {
                lemma_mod_bound(p as int, m as int);
            }
            p % m
        },
        None => mulmod_via_u128(a, b, m),
    }
}

/// `(x + y) mod m` for `x, y < m`, without overflow.
fn addmod_u128(x: u128, y: u128, m: u128) -> (r: u128)
    requires
        x < m,
        y < m,
    ensures
        r < m,
        r as int == (x + y) % (m as int),
{
    proof {
        if x + y >= m {
            lemma_mod_sub_multiples_vanish((x + y) as int, m as int);
            lemma_small_mod((x + y - m) as nat, m as nat);
        } else {
            lemma_small_mod((x + y) as nat, m as nat);
        }
    }
    if x >= m - y {
        x - (m - y)
    } else {
        x + y
    }
}

/// `(a * b) mod m` for u128: one native product when `m < 2^64`, otherwise
/// double-and-add over the bits of `b`, every intermediate value below `m`.
fn mulmod_u128(a: u128, b: u128, m: u128) -> (r: u128)
    requires
        m > 0,
    ensures
        r < m,
        r as int == (a * b) % (m as int),
{
    if m <= u64::MAX as u128 {
        let a1 = a % m;
        let b1 = b % m;
        proof {
            lemma_mul_upper_bound(a1 as int, u64::MAX as int, b1 as int, u64::MAX as int);
            lemma_mul_mod_noop(a as int, b as int, m as int);
            lemma_mod_bound((a1 * b1) as int, m as int);
        }
        return (a1 * b1) % m;
    }
    let mut r: u128 = 0;
    let mut base: u128 = a % m;
    let mut e: u128 = b;
    proof {
        lemma_mod_bound(a as int, m as int);
        lemma_mul_mod_noop_left(a as int, b as int, m as int);
    }
    while e > 0
        invariant
            m > 0,
            r < m,
            base < m,
            (r + base * e) % (m as int) == (a * b) % (m as int),
        decreases e,
    {
        let e2 = e / 2;
        proof {
            lemma_fundamental_div_mod(e as int, 2);
        }
        if e % 2 == 1 {
            let r2 = addmod_u128(r, base, m);
            let b2 = addmod_u128(base, base, m);
            proof {
                assert(r + base * e == (r + base) + (2 * base) * e2) by (nonlinear_arith)
                    requires
                        e == 2 * e2 + 1,
                ;
                lemma_add_mod_noop((r + base) as int, (2 * base) * e2, m as int);
                lemma_mul_mod_noop_left((2 * base) as int, e2 as int, m as int);
                lemma_add_mod_noop(r2 as int, b2 * e2, m as int);
                lemma_small_mod(r2 as nat, m as nat);
                lemma_mul_mod_noop_left(b2 as int, e2 as int, m as int);
                lemma_small_mod(b2 as nat, m as nat);
            }
            r = r2;
            base = b2;
        } else {
            let b2 = addmod_u128(base, base, m);
            proof {
                assert(base * e == (2 * base) * e2) by (nonlinear_arith)
                    requires
                        e == 2 * e2,
                ;
                lemma_add_mod_noop(r as int, (2 * base) * e2, m as int);
                lemma_mul_mod_noop_left((2 * base) as int, e2 as int, m as int);
                lemma_add_mod_noop(r as int, b2 * e2, m as int);
                lemma_mul_mod_noop_left(b2 as int, e2 as int, m as int);
                lemma_small_mod(b2 as nat, m as nat);
            }
            base = b2;
        }
        e = e2;
    }
    proof {
        lemma_small_mod(r as nat, m as nat);
    }
    r
}

/// Two's-complement reading of the bit pattern.
/// 2^k as a u128, assembled from u64 shifts (vstd proves `shl` only up to u64).
fn pow2_u128(k: u32) -> (r: u128)
    requires
        k < 128,
    ensures
        r == pow2(k as nat),
{
    if k < 64 {
        proof {
            vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, k as u64);
        }
        (1u64 << (k as u64)) as u128
    } else {
        let j = k - 64;
        proof {
            vstd::bits::lemma_u64_pow2_no_overflow(j as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, j as u64);
            lemma_pow2_adds(j as nat, 64);
            lemma2_to64();
            lemma_pow2_strictly_increases(k as nat, 128);
            lemma_pow2_word(128);
        }
        ((1u64 << (j as u64)) as u128) * 0x1_0000_0000_0000_0000u128
    }
}

pub open spec fn signed_view<W: Word>(w: W) -> int {
    if w.view() < W::modulus() / 2 {
        w.view() as int
    } else {
        w.view() - W::modulus()
    }
}

} // verus!

/// Native `trailing_zeros` at one width, from vstd's per-width axiom.
macro_rules! tz_native {
    ($tz:ident, $lemma:ident, $t:ty, $bits:literal, $axiom:ident, $shr:path, $pow2:path, $shl:path) => {
        verus! {
            proof fn $lemma(i: $t, t: $t)
                requires
                    i != 0,
                    t < $bits,
                    (i >> t) & 1 == 1,
                    i << sub($bits, t) == 0,
                ensures
                    tz_spec(i as nat, t as nat),
            {
                $shr(i, t);
                let q = i >> t;
                assert(q & 1 == 1 ==> q % 2 == 1) by (bit_vector);
                assert(i << sub($bits, t) == 0 ==> (i >> t) << t == i) by (bit_vector)
                    requires
                        t < $bits,
                ;
                lemma_pow2_pos(t as nat);
                lemma_fundamental_div_mod(i as int, pow2(t as nat) as int);
                $pow2(t as nat);
                assert(q * pow2(t as nat) <= <$t>::MAX) by {
                    lemma_mod_pos_bound(i as int, pow2(t as nat) as int);
                }
                $shl(q, t);
                lemma_mod_multiples_basic(q as int, pow2(t as nat) as int);
            }

            fn $tz(x: $t) -> (r: u32)
                ensures
                    x == 0 ==> r == $bits,
                    x != 0 ==> r < $bits && tz_spec(x as nat, r as nat),
            {
                let r = x.trailing_zeros();
                proof {
                    $axiom(x);
                    if x != 0 {
                        $lemma(x, r as $t);
                    }
                }
                r
            }
        }
    };
}

tz_native!(
    tz_u8,
    lemma_tz_from_shifts_u8,
    u8,
    8,
    axiom_u8_trailing_zeros,
    vstd::bits::lemma_u8_shr_is_div,
    vstd::bits::lemma_u8_pow2_no_overflow,
    vstd::bits::lemma_u8_shl_is_mul
);
tz_native!(
    tz_u16,
    lemma_tz_from_shifts_u16,
    u16,
    16,
    axiom_u16_trailing_zeros,
    vstd::bits::lemma_u16_shr_is_div,
    vstd::bits::lemma_u16_pow2_no_overflow,
    vstd::bits::lemma_u16_shl_is_mul
);
tz_native!(
    tz_u32,
    lemma_tz_from_shifts_u32,
    u32,
    32,
    axiom_u32_trailing_zeros,
    vstd::bits::lemma_u32_shr_is_div,
    vstd::bits::lemma_u32_pow2_no_overflow,
    vstd::bits::lemma_u32_shl_is_mul
);
tz_native!(
    tz_u64,
    lemma_tz_from_shifts_u64,
    u64,
    64,
    axiom_u64_trailing_zeros,
    vstd::bits::lemma_u64_shr_is_div,
    vstd::bits::lemma_u64_pow2_no_overflow,
    vstd::bits::lemma_u64_shl_is_mul
);

macro_rules! impl_word {
    ($t:ty, $bits:expr, $modulus:expr, $tz_ty:ty, $tz:ident, $mm_ty:ty, $mulmod:ident, $shr_is_div:path) => {
        verus! {
            impl Word for $t {
                open spec fn bits() -> nat {
                    $bits
                }

                open spec fn modulus() -> nat {
                    $modulus
                }

                open spec fn view(self) -> nat {
                    self as nat
                }

                open spec fn from_int(i: int) -> Self {
                    (i % ($modulus as int)) as $t
                }

                proof fn lemma_modulus() {
                    lemma_pow2_word($bits);
                }

                proof fn lemma_view_bounded(self) {
                }

                proof fn lemma_view_injective(a: Self, b: Self) {
                }

                proof fn lemma_from_int(i: int) {
                    vstd::arithmetic::div_mod::lemma_mod_bound(i, $modulus as int);
                }

                fn zero() -> (r: Self) {
                    0
                }

                fn one() -> (r: Self) {
                    1
                }

                fn max() -> (r: Self) {
                    <$t>::MAX
                }

                fn le(self, o: Self) -> (b: bool) {
                    self <= o
                }

                fn lt(self, o: Self) -> (b: bool) {
                    self < o
                }

                fn eq(self, o: Self) -> (b: bool) {
                    self == o
                }

                fn checked_add(self, o: Self) -> (r: Option<Self>) {
                    if self <= <$t>::MAX - o {
                        Some(self + o)
                    } else {
                        None
                    }
                }

                fn checked_sub(self, o: Self) -> (r: Option<Self>) {
                    if o <= self {
                        Some(self - o)
                    } else {
                        None
                    }
                }

                fn neg_nonzero(self) -> (r: Self) {
                    <$t>::MAX - (self - 1)
                }

                fn udiv(self, o: Self) -> (r: Self) {
                    self / o
                }

                fn urem(self, o: Self) -> (r: Self) {
                    self % o
                }

                fn bit_width() -> (r: u32) {
                    $bits
                }

                fn half() -> (r: Self) {
                    <$t>::MAX / 2 + 1
                }

                fn wrapping_add(self, o: Self) -> (r: Self) {
                    let ghost i: int = self + o;
                    proof {
                        if i < $modulus {
                            lemma_small_mod(i as nat, $modulus);
                        } else {
                            lemma_mod_sub_multiples_vanish(i, $modulus as int);
                            lemma_small_mod((i - $modulus) as nat, $modulus);
                        }
                    }
                    if self <= <$t>::MAX - o {
                        self + o
                    } else {
                        self - (<$t>::MAX - o) - 1
                    }
                }

                fn wrapping_sub(self, o: Self) -> (r: Self) {
                    let ghost i: int = self - o;
                    proof {
                        if i >= 0 {
                            lemma_small_mod(i as nat, $modulus);
                        } else {
                            lemma_mod_add_multiples_vanish(i, $modulus as int);
                            lemma_small_mod((i + $modulus) as nat, $modulus);
                        }
                    }
                    if o <= self {
                        self - o
                    } else {
                        <$t>::MAX - (o - self - 1)
                    }
                }

                fn checked_mul(self, o: Self) -> (r: Option<Self>) {
                    self.checked_mul(o)
                }

                fn trailing_zeros(self) -> (r: u32) {
                    proof {
                        lemma_pow2_word($bits);
                    }
                    if self == 0 {
                        $bits
                    } else {
                        let t = $tz(self as $tz_ty);
                        proof {
                            lemma_tz_lt_bits(self as nat, t as nat, $bits);
                        }
                        t
                    }
                }

                fn mulmod(self, o: Self, m: Self) -> (r: Self) {
                    $mulmod(self as $mm_ty, o as $mm_ty, m as $mm_ty) as $t
                }

                open spec fn and(self, o: Self) -> Self {
                    self & o
                }

                open spec fn or(self, o: Self) -> Self {
                    self | o
                }

                open spec fn xor(self, o: Self) -> Self {
                    self ^ o
                }

                open spec fn not(self) -> Self {
                    !self
                }

                // The shift amounts `$bits/2, ..., $bits/128` sum to every offset
                // below `$bits`; the ones that are 0 at narrow widths are no-ops.
                open spec fn ones_above(self) -> Self {
                    let x1 = self | (self >> (($bits as $t) / 2));
                    let x2 = x1 | (x1 >> (($bits as $t) / 4));
                    let x3 = x2 | (x2 >> (($bits as $t) / 8));
                    let x4 = x3 | (x3 >> (($bits as $t) / 16));
                    let x5 = x4 | (x4 >> (($bits as $t) / 32));
                    let x6 = x5 | (x5 >> (($bits as $t) / 64));
                    x6 | (x6 >> (($bits as $t) / 128))
                }

                fn bit_and(self, o: Self) -> (r: Self) {
                    self & o
                }

                fn bit_or(self, o: Self) -> (r: Self) {
                    self | o
                }

                fn bit_xor(self, o: Self) -> (r: Self) {
                    self ^ o
                }

                fn bit_not(self) -> (r: Self) {
                    !self
                }

                fn smear(self) -> (r: Self) {
                    let x1 = self | (self >> (($bits as $t) / 2));
                    let x2 = x1 | (x1 >> (($bits as $t) / 4));
                    let x3 = x2 | (x2 >> (($bits as $t) / 8));
                    let x4 = x3 | (x3 >> (($bits as $t) / 16));
                    let x5 = x4 | (x4 >> (($bits as $t) / 32));
                    let x6 = x5 | (x5 >> (($bits as $t) / 64));
                    x6 | (x6 >> (($bits as $t) / 128))
                }

                proof fn lemma_and_le(a: Self, b: Self) {
                    assert(a & b <= a && a & b <= b) by (bit_vector);
                }

                proof fn lemma_or_ge(a: Self, b: Self) {
                    assert(a <= (a | b) && b <= (a | b)) by (bit_vector);
                }

                proof fn lemma_below_ones_above(a: Self, b: Self, m: Self) {
                    let x1 = m | (m >> (($bits as $t) / 2));
                    let x2 = x1 | (x1 >> (($bits as $t) / 4));
                    let x3 = x2 | (x2 >> (($bits as $t) / 8));
                    let x4 = x3 | (x3 >> (($bits as $t) / 16));
                    let x5 = x4 | (x4 >> (($bits as $t) / 32));
                    let x6 = x5 | (x5 >> (($bits as $t) / 64));
                    let x7 = x6 | (x6 >> (($bits as $t) / 128));
                    assert(m <= x7 && x7 & x7.wrapping_add(1) == 0) by (bit_vector)
                        requires
                            x1 == m | (m >> (($bits as $t) / 2)),
                            x2 == x1 | (x1 >> (($bits as $t) / 4)),
                            x3 == x2 | (x2 >> (($bits as $t) / 8)),
                            x4 == x3 | (x3 >> (($bits as $t) / 16)),
                            x5 == x4 | (x4 >> (($bits as $t) / 32)),
                            x6 == x5 | (x5 >> (($bits as $t) / 64)),
                            x7 == x6 | (x6 >> (($bits as $t) / 128)),
                    ;
                    assert((a | b) <= x7 && (a ^ b) <= x7) by (bit_vector)
                        requires
                            a <= x7,
                            b <= x7,
                            x7 & x7.wrapping_add(1) == 0,
                    ;
                }

                proof fn lemma_not(a: Self) {
                    assert(!a == <$t>::MAX - a) by (bit_vector);
                }

                fn to_shift(self) -> (r: Option<u32>) {
                    if self < $bits as $t {
                        Some(self as u32)
                    } else {
                        None
                    }
                }

                fn shr(self, k: u32) -> (r: Self) {
                    proof {
                        $shr_is_div(self, k as $t);
                    }
                    self >> (k as $t)
                }

                fn checked_shl(self, k: u32) -> (r: Option<Self>) {
                    let p = pow2_u128(k);
                    proof {
                        lemma_pow2_word($bits);
                        lemma_pow2_strictly_increases(k as nat, $bits);
                    }
                    self.checked_mul(p as $t)
                }
            }
        }
    };
}

impl_word!(
    u8,
    8,
    0x100,
    u8,
    tz_u8,
    u64,
    mulmod_via_u64,
    vstd::bits::lemma_u8_shr_is_div
);
impl_word!(
    u16,
    16,
    0x1_0000,
    u16,
    tz_u16,
    u64,
    mulmod_via_u64,
    vstd::bits::lemma_u16_shr_is_div
);
impl_word!(
    u32,
    32,
    0x1_0000_0000,
    u32,
    tz_u32,
    u64,
    mulmod_via_u64,
    vstd::bits::lemma_u32_shr_is_div
);
impl_word!(
    u64,
    64,
    0x1_0000_0000_0000_0000,
    u64,
    tz_u64,
    u64,
    mulmod_u64,
    vstd::bits::lemma_u64_shr_is_div
);
impl_word!(
    u128,
    128,
    (0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff + 1),
    u128,
    tz_u128,
    u128,
    mulmod_u128,
    vstd::bits::lemma_u128_shr_is_div
);
