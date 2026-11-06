// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Machine words as bitstrings: the bridge from native words to the nat
//! bitstring model of `nats.rs`, for executable code generic over the width.
//!
//! `BitWord` extends `Word` with the bitwise operators read as `bw_and`,
//! `bw_or`, `bw_xor`, and with the wrapping shift and product read through
//! `chop`. These are the per-width facts, proved once per width by
//! `impl_bitword!` with `bit_vector`; everything else in this file is derived
//! generically from them and from `Word`. Every `Word` width, `u128` included,
//! is a `BitWord`: these per-bit proofs stay small at every width.
#![allow(unused_imports)]
use crate::bools::Bit;
use crate::div::*;
use crate::nats::*;
use crate::word::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub trait BitWord: Word {
    proof fn lemma_and(a: Self, b: Self)
        ensures a.and(b).view() == bw_and(a.view(), b.view()),
    ;

    proof fn lemma_or(a: Self, b: Self)
        ensures a.or(b).view() == bw_or(a.view(), b.view()),
    ;

    proof fn lemma_xor(a: Self, b: Self)
        ensures a.xor(b).view() == bw_xor(a.view(), b.view()),
    ;

    /// Wrapping multiplication.
    fn mul_wrap(self, o: Self) -> (r: Self)
        ensures r.view() == chop(prod(self.view(), o.view()), Self::bits()),
    ;

    /// Wrapping left shift.
    fn shl_wrap(self, k: u32) -> (r: Self)
        requires (k as nat) < Self::bits(),
        ensures r.view() == chop(lshi(self.view(), k as nat), Self::bits()),
    ;
}

/// 2^bits, as `exp`.
pub proof fn lemma_exp_bits<W: Word>()
    ensures exp(W::bits()) == W::modulus(), W::bits() > 0
{
    W::lemma_modulus();
    lemma_pow2(W::bits());
    exp_eq_pow2(W::bits());
}

/// A word fits in its width.
pub proof fn lemma_fits<W: Word>(a: W)
    ensures fits(a.view(), W::bits()), a.view() < exp(W::bits())
{
    lemma_exp_bits::<W>();
    a.lemma_view_bounded();
    chop_id(a.view(), W::bits());
}

/// Wrapping addition is the chopped sum.
pub proof fn lemma_add<W: Word>(a: W, b: W)
    ensures W::from_int(a.view() as int + b.view() as int).view() == chop(nat_add(a.view(), b.view()), W::bits())
{
    lemma_exp_bits::<W>();
    W::lemma_from_int(a.view() as int + b.view() as int);
    nat_add_correct(a.view(), b.view());
    chop_is_mod(nat_add(a.view(), b.view()), W::bits());
}

/// Wrapping subtraction is the chopped sum with the two's complement.
pub proof fn lemma_sub<W: Word>(a: W, b: W)
    ensures W::from_int(a.view() as int - b.view() as int).view()
        == chop(nat_add(a.view(), (exp(W::bits()) - b.view()) as nat), W::bits())
{
    let m = W::modulus() as int;
    lemma_exp_bits::<W>();
    lemma_fits(b);
    W::lemma_from_int(a.view() as int - b.view() as int);
    let s = nat_add(a.view(), (exp(W::bits()) - b.view()) as nat);
    nat_add_correct(a.view(), (exp(W::bits()) - b.view()) as nat);
    chop_is_mod(s, W::bits());
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(a.view() as int - b.view() as int, m);
}

/// Wrapping negation is the chopped two's complement.
pub proof fn lemma_neg<W: Word>(c: W)
    ensures W::from_int(0 - c.view() as int).view() == chop((exp(W::bits()) - c.view()) as nat, W::bits())
{
    let m = W::modulus() as int;
    lemma_exp_bits::<W>();
    lemma_fits(c);
    W::lemma_from_int(0 - c.view() as int);
    chop_is_mod((exp(W::bits()) - c.view()) as nat, W::bits());
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(0 - c.view() as int, m);
}

/// Bitwise not is xor with the all-ones word.
pub proof fn lemma_not<W: Word>(a: W)
    ensures a.not().view() == bw_xor(a.view(), all_ones(W::bits()))
{
    lemma_exp_bits::<W>();
    lemma_fits(a);
    W::lemma_not(a);
    xor_ones_complement(a.view(), W::bits());
}

/// And-not is bw_and_not.
pub proof fn lemma_and_not<W: BitWord>(a: W, b: W)
    ensures a.and(b.not()).view() == bw_and_not(a.view(), b.view())
{
    let w = W::bits();
    lemma_fits(a);
    lemma_not(b);
    W::lemma_and(a, b.not());
    let ones = all_ones(w);
    assert forall|i: nat| #![auto] bit(bw_and(a.view(), bw_xor(b.view(), ones)), i) == bit(bw_and_not(a.view(), b.view()), i) by {
        and_bit(a.view(), bw_xor(b.view(), ones), i);
        xor_bit(b.view(), ones, i);
        and_not_bit(a.view(), b.view(), i);
        all_ones_bit(w, i);
        if i >= w { bit_above(a.view(), w, i); }
    };
    eq_from_bits(bw_and(a.view(), bw_xor(b.view(), ones)), bw_and_not(a.view(), b.view()));
}

/// Logical right shift is rshi.
pub proof fn lemma_shr<W: Word>(a: W, k: nat, r: W)
    requires r.view() == a.view() / pow2(k)
    ensures r.view() == rshi(a.view(), k)
{
    rsh_div(a.view(), k);
    lemma_pow2(k);
    exp_eq_pow2(k);
}

/// The low bit of a word, tested by and with one, is the head bit.
pub proof fn lemma_low_bit<W: BitWord>(a: W, one: W)
    requires one.view() == 1
    ensures (a.and(one).view() == 1) == hd(a.view()).b(), a.and(one).view() <= 1
{
    W::lemma_and(a, one);
    let x = bw_and(a.view(), 1);
    assert(exp(0) == 1);
    assert forall|i: nat| #![auto] bit(x, i) == if i == 0 { hd(a.view()) } else { Bit::f() } by {
        and_bit(a.view(), 1, i);
        bit_exp(0, i);
    };
    if hd(a.view()).b() {
        assert forall|i: nat| #![auto] bit(x, i) == bit(1, i) by { bit_exp(0, i); };
        eq_from_bits(x, 1);
    } else {
        assert forall|i: nat| #![auto] bit(x, i) == bit(0, i) by { bit_zero(i); };
        eq_from_bits(x, 0);
    }
}

} // verus!

/// Per-width proofs of `BitWord`, by `bit_vector` on the native type.
macro_rules! impl_bitword {
    ($m:ident, $t:ty, $bits:expr) => {
        mod $m {
            use super::*;
            verus! {

            /// The spec bit of a word is its native bit.
            proof fn native_bit(n: $t, i: nat)
                requires i < $bits
                ensures bit(n as nat, i).b() == ((n >> (i as $t)) & 1 == 1)
                decreases i
            {
                if i == 0 {
                    assert(((n >> 0) & 1) == (n % 2)) by(bit_vector);
                } else {
                    let iu = i as $t;
                    assert((n >> 1) as nat == n as nat / 2) by(bit_vector);
                    native_bit(n >> 1, (i - 1) as nat);
                    assert(((n >> iu) & 1) == (((n >> 1) >> ((iu - 1) as $t)) & 1)) by(bit_vector)
                        requires iu < $bits, iu > 0;
                }
            }

            /// A word equals a nat with the same bits below the width and none above.
            proof fn eq_bits(x: $t, y: nat)
                requires
                    forall|i: nat| i < $bits ==> #[trigger] bit(x as nat, i) == bit(y, i),
                    forall|i: nat| i >= $bits ==> !(#[trigger] bit(y, i)).b(),
                ensures x as nat == y
            {
                lemma_fits(x);
                assert forall|i: nat| #![auto] bit(x as nat, i) == bit(y, i) by {
                    if i >= $bits {
                        bit_above(x as nat, $bits, i);
                    }
                };
                eq_from_bits(x as nat, y);
            }

            pub proof fn native_and(a: $t, b: $t)
                ensures (a & b) as nat == bw_and(a as nat, b as nat)
            {
                lemma_fits(a);
                assert forall|i: nat| i < $bits implies #[trigger] bit((a & b) as nat, i) == bit(bw_and(a as nat, b as nat), i) by {
                    and_bit(a as nat, b as nat, i);
                    native_bit(a, i); native_bit(b, i); native_bit(a & b, i);
                    let iu = i as $t;
                    assert(((a & b) >> iu) & 1 == if ((a >> iu) & 1 == 1) && ((b >> iu) & 1 == 1) { 1 as $t } else { 0 as $t })
                        by(bit_vector) requires iu < $bits;
                };
                assert forall|i: nat| i >= $bits implies !(#[trigger] bit(bw_and(a as nat, b as nat), i)).b() by {
                    and_bit(a as nat, b as nat, i);
                    bit_above(a as nat, $bits, i);
                };
                eq_bits(a & b, bw_and(a as nat, b as nat));
            }

            pub proof fn native_or(a: $t, b: $t)
                ensures (a | b) as nat == bw_or(a as nat, b as nat)
            {
                lemma_fits(a); lemma_fits(b);
                assert forall|i: nat| i < $bits implies #[trigger] bit((a | b) as nat, i) == bit(bw_or(a as nat, b as nat), i) by {
                    or_bit(a as nat, b as nat, i);
                    native_bit(a, i); native_bit(b, i); native_bit(a | b, i);
                    let iu = i as $t;
                    assert(((a | b) >> iu) & 1 == if ((a >> iu) & 1 == 1) || ((b >> iu) & 1 == 1) { 1 as $t } else { 0 as $t })
                        by(bit_vector) requires iu < $bits;
                };
                assert forall|i: nat| i >= $bits implies !(#[trigger] bit(bw_or(a as nat, b as nat), i)).b() by {
                    or_bit(a as nat, b as nat, i);
                    bit_above(a as nat, $bits, i);
                    bit_above(b as nat, $bits, i);
                };
                eq_bits(a | b, bw_or(a as nat, b as nat));
            }

            pub proof fn native_xor(a: $t, b: $t)
                ensures (a ^ b) as nat == bw_xor(a as nat, b as nat)
            {
                lemma_fits(a); lemma_fits(b);
                assert forall|i: nat| i < $bits implies #[trigger] bit((a ^ b) as nat, i) == bit(bw_xor(a as nat, b as nat), i) by {
                    xor_bit(a as nat, b as nat, i);
                    native_bit(a, i); native_bit(b, i); native_bit(a ^ b, i);
                    let iu = i as $t;
                    assert(((a ^ b) >> iu) & 1 == if ((a >> iu) & 1 == 1) != ((b >> iu) & 1 == 1) { 1 as $t } else { 0 as $t })
                        by(bit_vector) requires iu < $bits;
                };
                assert forall|i: nat| i >= $bits implies !(#[trigger] bit(bw_xor(a as nat, b as nat), i)).b() by {
                    xor_bit(a as nat, b as nat, i);
                    bit_above(a as nat, $bits, i);
                    bit_above(b as nat, $bits, i);
                };
                eq_bits(a ^ b, bw_xor(a as nat, b as nat));
            }

            /// Native left shift by one is lsh, chopped.
            proof fn native_lsh(a: $t)
                ensures (a << 1) as nat == chop(lsh(a as nat), $bits)
            {
                assert forall|i: nat| i < $bits implies #[trigger] bit((a << 1) as nat, i) == bit(chop(lsh(a as nat), $bits), i) by {
                    chop_bit(lsh(a as nat), $bits, i);
                    native_bit(a << 1, i);
                    bit_cons(a as nat, Bit::f(), i);
                    let iu = i as $t;
                    if i == 0 {
                        assert((((a << 1) >> iu) & 1) == 0) by(bit_vector) requires iu == 0;
                    } else {
                        native_bit(a, (i - 1) as nat);
                        assert((((a << 1) >> iu) & 1) == ((a >> ((iu - 1) as $t)) & 1)) by(bit_vector)
                            requires iu < $bits, iu > 0;
                    }
                };
                assert forall|i: nat| i >= $bits implies !(#[trigger] bit(chop(lsh(a as nat), $bits), i)).b() by {
                    chop_bit(lsh(a as nat), $bits, i);
                };
                eq_bits(a << 1, chop(lsh(a as nat), $bits));
            }

            /// Native left shift by k is lshi, chopped.
            pub proof fn native_lshi(a: $t, k: nat)
                requires k < $bits
                ensures (a << (k as $t)) as nat == chop(lshi(a as nat, k), $bits)
                decreases k
            {
                if k == 0 {
                    assert(a << 0 == a) by(bit_vector);
                    lemma_fits(a);
                } else {
                    let ku = k as $t;
                    let b = a << ((ku - 1) as $t);
                    native_lshi(a, (k - 1) as nat);
                    native_lsh(b);
                    chop_lsh(lshi(a as nat, (k - 1) as nat), $bits);
                    assert(a << ku == b << 1) by(bit_vector)
                        requires ku < $bits, ku > 0, b == a << ((ku - 1) as $t);
                }
            }
            }
        }

        verus! {
        impl BitWord for $t {
            proof fn lemma_and(a: Self, b: Self) { $m::native_and(a, b); }
            proof fn lemma_or(a: Self, b: Self) { $m::native_or(a, b); }
            proof fn lemma_xor(a: Self, b: Self) { $m::native_xor(a, b); }

            fn mul_wrap(self, o: Self) -> (r: Self) {
                proof {
                    exp_concrete($bits);
                    chop_is_mod(prod(self as nat, o as nat), $bits);
                }
                self.wrapping_mul(o)
            }

            fn shl_wrap(self, k: u32) -> (r: Self) {
                proof { $m::native_lshi(self, k as nat); }
                self << (k as $t)
            }
        }
        }
    };
}

impl_bitword!(bw8, u8, 8);
impl_bitword!(bw16, u16, 16);
impl_bitword!(bw32, u32, 32);
impl_bitword!(bw64, u64, 64);
impl_bitword!(bw128, u128, 128);
