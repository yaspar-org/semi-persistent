// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Natural numbers as infinite bitstrings.
//!
//! Key idea: treat nat as an infinite boolean string via hd (mod 2) / tl (div 2).
//! This eliminates representational differences caused by leading zeros.

use crate::bools::Bit;
use vstd::prelude::*;

verus! {

// ============================================================
// Core bitstring decomposition
// ============================================================

/// Lowest-order bit
pub open spec fn hd(n: nat) -> Bit { Bit::ctor_n(n % 2) }

/// All but the lowest-order bit (right shift by 1)
pub open spec fn tl(n: nat) -> nat { n / 2 }

/// Left-shift by 1, inserting bit b at position 0.
pub open spec fn cons(n: nat, b: Bit) -> nat { b.n() + 2 * n }

/// The i-th bit of n.
pub open spec fn bit(n: nat, i: nat) -> Bit
    decreases i
{
    if i == 0 { hd(n) } else { bit(tl(n), (i - 1) as nat) }
}

/// True iff n is zero
pub open spec fn is_zero(n: nat) -> bool { n == 0 }

// ============================================================
// Core lemmas: cons/hd/tl round-trip
// ============================================================

pub proof fn hd_tl(n: nat)
    ensures n == cons(tl(n), hd(n))
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 2);
}

pub proof fn hd_cons(n: nat, b: Bit)
    ensures hd(cons(n, b)) == b, tl(cons(n, b)) == n
{
    let c = cons(n, b);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c as int, 2);
}

// ============================================================
// Bit indexing lemmas
// ============================================================

pub proof fn bit_zero(i: nat)
    ensures bit(0, i) == Bit::f()
    decreases i
{
    if i > 0 { bit_zero((i - 1) as nat); }
}

pub proof fn bit_tl(n: nat, i: nat)
    ensures bit(tl(n), i) == bit(n, i + 1)
    decreases i
{
    if i > 0 { bit_tl(tl(n), (i - 1) as nat); }
}

pub proof fn bit_cons(n: nat, b: Bit, i: nat)
    ensures bit(cons(n, b), i) == if i == 0 { b } else { bit(n, (i - 1) as nat) }
    decreases i
{
    hd_cons(n, b);
    if i > 0 {
        // bit(cons(n,b), i) == bit(tl(cons(n,b)), i-1) == bit(n, i-1)
    }
}

/// Bitwise equality implies numeric equality.
pub proof fn eq_from_bits(a: nat, b: nat)
    requires forall|i: nat| #![auto] bit(a, i) == bit(b, i)
    ensures a == b
    decreases a + b
{
    if a == 0 && b == 0 {
    } else if a == 0 {
        bit_zero(0);
        assert(bit(b, 0) == Bit::f());
        assert(!hd(b).b());
        assert forall|i: nat| #![auto] bit(0 as nat, i) == bit(tl(b), i) by {
            bit_tl(b, i);
            bit_zero(i);
        };
        eq_from_bits(0, tl(b));
        hd_tl(b);
    } else if b == 0 {
        bit_zero(0);
        assert(!hd(a).b());
        assert forall|i: nat| #![auto] bit(0 as nat, i) == bit(tl(a), i) by {
            bit_tl(a, i);
            bit_zero(i);
        };
        eq_from_bits(0, tl(a));
        hd_tl(a);
    } else {
        assert(hd(a) == hd(b)) by {
            assert(bit(a, 0) == bit(b, 0));
            // bit(n, 0) == hd(n) by definition
        };
        assert forall|i: nat| #![auto] bit(tl(a), i) == bit(tl(b), i) by {
            bit_tl(a, i);
            bit_tl(b, i);
        };
        eq_from_bits(tl(a), tl(b));
        hd_tl(a);
        hd_tl(b);
    }
}

// ============================================================
// Bitwise binary map (the workhorse)
// ============================================================

/// Apply binary boolean function f to corresponding bits of a and b.
pub open spec fn mapd(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit) -> nat
    recommends f(Bit::f(), Bit::f()) == Bit::f()
    decreases a + b
{
    if a == 0 && b == 0 { 0 }
    else { cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b))) }
}

/// mapd produces correct bits.
/// This is THE key lemma — all bitwise op correctness flows from here.
pub proof fn mapd_bit(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit, i: nat)
    requires f(Bit::f(), Bit::f()) == Bit::f()
    ensures bit(mapd(a, b, f), i) == f(bit(a, i), bit(b, i))
    decreases i, a + b
{
    if a == 0 && b == 0 {
        bit_zero(i);
    } else if i == 0 {
        hd_cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b)));
    } else {
        hd_cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b)));
        mapd_bit(tl(a), tl(b), f, (i - 1) as nat);
    }
}

// ============================================================
// Named bitwise operations
// ============================================================

pub open spec fn bw_or(a: nat, b: nat) -> nat { mapd(a, b, |x: Bit, y: Bit| x.or(y)) }
pub open spec fn bw_xor(a: nat, b: nat) -> nat { mapd(a, b, |x: Bit, y: Bit| x.xor(y)) }
pub open spec fn bw_and(a: nat, b: nat) -> nat { mapd(a, b, |x: Bit, y: Bit| x.and(y)) }
pub open spec fn bw_and_not(a: nat, b: nat) -> nat { mapd(a, b, |x: Bit, y: Bit| x.and_not(y)) }

pub proof fn or_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_or(a, b), i) == bit(a, i).or(bit(b, i))
{ mapd_bit(a, b, |x: Bit, y: Bit| x.or(y), i); }

/// mapd decomposes through hd/tl.
/// This is the key helper for Tnum bitwise soundness proofs.
pub proof fn mapd_hd_tl(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit)
    requires f(Bit::f(), Bit::f()) == Bit::f()
    ensures
        hd(mapd(a, b, f)) == f(hd(a), hd(b)),
        tl(mapd(a, b, f)) == mapd(tl(a), tl(b), f),
{
    if a == 0 && b == 0 {
        // mapd(0, 0, f) == 0
        // hd(0) == F, f(F, F) == F ✓
        // tl(0) == 0, mapd(0, 0, f) == 0 ✓
        bit_zero(0);
    } else {
        hd_cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b)));
    }
}

pub proof fn xor_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_xor(a, b), i) == bit(a, i).xor(bit(b, i))
{ mapd_bit(a, b, |x: Bit, y: Bit| x.xor(y), i); }

pub proof fn and_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_and(a, b), i) == bit(a, i).and(bit(b, i))
{ mapd_bit(a, b, |x: Bit, y: Bit| x.and(y), i); }

pub proof fn and_not_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_and_not(a, b), i) == bit(a, i).and_not(bit(b, i))
{ mapd_bit(a, b, |x: Bit, y: Bit| x.and_not(y), i); }

// ============================================================
// Addition with carry
// ============================================================

pub open spec fn nat_add_carry(a: nat, b: nat, c: Bit) -> nat
    decreases a + b
{
    if a == 0 && b == 0 { c.n() }
    else {
        let (r, c1) = hd(a).full_add(hd(b), c);
        cons(nat_add_carry(tl(a), tl(b), c1), r)
    }
}

pub proof fn nat_add_carry_correct(a: nat, b: nat, c: Bit)
    ensures nat_add_carry(a, b, c) == a + b + c.n()
    decreases a + b
{
    if a == 0 && b == 0 {
    } else {
        let (r, c1) = hd(a).full_add(hd(b), c);
        hd(a).full_add_correct(hd(b), c);
        nat_add_carry_correct(tl(a), tl(b), c1);
        hd_tl(a);
        hd_tl(b);
        assert(a == hd(a).n() + 2 * tl(a));
        assert(b == hd(b).n() + 2 * tl(b));
        assert(hd(a).n() + hd(b).n() + c.n() == 2 * c1.n() + r.n());
        assert(nat_add_carry(tl(a), tl(b), c1) == tl(a) + tl(b) + c1.n());
        assert(cons(nat_add_carry(tl(a), tl(b), c1), r) == r.n() + 2 * (tl(a) + tl(b) + c1.n()));
    }
}

pub open spec fn nat_add(a: nat, b: nat) -> nat { nat_add_carry(a, b, Bit::f()) }

pub proof fn nat_add_correct(a: nat, b: nat)
    ensures nat_add(a, b) == a + b
{ nat_add_carry_correct(a, b, Bit::f()); }

/// Subtraction (defined only when b <= a, for Anum use)
pub open spec fn nat_sub(a: nat, b: nat) -> nat
    recommends b <= a
{ (a - b) as nat }

// ============================================================
// Disjointness
// ============================================================

pub open spec fn disj(a: nat, b: nat) -> bool { bw_and(a, b) == 0 }

pub proof fn disj_bits(a: nat, b: nat)
    ensures disj(a, b) <==> forall|i: nat| #![auto] !(bit(a, i).b() && bit(b, i).b())
{
    if disj(a, b) {
        assert forall|i: nat| #![auto] !(bit(a, i).b() && bit(b, i).b()) by {
            and_bit(a, b, i);
            bit_zero(i);
        };
    } else {
        if forall|i: nat| #![auto] !(bit(a, i).b() && bit(b, i).b()) {
            assert forall|i: nat| #![auto] bit(bw_and(a, b), i) == bit(0 as nat, i) by {
                and_bit(a, b, i);
                bit_zero(i);
            };
            eq_from_bits(bw_and(a, b), 0);
        }
    }
}

pub proof fn disj_zero(n: nat)
    ensures disj(0, n)
{
    assert forall|i: nat| #![auto] !(bit(0 as nat, i).b() && bit(n, i).b()) by {
        bit_zero(i);
    };
    disj_bits(0, n);
}

pub proof fn disj_cons(a: nat, x: Bit, b: nat, y: Bit)
    requires disj(a, b), !x.b() || !y.b()
    ensures disj(cons(a, x), cons(b, y))
{
    assert(disj(cons(a, x), cons(b, y))) by {
        assert forall|i: nat| #![auto] !(bit(cons(a, x), i).b() && bit(cons(b, y), i).b()) by {
            bit_cons(a, x, i);
            bit_cons(b, y, i);
            if i == 0 {
            } else {
                disj_bits(a, b);
            }
        };
        disj_bits(cons(a, x), cons(b, y));
    };
}

pub proof fn nat_add_or(a: nat, b: nat)
    requires disj(a, b)
    ensures nat_add(a, b) == bw_or(a, b)
    decreases a + b
{
    if !(a == 0 && b == 0) {
        // Need: tl's are disjoint
        // From disj(a,b) and mapd definition, tl(and(a,b)) == and(tl(a), tl(b))
        // Since and(a,b) == 0, and(tl(a), tl(b)) == 0
        // This follows from mapd's recursive structure
        assert(disj(tl(a), tl(b))) by {
            // mapd unfolds: and(a,b) = cons(and(tl(a),tl(b)), hd(a).and(hd(b)))
            // if and(a,b) == 0, then tl(and(a,b)) == 0, i.e. and(tl(a),tl(b)) == 0
            assert forall|i: nat| #![auto] !(bit(tl(a), i).b() && bit(tl(b), i).b()) by {
                disj_bits(a, b);
                bit_tl(a, i);
                bit_tl(b, i);
            };
            disj_bits(tl(a), tl(b));
        };
        nat_add_or(tl(a), tl(b));
    }
}

// ============================================================
// Shifts
// ============================================================

pub open spec fn lsh(n: nat) -> nat { cons(n, Bit::f()) }
pub open spec fn rsh(n: nat) -> nat { tl(n) }

pub open spec fn lshi(n: nat, i: nat) -> nat
    decreases i
{ if i == 0 { n } else { lsh(lshi(n, (i - 1) as nat)) } }

pub open spec fn rshi(n: nat, i: nat) -> nat
    decreases i
{ if i == 0 { n } else { rshi(rsh(n), (i - 1) as nat) } }

// ============================================================
// Exponentiation: 2^i
// ============================================================

pub open spec fn exp(i: nat) -> nat
    decreases i
{ lshi(1, i) }

pub proof fn exp_pos(i: nat)
    ensures exp(i) >= 1
    decreases i
{
    if i > 0 { exp_pos((i - 1) as nat); }
}

/// Bridge: exp(W) == 2^W for the specific widths we use
pub proof fn exp_8()  ensures exp(8)  == 256   { reveal_with_fuel(lshi, 9);  }
pub proof fn exp_16() ensures exp(16) == 65536  { reveal_with_fuel(lshi, 17); }
pub proof fn exp_32() ensures exp(32) == 0x1_0000_0000 { reveal_with_fuel(lshi, 33); }
pub proof fn exp_64() ensures exp(64) == 0x1_0000_0000_0000_0000 {
    exp_32();
    assert(lshi(1nat, 32nat) == exp(32nat)) by { reveal_with_fuel(lshi, 33); }
    lsh_exp(exp(32), 32);
    assert(prod(exp(32), exp(32)) == 0x1_0000_0000_0000_0000nat);
    assert(lshi(1nat, 64nat) == lshi(lshi(1nat, 32nat), 32nat)) by { reveal_with_fuel(lshi, 33); }
}
#[verifier::rlimit(10000)]
pub proof fn exp_128() ensures exp(128) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000 {
    exp_64();
    assert(lshi(1nat, 64nat) == exp(64nat)) by { reveal_with_fuel(lshi, 65); }
    lsh_exp(exp(64), 64);
    assert(prod(exp(64), exp(64)) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat);
    assert(lshi(1nat, 128nat) == lshi(lshi(1nat, 64nat), 64nat)) by { reveal_with_fuel(lshi, 65); }
}

/// Dispatch: exp(W) == 2^W for W in {8, 16, 32, 64, 128}
pub proof fn exp_concrete(w: nat)
    requires w == 8 || w == 16 || w == 32 || w == 64 || w == 128
    ensures exp(w) == if w == 8 { 256nat }
                     else if w == 16 { 65536nat }
                     else if w == 32 { 0x1_0000_0000nat }
                     else if w == 64 { 0x1_0000_0000_0000_0000nat }
                     else { 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat }
{
    if w == 8 { exp_8(); }
    else if w == 16 { exp_16(); }
    else if w == 32 { exp_32(); }
    else if w == 64 { exp_64(); }
    else { exp_128(); }
}
pub proof fn exp_eq_pow2(i: nat)
    ensures exp(i) as int == vstd::arithmetic::power::pow(2int, i)
    decreases i
{
    reveal(vstd::arithmetic::power::pow);
    if i > 0 {
        exp_eq_pow2((i - 1) as nat);
        lsh_is_times2(exp((i - 1) as nat));
    }
}

// ============================================================
// Ones: i-bit number of all 1's (== 2^i - 1)
// ============================================================

/// Recursive version (with bit-level ensures)
pub open spec fn all_ones_r(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { cons(all_ones_r((i - 1) as nat), Bit::t()) }
}

pub proof fn all_ones_r_bit(i: nat, j: nat)
    ensures bit(all_ones_r(i), j).b() <==> j < i
    decreases i
{
    if i == 0 {
        bit_zero(j);
    } else {
        bit_cons(all_ones_r((i - 1) as nat), Bit::t(), j);
        if j > 0 {
            all_ones_r_bit((i - 1) as nat, (j - 1) as nat);
        }
    }
}

/// Nonrecursive version: all_ones(i) == exp(i) - 1
pub open spec fn all_ones(i: nat) -> nat {
    (exp(i) - 1) as nat
}

// ============================================================
// Multiplication
// ============================================================

pub open spec fn prod(a: nat, b: nat) -> nat { a * b }

pub open spec fn nat_mul_bit(a: nat, b: Bit) -> nat {
    if b.b() { a } else { 0 }
}

/// Shift-add multiplication with accumulator.
pub open spec fn nat_mul_acc(a: nat, u: nat, acc: nat) -> nat
    decreases a
{
    if a == 0 { acc }
    else { nat_mul_acc(tl(a), lsh(u), nat_add(acc, nat_mul_bit(u, hd(a)))) }
}

// ============================================================
// Chop: discard all but the i low-order bits
// ============================================================

/// Recursive chop.
pub open spec fn chop(n: nat, i: nat) -> nat
    decreases i
{
    if i == 0 { 0 }
    else { cons(chop(tl(n), (i - 1) as nat), hd(n)) }
}

pub proof fn chop_bit(n: nat, i: nat, j: nat)
    ensures bit(chop(n, i), j) == if j < i { bit(n, j) } else { Bit::f() }
    decreases i, j
{
    if i == 0 {
        bit_zero(j);
    } else {
        let c = chop(tl(n), (i - 1) as nat);
        if j == 0 {
            hd_cons(c, hd(n));
        } else {
            hd_cons(c, hd(n));
            chop_bit(tl(n), (i - 1) as nat, (j - 1) as nat);
            bit_tl(n, (j - 1) as nat);
        }
    }
}

/// n fits in i bits
pub open spec fn fits(n: nat, i: nat) -> bool { n == chop(n, i) }

pub proof fn chop_idem(n: nat, i: nat)
    ensures fits(chop(n, i), i)
{
    assert forall|j: nat| #![auto] bit(chop(chop(n, i), i), j) == bit(chop(n, i), j) by {
        chop_bit(chop(n, i), i, j);
        chop_bit(n, i, j);
    };
    eq_from_bits(chop(chop(n, i), i), chop(n, i));
}

/// Chop preserves disjointness.
pub proof fn chop_disj(a: nat, b: nat, i: nat)
    requires disj(a, b)
    ensures disj(chop(a, i), chop(b, i))
{
    disj_bits(a, b);
    assert forall|j: nat| #![auto] !(bit(chop(a, i), j).b() && bit(chop(b, i), j).b()) by {
        chop_bit(a, i, j);
        chop_bit(b, i, j);
    };
    disj_bits(chop(a, i), chop(b, i));
}

/// Chop distributes through mapd.
pub proof fn chop_mapd(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit, i: nat)
    requires f(Bit::f(), Bit::f()) == Bit::f()
    ensures chop(mapd(a, b, f), i) == mapd(chop(a, i), chop(b, i), f)
{
    assert forall|j: nat| #![auto] bit(chop(mapd(a, b, f), i), j) == bit(mapd(chop(a, i), chop(b, i), f), j) by {
        chop_bit(mapd(a, b, f), i, j);
        mapd_bit(a, b, f, j);
        mapd_bit(chop(a, i), chop(b, i), f, j);
        chop_bit(a, i, j);
        chop_bit(b, i, j);
    };
    eq_from_bits(chop(mapd(a, b, f), i), mapd(chop(a, i), chop(b, i), f));
}

#[verifier::spinoff_prover]
pub proof fn chop_bw_xor(a: nat, b: nat, w: nat)
    ensures chop(bw_xor(a, b), w) == bw_xor(chop(a, w), chop(b, w))
{
    assert forall|j: nat| #![auto] bit(chop(bw_xor(a, b), w), j) == bit(bw_xor(chop(a, w), chop(b, w)), j) by {
        chop_bit(bw_xor(a, b), w, j); xor_bit(a, b, j);
        xor_bit(chop(a, w), chop(b, w), j); chop_bit(a, w, j); chop_bit(b, w, j);
    };
    eq_from_bits(chop(bw_xor(a, b), w), bw_xor(chop(a, w), chop(b, w)));
}

#[verifier::spinoff_prover]
pub proof fn chop_bw_or(a: nat, b: nat, w: nat)
    ensures chop(bw_or(a, b), w) == bw_or(chop(a, w), chop(b, w))
{
    assert forall|j: nat| #![auto] bit(chop(bw_or(a, b), w), j) == bit(bw_or(chop(a, w), chop(b, w)), j) by {
        chop_bit(bw_or(a, b), w, j); or_bit(a, b, j);
        or_bit(chop(a, w), chop(b, w), j); chop_bit(a, w, j); chop_bit(b, w, j);
    };
    eq_from_bits(chop(bw_or(a, b), w), bw_or(chop(a, w), chop(b, w)));
}

#[verifier::spinoff_prover]
pub proof fn chop_bw_and_not(a: nat, b: nat, w: nat)
    ensures chop(bw_and_not(a, b), w) == bw_and_not(chop(a, w), chop(b, w))
{
    assert forall|j: nat| #![auto] bit(chop(bw_and_not(a, b), w), j) == bit(bw_and_not(chop(a, w), chop(b, w)), j) by {
        chop_bit(bw_and_not(a, b), w, j); and_not_bit(a, b, j);
        and_not_bit(chop(a, w), chop(b, w), j); chop_bit(a, w, j); chop_bit(b, w, j);
    };
    eq_from_bits(chop(bw_and_not(a, b), w), bw_and_not(chop(a, w), chop(b, w)));
}

/// Chop distributes through plus.
pub proof fn chop_nat_add(a: nat, b: nat, i: nat)
    ensures chop(nat_add(a, b), i) == chop(nat_add(chop(a, i), chop(b, i)), i)
{
    nat_add_correct(a, b);
    nat_add_correct(chop(a, i), chop(b, i));
    chop_is_mod(a, i);
    chop_is_mod(b, i);
    chop_is_mod(nat_add(a, b), i);
    chop_is_mod(nat_add(chop(a, i), chop(b, i)), i);
    exp_pos(i);
    let d = exp(i) as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b as int, d);
    let ra = (a as int) % d;
    let rb = (b as int) % d;
    let qa = (a as int) / d;
    let qb = (b as int) / d;
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, qa, qb);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ra + rb, d);
    let q2 = (ra + rb) / d;
    let r2 = (ra + rb) % d;
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, qa + qb, q2);
    mod_unique((a + b) as int, d, qa + qb + q2, r2);
}

proof fn mod_unique(n: int, d: int, q: int, r: int)
    requires d > 0, 0 <= r, r < d, n == q * d + r
    ensures n % d == r
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n, d, q, r);
}

/// Chop distributes through lsh.
pub proof fn chop_lsh(n: nat, i: nat)
    ensures chop(lsh(n), i) == chop(lsh(chop(n, i)), i)
{
    assert forall|j: nat| #![auto] bit(chop(lsh(n), i), j) == bit(chop(lsh(chop(n, i)), i), j) by {
        chop_bit(lsh(n), i, j);
        chop_bit(lsh(chop(n, i)), i, j);
        bit_cons(n, Bit::f(), j);
        bit_cons(chop(n, i), Bit::f(), j);
        if j < i && j > 0 {
            chop_bit(n, i, (j - 1) as nat);
        }
    };
    eq_from_bits(chop(lsh(n), i), chop(lsh(chop(n, i)), i));
}

// ============================================================
// len: minimum bits to represent n
// ============================================================

pub open spec fn len(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { 1 + len(tl(n)) }
}

pub open spec fn chopped(n: nat, i: nat) -> bool { len(n) <= i }

// ============================================================
// Ordering predicates
// ============================================================

pub open spec fn le(a: nat, b: nat) -> bool { a <= b }
pub open spec fn lt(a: nat, b: nat) -> bool { a < b }

// ============================================================
// Shift lemmas
// ============================================================

pub proof fn lsh_plus(n: nat, i: nat, j: nat)
    ensures lshi(lshi(n, i), j) == lshi(n, i + j)
    decreases j
{
    if j > 0 { lsh_plus(n, i, (j - 1) as nat); }
}

pub proof fn rsh_plus(n: nat, i: nat, j: nat)
    ensures rshi(rshi(n, i), j) == rshi(n, i + j)
    decreases i
{
    if i > 0 { rsh_plus(rsh(n), (i - 1) as nat, j); }
}

pub proof fn lsh_is_times2(n: nat)
    ensures lsh(n) == 2 * n
{}

pub proof fn lsh_exp(n: nat, i: nat)
    ensures lshi(n, i) == prod(n, exp(i))
    decreases i
{
    if i == 0 {
        // lshi(n, 0) == n, exp(0) == lshi(1, 0) == 1, prod(n, 1) == n * 1 == n
        assert(exp(0) == 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(n as int);
    } else {
        lsh_exp(n, (i - 1) as nat);
        let e = exp((i - 1) as nat);
        lsh_is_times2(n * e);
        lsh_is_times2(e);
        // 2 * (n * e) == n * (2 * e)
        vstd::arithmetic::mul::lemma_mul_is_associative(n as int, 2 as int, e as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, 2 as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(2 as int, n as int, e as int);
    }
}

/// (x/y)/z == x/(y*z)
proof fn div_div(x: int, y: int, z: int)
    requires y > 0, z > 0
    ensures (x / y) / z == x / (y * z)
{
    let dy = x / y;
    let ry = x % y;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, y);
    // x == dy * y + ry, 0 <= ry < y

    let dz = dy / z;
    let rz = dy % z;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(dy, z);
    // dy == dz * z + rz, 0 <= rz < z

    let yz = z * y;
    let ryz = rz * y + ry;

    // Show: x == dz * yz + ryz and 0 <= ryz < yz
    // Then by uniqueness: x / yz == dz == (x/y)/z

    // x == dy * y + ry == (dz * z + rz) * y + ry == dz * z * y + rz * y + ry == dz * yz + ryz
    vstd::arithmetic::mul::lemma_mul_is_associative(dz as int, z, y);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(y, dz * z, rz);
    assert(x == dz * yz + ryz);

    // 0 <= ryz: rz >= 0 and y > 0 and ry >= 0
    assert(ryz >= 0) by {
        vstd::arithmetic::mul::lemma_mul_nonnegative(rz, y);
    };

    // ryz < yz: ryz == rz * y + ry < (rz+1)*y <= z*y == yz
    assert(ryz < yz) by {
        assert(rz + 1 <= z);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(y, rz, 1 as int);
        assert(ryz < (rz + 1) * y);
        vstd::arithmetic::mul::lemma_mul_inequality(rz + 1, z, y);
    };

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, yz, dz, ryz);
    vstd::arithmetic::mul::lemma_mul_is_commutative(y, z);
}

/// (x*y) % d == ((x%d) * (y%d)) % d
proof fn times_mod(x: int, y: int, d: int)
    requires d > 0
    ensures (x * y) % d == ((x % d) * (y % d)) % d
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, d);
    let dx = x / d;
    let rx = x % d;
    let dy = y / d;
    let ry = y % d;
    // x*y == (dx*d + rx)*(dy*d + ry)
    // We show x*y == d*k + rx*ry for some k, then use lemma_mod_multiples_vanish

    // First establish: x*y == d*(dx*dy*d + dx*ry + rx*dy) + rx*ry
    // by expanding (dx*d + rx)*(dy*d + ry) step by step
    // Prove x*y == d*k + rx*ry where k = dx*dy*d + dx*ry + rx*dy
    // by expanding (dx*d + rx)*(dy*d + ry) step by step

    // x == d*dx + rx, y == d*dy + ry (note: vstd gives d*(x/d) + x%d)
    assert(x == d * dx + rx);
    assert(y == d * dy + ry);
    vstd::arithmetic::mul::lemma_mul_is_commutative(d, dx);
    vstd::arithmetic::mul::lemma_mul_is_commutative(d, dy);
    assert(x == dx * d + rx);
    assert(y == dy * d + ry);

    // (dx*d + rx) * (dy*d + ry) = dx*d*(dy*d+ry) + rx*(dy*d+ry)
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(dy * d + ry, dx * d, rx);

    // dx*d*(dy*d+ry) = dx*d*(dy*d) + dx*d*ry
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(dx * d, dy * d, ry);

    // rx*(dy*d+ry) = rx*(dy*d) + rx*ry
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(rx, dy * d, ry);

    assert(x * y == dx * d * (dy * d) + dx * d * ry + rx * (dy * d) + rx * ry);

    // Now factor d out of the first three terms:
    // dx*d*(dy*d) = d*dx*(dy*d) = d*(dx*(dy*d)) = d*(dx*dy*d)
    vstd::arithmetic::mul::lemma_mul_is_commutative(dx, d);
    vstd::arithmetic::mul::lemma_mul_is_associative(d, dx, dy * d);
    vstd::arithmetic::mul::lemma_mul_is_associative(dx, dy, d);
    assert(dx * d * (dy * d) == d * (dx * dy * d));

    // dx*d*ry = d*dx*ry = d*(dx*ry)
    vstd::arithmetic::mul::lemma_mul_is_associative(d, dx, ry);
    assert(dx * d * ry == d * (dx * ry));

    // rx*(dy*d) = (rx*dy)*d = d*(rx*dy)
    vstd::arithmetic::mul::lemma_mul_is_associative(rx, dy, d);
    vstd::arithmetic::mul::lemma_mul_is_commutative(rx * dy, d);
    assert(rx * (dy * d) == d * (rx * dy));

    // Combine: d*(dx*dy*d) + d*(dx*ry) + d*(rx*dy) = d*(dx*dy*d + dx*ry + rx*dy)
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, dx * dy * d, dx * ry);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, dx * dy * d + dx * ry, rx * dy);

    let k = dx * dy * d + dx * ry + rx * dy;
    assert(x * y == d * k + rx * ry);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(k, rx * ry, d);
}

pub proof fn rsh_div(n: nat, i: nat)
    ensures rshi(n, i) == n / exp(i)
    decreases i
{
    if i == 0 {
        assert(exp(0) == 1nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 1);
    } else {
        rsh_div(rsh(n), (i - 1) as nat);
        // IH: rshi(n/2, i-1) == (n/2) / exp(i-1)
        // Need: (n/2) / exp(i-1) == n / (2 * exp(i-1)) == n / exp(i)
        exp_pos((i - 1) as nat);
        lsh_is_times2(exp((i - 1) as nat));
        div_div(n as int, 2, exp((i - 1) as nat) as int);
    }
}

// ============================================================
// chop == mod exp(i) linking
// ============================================================

#[verifier::rlimit(100)]
pub proof fn chop_is_mod(n: nat, i: nat)
    ensures chop(n, i) == n % exp(i)
    decreases i
{
    exp_pos(i);
    if i == 0 {
    } else {
        chop_is_mod(tl(n), (i - 1) as nat);
        hd_tl(n);
        exp_pos((i - 1) as nat);
        let e = exp((i - 1) as nat);
        let h: nat = hd(n).n();
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(tl(n) as int, e as int);
        let q = (tl(n) / e) as nat;
        let r = (tl(n) % e) as nat;
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(2 as int, (q * e) as int, r as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(2 as int, q as int, e as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(2 as int, q as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(q as int, 2 as int, e as int);
        let d = (2 * e) as int;
        assert(n as int == (q as int) * d + ((h + 2 * r) as int));
        assert(h + 2 * r < 2 * e) by {
            assert(h <= 1);
            assert(r < e);
            vstd::arithmetic::mul::lemma_mul_inequality(r as int, (e - 1) as int, 2);
        };
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, d);
        assert(n % (2 * e) == h + 2 * r) by {
            let nd = (n as int) / d;
            let nr = (n as int) % d;
            assert((nd - q as int) * d == (h + 2 * r) as int - nr) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub(d, nd, q as int);
            };
            if nd != q as int {
                if nd > q as int {
                    vstd::arithmetic::mul::lemma_mul_inequality(1, nd - q as int, d);
                } else {
                    vstd::arithmetic::mul::lemma_mul_inequality(1, q as int - nd, d);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_sub(d, q as int, nd);
                }
            }
        };
    }
}

// ============================================================
// chop_times: chop distributes through prod
// ============================================================

pub proof fn chop_nat_mul(a: nat, b: nat, i: nat)
    ensures chop(prod(chop(a, i), chop(b, i)), i) == chop(prod(a, b), i)
{
    chop_is_mod(a, i);
    chop_is_mod(b, i);
    chop_is_mod(prod(a, b), i);
    chop_is_mod(prod(chop(a, i), chop(b, i)), i);
    exp_pos(i);
    times_mod(a as int, b as int, exp(i) as int);
}

// ============================================================
// Negation
// ============================================================

/// Nonrecursive i-bit negation: flip bits and add 1, then chop.
pub open spec fn neg1(n: nat, i: nat, b: Bit) -> nat {
    chop(nat_add_carry(bw_xor(n, all_ones(i)), 0, b.not()), i)
}

/// Final nonrecursive negation.
pub open spec fn neg(n: nat, i: nat) -> nat {
    neg1(n, i, Bit::f())
}

/// Chopped subtraction: a - b mod 2^i.
pub open spec fn c_minus(a: nat, b: nat, i: nat) -> nat {
    chop(nat_add(a, neg(b, i)), i)
}

// ============================================================
// Recursive multiplication
// ============================================================

pub open spec fn nat_mul_rec(a: nat, u: nat) -> nat
    decreases a
{
    if a == 0 { 0 }
    else { nat_add(nat_mul_rec(tl(a), lsh(u)), nat_mul_bit(u, hd(a))) }
}

// ============================================================
// Division: concrete long division spec
// ============================================================

/// Concrete long division by iterated subtraction.
/// Processes bits from position i-1 down to 0.
/// Returns (quotient, remainder) such that n == q * d + r and r < d,
/// for the i low-order bits of n.
pub open spec fn div1(n: nat, d: nat, q: nat, r: nat, i: nat) -> (nat, nat)
    recommends d > 0
    decreases i
{
    if i == 0 { (q, r) }
    else {
        let i1 = (i - 1) as nat;
        let r1 = nat_add(lsh(r), bit(n, i1).n());
        if r1 >= d {
            div1(n, d, bw_or(q, exp(i1)), (r1 - d) as nat, i1)
        } else {
            div1(n, d, q, r1, i1)
        }
    }
}

/// Two's complement negation: 2^w - d (for d > 0, d < 2^w).
pub open spec fn twos_comp(d: nat, w: nat) -> nat
    recommends d > 0
{
    (exp(w) - d) as nat
}

/// Bounded subtraction via addition of two's complement.
/// sub_bv(a, d, w) = chop(a + (2^w - d), w) = (a - d) mod 2^w.
pub open spec fn sub_bv(a: nat, d: nat, w: nat) -> nat
    recommends d > 0
{
    chop(nat_add(a, twos_comp(d, w)), w)
}

// ============================================================
// Finite-width operations (model machine arithmetic)
// ============================================================

pub open spec fn c_nat_add(a: nat, b: nat, i: nat) -> nat { chop(nat_add(a, b), i) }
pub open spec fn c_prod(a: nat, b: nat, i: nat) -> nat { chop(prod(a, b), i) }

pub open spec fn c_map(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit, i: nat) -> nat
    recommends f(Bit::f(), Bit::f()) == Bit::f()
{ chop(mapd(a, b, f), i) }

pub open spec fn c_xor(a: nat, b: nat, i: nat) -> nat { c_map(a, b, |x: Bit, y: Bit| x.xor(y), i) }
pub open spec fn c_or(a: nat, b: nat, i: nat) -> nat { c_map(a, b, |x: Bit, y: Bit| x.or(y), i) }
pub open spec fn c_and(a: nat, b: nat, i: nat) -> nat { c_map(a, b, |x: Bit, y: Bit| x.and(y), i) }
pub open spec fn c_and_not(a: nat, b: nat, i: nat) -> nat { c_map(a, b, |x: Bit, y: Bit| x.and_not(y), i) }
pub open spec fn c_lsh(n: nat, i: nat) -> nat { chop(lsh(n), i) }
pub open spec fn c_rsh(n: nat, i: nat) -> nat { chop(rsh(n), i) }

/// chop(n + exp(w), w) == chop(n, w): adding 2^w doesn't change the low w bits.
pub proof fn chop_nat_add_pow2(n: nat, w: nat)
    ensures chop(nat_add(n, exp(w)), w) == chop(n, w)
{
    nat_add_carry_correct(n, exp(w), Bit::f());
    chop_is_mod(nat_add(n, exp(w)), w);
    chop_is_mod(n, w);
    exp_pos(w);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, n as int, exp(w) as int);
}

/// chop(n, w) == n when n < exp(w).
pub proof fn chop_id(n: nat, w: nat)
    requires n < exp(w)
    ensures chop(n, w) == n
{
    chop_is_mod(n, w);
    exp_pos(w);
    vstd::arithmetic::div_mod::lemma_small_mod(n as nat, exp(w) as nat);
}

pub proof fn bit_exp(i: nat, j: nat)
    ensures bit(exp(i), j) == (if i == j { Bit::t() } else { Bit::f() })
    decreases i + j
{
    exp_pos(i);
    if i == 0 {
        if j == 0 {} else { bit_zero((j - 1) as nat); }
    } else {
        exp_pos((i - 1) as nat);
        hd_cons(exp((i - 1) as nat), Bit::f());
        if j == 0 {} else { bit_exp((i - 1) as nat, (j - 1) as nat); }
    }
}

/// xor(y, all_ones(w)) + 1 == exp(w) - y for y < exp(w).
/// Flipping all w bits and adding 1 gives the two's complement.
pub proof fn xor_ones_complement(y: nat, w: nat)
    requires y < exp(w)
    ensures bw_xor(y, all_ones(w)) + 1 == exp(w) - y
    decreases w
{
    exp_pos(w);
    if w == 0 {
    } else {
        // all_ones(w) = 2 * all_ones(w-1) + 1
        // xor(y, all_ones(w)) = cons(xor(tl(y), all_ones(w-1)), hd(y).xor(T))
        // = cons(xor(tl(y), all_ones(w-1)), hd(y).not())
        mapd_hd_tl(y, all_ones(w), |a: Bit, b: Bit| a.xor(b));
        // hd(all_ones(w)) = T, tl(all_ones(w)) = all_ones(w-1)
        exp_pos((w - 1) as nat);
        hd_cons(all_ones((w - 1) as nat), Bit::t());
        // IH: xor(tl(y), all_ones(w-1)) + 1 == exp(w-1) - tl(y)
        xor_ones_complement(tl(y), (w - 1) as nat);
        hd_tl(y);
        // xor(y, all_ones(w)) = 2 * xor(tl(y), all_ones(w-1)) + (1 - hd(y))
        // xor(y, all_ones(w)) + 1 = 2 * xor(tl(y), all_ones(w-1)) + (1 - hd(y)) + 1
        //                      = 2 * xor(tl(y), all_ones(w-1)) + 2 - hd(y)
        //                      = 2 * (xor(tl(y), all_ones(w-1)) + 1) - hd(y)
        //                      = 2 * (exp(w-1) - tl(y)) - hd(y)
        //                      = 2*exp(w-1) - 2*tl(y) - hd(y)
        //                      = exp(w) - (2*tl(y) + hd(y))
        //                      = exp(w) - y
    }
}

/// all_ones(len(n)) >= n: the all-ones mask of bit-length n covers n.
pub proof fn all_ones_covers(n: nat)
    ensures n <= all_ones(len(n))
{
    len_bound(n);
    exp_pos(len(n));
    // n < exp(len(n)), all_ones(len(n)) = exp(len(n)) - 1
    // so n <= exp(len(n)) - 1 = all_ones(len(n))
}

/// Tn(0, all_ones(n)).has(k) for k < exp(n): any value fitting in n bits
/// is a member of the all-uncertain n-bit Tnum.
pub proof fn all_ones_has(k: nat, n: nat)
    requires k < exp(n)
    ensures bw_and_not(k, all_ones(n)) == 0
    decreases n
{
    exp_pos(n);
    if n == 0 {
    } else {
        all_ones_has(tl(k), (n - 1) as nat);
        hd_cons(all_ones((n - 1) as nat), Bit::t());
        mapd_hd_tl(k, all_ones(n), |x: Bit, y: Bit| x.and_not(y));
    }
}

/// len(n) is the bit-length: n < exp(len(n)).
pub proof fn len_bound(n: nat)
    ensures n < exp(len(n))
    decreases n
{
    if n > 0 {
        len_bound(tl(n));
        exp_pos(len(tl(n)));
    }
}

} // verus!
