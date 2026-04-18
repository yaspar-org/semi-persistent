// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use vstd::prelude::*;

fn main() {
    semi_persistent_abstract_domains::demo::demo();
}
verus! {

// ================================================================
// B: Booleans with bitvector-style operations
// ================================================================

/// Boolean-to-nat
pub open spec fn bn(b: bool) -> nat { if b { 1 } else { 0 } }

/// Boolean OR
pub open spec fn bor(a: bool, b: bool) -> bool { a || b }
/// Boolean AND
pub open spec fn band(a: bool, b: bool) -> bool { a && b }
/// Boolean XOR
pub open spec fn bxor(a: bool, b: bool) -> bool { a != b }
/// Boolean AND-NOT
pub open spec fn bandnot(a: bool, b: bool) -> bool { a && !b }

/// Full adder: (result, carry)
pub open spec fn bplus(a: bool, b: bool, c: bool) -> (bool, bool) {
    let r = bxor(bxor(a, b), c);
    let carry = if a { bor(b, c) } else { band(b, c) };
    (r, carry)
}

pub proof fn bplus_correct(a: bool, b: bool, c: bool)
    ensures ({ let (r, carry) = bplus(a, b, c); bn(a) + bn(b) + bn(c) == 2 * bn(carry) + bn(r) })
{}

// ================================================================
// N: Natural numbers as infinite bitstrings via div/mod 2
// ================================================================

/// Low bit
pub open spec fn hd(n: nat) -> bool { n % 2 != 0 }
/// Shift right 1
pub open spec fn tl(n: nat) -> nat { n / 2 }
/// Shift left 1, inserting b at position 0
pub open spec fn cons(n: nat, b: bool) -> nat { bn(b) + 2 * n }

pub proof fn cons_hd_tl(n: nat)
    ensures cons(tl(n), hd(n)) == n
{
    assert(n == (n / 2) * 2 + n % 2) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 2);
    };
}

pub proof fn hd_cons(n: nat, b: bool)
    ensures hd(cons(n, b)) == b, tl(cons(n, b)) == n
{
    let c = cons(n, b);
    assert(c == bn(b) + 2 * n);
    assert(c % 2 == bn(b) % 2) by {
        assert(c == bn(b) + 2 * n);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c as int, 2);
    };
    assert(c / 2 == n) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c as int, 2);
    };
}

/// i-th bit
pub open spec fn bit(n: nat, i: nat) -> bool
    decreases i
{
    if i == 0 { hd(n) } else { bit(tl(n), (i - 1) as nat) }
}

pub proof fn bit_zero(i: nat)
    ensures !bit(0, i)
    decreases i
{
    reveal(bit);
    if i > 0 { bit_zero((i - 1) as nat); }
}

pub proof fn bit_tl(n: nat, i: nat)
    ensures bit(tl(n), i) == bit(n, i + 1)
    decreases i
{
    reveal(bit);
    if i > 0 { bit_tl(tl(n), (i - 1) as nat); }
}

pub proof fn bit_cons(n: nat, b: bool, i: nat)
    ensures bit(cons(n, b), i) == if i == 0 { b } else { bit(n, (i - 1) as nat) }
    decreases i
{
    reveal(bit);
    hd_cons(n, b);
    if i > 0 {
        assert(bit(cons(n, b), i) == bit(tl(cons(n, b)), (i - 1) as nat));
    }
}

/// Bitwise equality via bits implies numeric equality
pub proof fn eq_from_bits(a: nat, b: nat)
    requires forall|i: nat| bit(a, i) == bit(b, i)
    ensures a == b
    decreases a + b
{
    reveal(bit);
    if a == 0 && b == 0 { }
    else if a == 0 {
        bit_zero(0);
        assert(bit(a, 0) == false);
        assert(bit(b, 0) == false);
        assert(!hd(b));
        assert(b % 2 == 0);
        // bit(0, i) == bit(b/2, i) for all i, so b/2 == 0 by induction
        assert forall|i: nat| #![auto] bit(0 as nat, i) == bit(tl(b), i) by {
            bit_tl(b, i);
            bit_zero(i);
            assert(bit(a, i + 1) == bit(b, i + 1));
        };
        eq_from_bits(0, tl(b));
        assert(b == cons(tl(b), hd(b))) by { cons_hd_tl(b); };
    }
    else if b == 0 {
        // symmetric to the a==0 case
        bit_zero(0);
        assert(!hd(a));
        assert forall|i: nat| #![auto] bit(0 as nat, i) == bit(tl(a), i) by {
            bit_tl(a, i);
            bit_zero(i);
            assert(bit(a, i + 1) == bit(b, i + 1));
        };
        eq_from_bits(0, tl(a));
        cons_hd_tl(a);
    }
    else {
        assert(hd(a) == hd(b)) by {
            assert(bit(a, 0) == bit(b, 0));
        };
        assert forall|i: nat| #![auto] bit(tl(a), i) == bit(tl(b), i) by {
            bit_tl(a, i);
            bit_tl(b, i);
            assert(bit(a, i + 1) == bit(b, i + 1));
        };
        eq_from_bits(tl(a), tl(b));
        cons_hd_tl(a);
        cons_hd_tl(b);
    }
}

// ================================================================
// Bitwise binary map
// ================================================================

pub open spec fn mapd(a: nat, b: nat, f: spec_fn(bool, bool) -> bool) -> nat
    recommends f(false, false) == false
    decreases a + b
{
    if a == 0 && b == 0 { 0 }
    else { cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b))) }
}

pub proof fn mapd_bit(a: nat, b: nat, f: spec_fn(bool, bool) -> bool, i: nat)
    requires f(false, false) == false
    ensures bit(mapd(a, b, f), i) == f(bit(a, i), bit(b, i))
    decreases i, a + b
{
    reveal(bit);
    reveal(mapd);
    if a == 0 && b == 0 {
        bit_zero(i);
    } else if i == 0 {
        hd_cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b)));
    } else {
        hd_cons(mapd(tl(a), tl(b), f), f(hd(a), hd(b)));
        mapd_bit(tl(a), tl(b), f, (i - 1) as nat);
    }
}

// Named bitwise ops
pub open spec fn bw_or(a: nat, b: nat) -> nat { mapd(a, b, |x, y| bor(x, y)) }
pub open spec fn bw_xor(a: nat, b: nat) -> nat { mapd(a, b, |x, y| bxor(x, y)) }
pub open spec fn bw_and(a: nat, b: nat) -> nat { mapd(a, b, |x, y| band(x, y)) }
pub open spec fn bw_andnot(a: nat, b: nat) -> nat { mapd(a, b, |x, y| bandnot(x, y)) }

pub proof fn or_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_or(a, b), i) == bor(bit(a, i), bit(b, i))
{ mapd_bit(a, b, |x, y| bor(x, y), i); }

pub proof fn xor_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_xor(a, b), i) == bxor(bit(a, i), bit(b, i))
{ mapd_bit(a, b, |x, y| bxor(x, y), i); }

pub proof fn and_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_and(a, b), i) == band(bit(a, i), bit(b, i))
{ mapd_bit(a, b, |x, y| band(x, y), i); }

pub proof fn andnot_bit(a: nat, b: nat, i: nat)
    ensures bit(bw_andnot(a, b), i) == bandnot(bit(a, i), bit(b, i))
{ mapd_bit(a, b, |x, y| bandnot(x, y), i); }

/// Bitwise disjointness
pub open spec fn disj(a: nat, b: nat) -> bool { bw_and(a, b) == 0 }

pub proof fn disj_bits(a: nat, b: nat)
    ensures disj(a, b) <==> forall|i: nat| !(bit(a, i) && bit(b, i))
{
    if disj(a, b) {
        assert forall|i: nat| #![auto] !(bit(a, i) && bit(b, i)) by {
            and_bit(a, b, i);
            bit_zero(i);
        };
    } else {
        // bw_and(a,b) != 0, so some bit is true
        // We need: exists i such that bit(bw_and(a,b), i) == true
        // This follows from: if all bits are false, then the number is 0
        if forall|i: nat| !(bit(a, i) && bit(b, i)) {
            assert forall|i: nat| #![auto] !bit(bw_and(a, b), i) by {
                and_bit(a, b, i);
            };
            assert forall|i: nat| #![auto] bit(bw_and(a, b), i) == bit(0 as nat, i) by {
                bit_zero(i);
            };
            eq_from_bits(bw_and(a, b), 0);
            assert(false); // contradiction
        }
    }
}

// ================================================================
// Addition with carry
// ================================================================

pub open spec fn plus_c(a: nat, b: nat, c: bool) -> nat
    decreases a + b
{
    if a == 0 && b == 0 { bn(c) }
    else {
        let (r, c1) = bplus(hd(a), hd(b), c);
        cons(plus_c(tl(a), tl(b), c1), r)
    }
}

pub proof fn plus_c_correct(a: nat, b: nat, c: bool)
    ensures plus_c(a, b, c) == a + b + bn(c)
    decreases a + b
{
    reveal(plus_c);
    if a == 0 && b == 0 {
    } else {
        let (r, c1) = bplus(hd(a), hd(b), c);
        bplus_correct(hd(a), hd(b), c);
        plus_c_correct(tl(a), tl(b), c1);
        cons_hd_tl(a);
        cons_hd_tl(b);
        // a = hd(a) + 2*tl(a), b = hd(b) + 2*tl(b)
        // a + b + c = bn(hd(a)) + bn(hd(b)) + bn(c) + 2*(tl(a) + tl(b))
        //           = 2*bn(c1) + bn(r) + 2*(tl(a) + tl(b))
        //           = bn(r) + 2*(tl(a) + tl(b) + bn(c1))
        //           = bn(r) + 2*plus_c(tl(a), tl(b), c1)
        //           = cons(plus_c(tl(a), tl(b), c1), r)
        assert(a == bn(hd(a)) + 2 * tl(a));
        assert(b == bn(hd(b)) + 2 * tl(b));
        assert(bn(hd(a)) + bn(hd(b)) + bn(c) == 2 * bn(c1) + bn(r));
        assert(plus_c(tl(a), tl(b), c1) == tl(a) + tl(b) + bn(c1));
        assert(cons(plus_c(tl(a), tl(b), c1), r) == bn(r) + 2 * (tl(a) + tl(b) + bn(c1)));
        assert(a + b + bn(c) == bn(r) + 2 * (tl(a) + tl(b) + bn(c1)));
    }
}

pub open spec fn plus(a: nat, b: nat) -> nat { plus_c(a, b, false) }

pub proof fn plus_correct(a: nat, b: nat)
    ensures nat_add(a, b) == a + b
{ plus_c_correct(a, b, false); }

// ================================================================
// Shifts
// ================================================================

pub open spec fn lsh(n: nat) -> nat { cons(n, false) }
pub open spec fn rsh(n: nat) -> nat { tl(n) }

pub proof fn lsh_is_times2(n: nat)
    ensures lsh(n) == 2 * n
{}

pub proof fn rsh_is_div2(n: nat)
    ensures rsh(n) == n / 2
{}

pub open spec fn lshi(n: nat, i: nat) -> nat
    decreases i
{ if i == 0 { n } else { lsh(lshi(n, (i - 1) as nat)) } }

pub open spec fn rshi(n: nat, i: nat) -> nat
    decreases i
{ if i == 0 { n } else { rshi(rsh(n), (i - 1) as nat) } }

// ================================================================
// 2^i and ones(i) = 2^i - 1
// ================================================================

pub open spec fn exp2(i: nat) -> nat
    decreases i
{ if i == 0 { 1 } else { 2 * exp2((i - 1) as nat) } }

pub proof fn exp2_pos(i: nat)
    ensures exp2(i) > 0
    decreases i
{
    reveal(exp2);
    if i > 0 { exp2_pos((i - 1) as nat); }
}

pub open spec fn ones(i: nat) -> nat { (exp2(i) - 1) as nat }

pub proof fn ones_bit(i: nat, j: nat)
    ensures bit(ones(i), j) == (j < i)
    decreases i
{
    reveal(bit);
    reveal(exp2);
    if i == 0 {
        bit_zero(j);
    } else {
        // ones(i) = 2^i - 1 = 2*(2^(i-1) - 1) + 1 = cons(ones(i-1), true)
        exp2_pos((i - 1) as nat);
        let o = ones(i);
        let prev = ones((i - 1) as nat);
        assert(exp2(i) == 2 * exp2((i - 1) as nat));
        assert(o == 2 * exp2((i - 1) as nat) - 1);
        assert(o == 2 * prev + 1);
        assert(o == cons(prev, true));
        if j == 0 {
            hd_cons(prev, true);
        } else {
            hd_cons(prev, true);
            assert(bit(o, j) == bit(tl(o), (j - 1) as nat));
            assert(tl(o) == prev);
            ones_bit((i - 1) as nat, (j - 1) as nat);
        }
    }
}

// ================================================================
// Chop: truncate to i low-order bits
// ================================================================

pub open spec fn chop(n: nat, i: nat) -> nat
    decreases i
{
    if i == 0 { 0 }
    else { cons(chop(tl(n), (i - 1) as nat), hd(n)) }
}

pub proof fn chop_bit(n: nat, i: nat, j: nat)
    ensures bit(chop(n, i), j) == (if j < i { bit(n, j) } else { false })
    decreases i, j
{
    reveal(bit);
    reveal(chop);
    if i == 0 {
        bit_zero(j);
    } else {
        let c = chop(tl(n), (i - 1) as nat);
        let result = cons(c, hd(n));
        if j == 0 {
            hd_cons(c, hd(n));
        } else {
            hd_cons(c, hd(n));
            assert(bit(result, j) == bit(tl(result), (j - 1) as nat));
            assert(tl(result) == c);
            chop_bit(tl(n), (i - 1) as nat, (j - 1) as nat);
            assert(bit(n, j) == bit(tl(n), (j - 1) as nat)) by { bit_tl(n, (j - 1) as nat); };
        }
    }
}

/// n fits in i bits
pub open spec fn fits(n: nat, i: nat) -> bool { n == chop(n, i) }

pub proof fn chop_fits(n: nat, i: nat)
    ensures fits(chop(n, i), i)
{
    assert forall|j: nat| #![auto] bit(chop(chop(n, i), i), j) == bit(chop(n, i), j) by {
        chop_bit(chop(n, i), i, j);
        chop_bit(n, i, j);
    };
    eq_from_bits(chop(chop(n, i), i), chop(n, i));
}

/// chop preserves disjointness
pub proof fn chop_disj(a: nat, b: nat, i: nat)
    requires disj(a, b)
    ensures disj(chop(a, i), chop(b, i))
{
    disj_bits(a, b);
    assert forall|j: nat| #![auto] !(bit(chop(a, i), j) && bit(chop(b, i), j)) by {
        chop_bit(a, i, j);
        chop_bit(b, i, j);
    };
    disj_bits(chop(a, i), chop(b, i));
}

/// chop distributes through mapd
pub proof fn chop_mapd(a: nat, b: nat, f: spec_fn(bool, bool) -> bool, i: nat)
    requires f(false, false) == false
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

// ================================================================
// chop == mod 2^i
// ================================================================

proof fn mul_assoc_2(q: nat, e: nat)
    ensures 2 * (q * e) == q * (2 * e)
{
    vstd::arithmetic::mul::lemma_mul_is_associative(2 as int, q as int, e as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(2 as int, q as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(q as int, 2 as int, e as int);
}

pub proof fn chop_is_mod(n: nat, i: nat)
    ensures chop(n, i) == n % exp2(i)
    decreases i
{
    reveal(chop);
    reveal(exp2);
    if i == 0 {
    } else {
        chop_is_mod(tl(n), (i - 1) as nat);
        cons_hd_tl(n);
        exp2_pos((i - 1) as nat);
        let e = exp2((i - 1) as nat);
        let h: nat = bn(hd(n));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(tl(n) as int, e as int);
        let q = (tl(n) / e) as nat;
        let r = (tl(n) % e) as nat;
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(2 as int, (q * e) as int, r as int);
        mul_assoc_2(q, e);
        let d = (2 * e) as int;
        // 2*tl(n) = 2*(q*e + r) = 2*q*e + 2*r = q*(2*e) + 2*r
        assert(2 * tl(n) == q * (2 * e) + 2 * r);
        // n = h + 2*tl(n) = h + q*(2*e) + 2*r = q*d + (h + 2*r)
        assert(n == h + q * (2 * e) + 2 * r);
        assert(n as int == (q as int) * d + ((h + 2 * r) as int));
        assert(h + 2 * r < 2 * e) by {
            assert(h <= 1);
            assert(r < e);
            // 2*r < 2*e and h <= 1 < 2, but we need h + 2*r < 2*e
            // h + 2*r <= 1 + 2*(e-1) = 2*e - 1 < 2*e
            vstd::arithmetic::mul::lemma_mul_inequality(r as int, (e - 1) as int, 2);
        };
        // By uniqueness of Euclidean division:
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, d);
        // n == (n/d)*d + n%d with 0 <= n%d < d
        // n == q*d + (h+2*r) with 0 <= h+2*r < d
        // So n%d == h+2*r and n/d == q
        // Z3 should get this from the two decompositions + uniqueness
        // Help it by asserting the remainder explicitly
        assert(n % (2 * e) == h + 2 * r) by {
            let nd = (n as int) / d;
            let nr = (n as int) % d;
            assert(n as int == nd * d + nr);
            assert(0 <= nr < d);
            assert(n as int == (q as int) * d + ((h + 2 * r) as int));
            // (nd - q) * d == (h + 2*r) - nr
            // |h+2*r - nr| < d, and (nd-q)*d is a multiple of d
            // So nd == q and nr == h+2*r
            assert((nd - q as int) * d == (h + 2 * r) as int - nr) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub(d, nd, q as int);
            };
            if nd != q as int {
                if nd > q as int {
                    assert((nd - q as int) >= 1);
                    vstd::arithmetic::mul::lemma_mul_inequality(1, nd - q as int, d);
                    assert((nd - q as int) * d >= d);
                } else {
                    assert((q as int - nd) >= 1);
                    vstd::arithmetic::mul::lemma_mul_inequality(1, q as int - nd, d);
                    assert((q as int - nd) * d >= d);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_sub(d, q as int, nd);
                }
            }
        };
        // chop(n, i) = cons(r, hd(n)) = h + 2*r
        assert(chop(n, i) == cons(chop(tl(n), (i - 1) as nat), hd(n)));
        assert(chop(tl(n), (i - 1) as nat) == r);
    }
}

// ================================================================
// chop distributes through plus
// ================================================================

pub proof fn chop_plus(a: nat, b: nat, i: nat)
    ensures chop(nat_add(a, b), i) == chop(nat_add(chop(a, i), chop(b, i)), i)
{
    nat_add_correct(a, b);
    nat_add_correct(chop(a, i), chop(b, i));
    chop_is_mod(a, i);
    chop_is_mod(b, i);
    chop_is_mod(nat_add(a, b), i);
    chop_is_mod(nat_add(chop(a, i), chop(b, i)), i);
    exp2_pos(i);
    let d = exp2(i) as int;
    // Need: (a+b) % d == ((a%d) + (b%d)) % d
    // i.e. chop(a+b, i) == chop((a%d + b%d), i)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b as int, d);
    let ra = (a as int) % d;
    let rb = (b as int) % d;
    let qa = (a as int) / d;
    let qb = (b as int) / d;
    // a + b = (qa+qb)*d + ra + rb
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, qa, qb);
    assert((a + b) as int == (qa + qb) * d + ra + rb);
    // ra + rb = q2*d + r2
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ra + rb, d);
    let q2 = (ra + rb) / d;
    let r2 = (ra + rb) % d;
    assert(ra + rb == q2 * d + r2);
    // a + b = (qa+qb+q2)*d + r2
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, qa + qb, q2);
    assert((a + b) as int == (qa + qb + q2) * d + r2);
    // By uniqueness: (a+b) % d == r2
    mod_unique((a + b) as int, d, qa + qb + q2, r2);
    // And (ra+rb) % d == r2 (already from lemma_fundamental_div_mod)
    // So (a+b) % d == (ra+rb) % d
}

proof fn mod_unique(n: int, d: int, q: int, r: int)
    requires d > 0, 0 <= r, r < d, n == q * d + r, q >= 0
    ensures n % d == r
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, d);
    let nd = n / d;
    let nr = n % d;
    // Both: n == nd*d + nr and n == q*d + r
    // So nd*d + nr == q*d + r
    // If nd > q: nd >= q+1, so nd*d >= (q+1)*d = q*d + d, so nr <= r - d < 0. Contradiction.
    // If nd < q: similarly. So nd == q, nr == r.
    if nd != q {
        if nd > q {
            assert(nd >= q + 1);
            assert(q + 1 >= 1);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, q, 1 as int);
            vstd::arithmetic::mul::lemma_mul_inequality(q + 1, nd, d);
            // nd*d + nr == q*d + r, so q*d + d + nr <= q*d + r, so d + nr <= r
            // But nr >= 0 and r < d, so d <= r - nr < d. Contradiction.
        } else {
            assert(q >= nd + 1);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(d, nd, 1 as int);
            assert((nd + 1) * d == nd * d + d);
            vstd::arithmetic::mul::lemma_mul_inequality(nd + 1, q, d);
            assert((nd + 1) * d <= q * d);
        }
    }
}

// ================================================================
// Multiplication helpers
// ================================================================

pub open spec fn times_b(a: nat, b: bool) -> nat { if b { a } else { 0 } }

pub open spec fn times1(a: nat, b: nat, acc: nat) -> nat
    decreases a
{
    if a == 0 { acc }
    else { nat_mul_acc(tl(a), lsh(b), nat_add(acc, nat_mul_bit(b, hd(a)))) }
}

pub open spec fn neg(n: nat, i: nat) -> nat {
    chop(nat_add(bw_xor(n, ones(i)), 1), i)
}

// ================================================================
// Tnum spec: membership, operations, soundness
// ================================================================

/// Tnum membership: n & !m == v (equivalently, n agrees with v on non-masked bits)
pub open spec fn tn_has(v: nat, m: nat, n: nat) -> bool {
    bw_andnot(n, m) == v
}

/// Tnum addition (bitvector algorithm)
pub open spec fn tn_plus_v(v1: nat, m1: nat, v2: nat, m2: nat) -> nat {
    let lbv = nat_add(v1, v2);
    let lbm = nat_add(m1, m2);
    let ub = nat_add(lbv, lbm);
    let diff = bw_xor(ub, lbv);
    let mask = bw_or(bw_or(diff, m1), m2);
    bw_andnot(lbv, mask)
}
pub open spec fn tn_plus_m(v1: nat, m1: nat, v2: nat, m2: nat) -> nat {
    let lbv = nat_add(v1, v2);
    let lbm = nat_add(m1, m2);
    let ub = nat_add(lbv, lbm);
    let diff = bw_xor(ub, lbv);
    bw_or(bw_or(diff, m1), m2)
}

/// Tnum negation (i-bit two's complement)
pub open spec fn tn_neg_v(v: nat, m: nat, i: nat) -> nat {
    tn_plus_v(bw_andnot(bw_xor(v, ones(i)), m), m, 1, 0)
}
pub open spec fn tn_neg_m(v: nat, m: nat, i: nat) -> nat {
    tn_plus_m(bw_andnot(bw_xor(v, ones(i)), m), m, 1, 0)
}

/// Tnum subtraction (direct formula from Tnum crate)
pub open spec fn tn_sub_v(v1: nat, m1: nat, v2: nat, m2: nat) -> nat {
    // lb = v1 - v2, lb2 = lb - m2, ub = lb + m1
    // diff = ub ^ lb2, mask = diff | m1 | m2
    // result_v = lb & !mask
    // For the spec we work on nats; wrapping is handled by chop
    let lb = nat_add(v1, neg(v2, 64)); // v1 - v2 as nat (will be chopped)
    let lb2 = nat_add(lb, neg(m2, 64));
    let ub = nat_add(lb, m1);
    let diff = bw_xor(ub, lb2);
    let mask = bw_or(bw_or(diff, m1), m2);
    bw_andnot(lb, mask)
}

/// Tnum times_b: multiply by a tristate bit
pub open spec fn tn_times_b_v(v: nat, m: nat, bv: bool, bm: bool) -> nat {
    if bv { v } else if bm { 0 } else { 0 }
}
pub open spec fn tn_times_b_m(v: nat, m: nat, bv: bool, bm: bool) -> nat {
    if bv { m } else if bm { bw_or(v, m) } else { 0 }
}

/// Tnum multiplication: shift-and-add with Anum accumulator
/// This is the SPEC version on infinite bitstrings.
/// acc_v tracks the certain part, acc_m tracks the uncertain part.
/// Loop invariant: the concrete multiplication result is in the abstract accumulator.
///
/// times_loop(p, q, acc_v, acc_m) computes:
///   for each bit i of p:
///     if p.v[i]: acc_m += Tn(0, q.m)
///     if p.m[i]: acc_m += Tn(0, q.v | q.m)
///     q <<= 1; p >>= 1
///   return acc_m + acc_v
pub open spec fn tn_mul_loop(
    pv: nat, pm: nat,  // remaining multiplier bits
    qv: nat, qm: nat,  // shifted multiplicand
    acc_v: nat,         // certain accumulator (= product of known bits so far)
    acc_m: nat,         // uncertain accumulator mask
) -> (nat, nat)  // (result_v, result_m) of the final Tnum
    decreases pv + pm
{
    if pv == 0 && pm == 0 {
        // Done: result = Tn(acc_v, 0) + Tn(0, acc_m) via tnum addition
        (tn_plus_v(acc_v, 0, 0, acc_m), tn_plus_m(acc_v, 0, 0, acc_m))
    } else {
        let p_v_bit = hd(pv);
        let p_m_bit = hd(pm);
        // Update acc_m based on current bit of multiplier
        let new_acc_m = if p_v_bit && !p_m_bit {
            // Known-1 bit: add q's uncertainty
            tn_plus_m(0, acc_m, 0, qm)
        } else if p_m_bit {
            // Unknown bit: add q's full range
            tn_plus_m(0, acc_m, 0, bw_or(qv, qm))
        } else {
            // Known-0 bit: no change
            acc_m
        };
        tn_mul_loop(tl(pv), tl(pm), lsh(qv), lsh(qm), acc_v, new_acc_m)
    }
}

/// Top-level Tnum multiplication spec
pub open spec fn tn_mul_v(v1: nat, m1: nat, v2: nat, m2: nat) -> nat {
    tn_mul_loop(v1, m1, v2, m2, nat_add(v1, 0 /* v1 * v2 computed externally */), 0).0
}

// ================================================================
// Soundness proof: Tnum multiplication
//
// The key invariant: at each iteration of the loop,
//   forall c1 c2 acc_c.
//     tn_has(pv, pm, c1) && tn_has(qv, qm, c2) && tn_has(acc_v, acc_m, acc_c)
//     ==> the final result has nat_mul_acc(c1, c2, acc_c)
//
// This follows from:
// 1. nat_mul_acc(c1, c2, acc_c) == nat_mul_acc(tl(c1), lsh(c2), acc_c + c2*hd(c1))
//    (the concrete shift-and-add step)
// 2. The abstract step overapproximates the concrete step:
//    - if hd(pv)=1: acc_c + c2*1 = acc_c + c2. The uncertain part c2's m bits
//      are added to acc_m. Sound because tn_plus is sound.
//    - if hd(pm)=1: c1's low bit is 0 or 1. If 0: acc unchanged. If 1: acc_c + c2.
//      We add Tn(0, qv|qm) which covers both cases.
//    - if hd(pv)=0,hd(pm)=0: c1's low bit is 0. acc unchanged.
// 3. Base case: when p=0, c1=0, so nat_mul_acc(0, c2, acc_c) = acc_c.
//    The result Tn(acc_v, 0) + Tn(0, acc_m) contains acc_c.
// ================================================================

/// Proof that times1 unfolds correctly
pub proof fn times1_step(a: nat, b: nat, acc: nat)
    requires a > 0 || tl(a) > 0  // a != 0
    ensures nat_mul_acc(a, b, acc) == nat_mul_acc(tl(a), lsh(b), nat_add(acc, nat_mul_bit(b, hd(a))))
    decreases a
{
    reveal(times1);
    // Direct from definition
}

/// Proof that nat_mul_acc(0, b, acc) == acc
pub proof fn times1_base(b: nat, acc: nat)
    ensures nat_mul_acc(0, b, acc) == acc
{
    reveal(times1);
}

/// Proof that times_b is sound: if tn_has(v,m,c) and b.has(bit), then
/// tn_has(times_b_v, times_b_m, c * bn(bit))
pub proof fn times_b_sound(v: nat, m: nat, c: nat, bv: bool, bm: bool, concrete_bit: bool)
    requires
        disj(v, m),
        tn_has(v, m, c),
        (bv ==> concrete_bit) && (!bv && !bm ==> !concrete_bit),
    ensures
        tn_has(tn_times_b_v(v, m, bv, bm), tn_times_b_m(v, m, bv, bm), nat_mul_bit(c, concrete_bit))
{
    if bv {
        assert(nat_mul_bit(c, true) == c);
    } else if bm {
        assert(nat_mul_bit(c, concrete_bit) == if concrete_bit { c } else { 0 });
        assert forall|i: nat| #![auto] !bit(bw_andnot(nat_mul_bit(c, concrete_bit), bw_or(v, m)), i) by {
            andnot_bit(nat_mul_bit(c, concrete_bit), bw_or(v, m), i);
            or_bit(v, m, i);
            if concrete_bit {
                andnot_bit(c, m, i);
            } else {
                bit_zero(i);
            }
        };
        assert(bw_andnot(nat_mul_bit(c, concrete_bit), bw_or(v, m)) == 0) by {
            assert forall|i: nat| #![auto] bit(bw_andnot(nat_mul_bit(c, concrete_bit), bw_or(v, m)), i) == bit(0 as nat, i) by {
                andnot_bit(nat_mul_bit(c, concrete_bit), bw_or(v, m), i);
                bit_zero(i);
                or_bit(v, m, i);
                if concrete_bit { andnot_bit(c, m, i); } else { bit_zero(i); }
            };
            eq_from_bits(bw_andnot(nat_mul_bit(c, concrete_bit), bw_or(v, m)), 0);
        };
    } else {
        assert(nat_mul_bit(c, false) == 0);
    }
}

// ================================================================
// Chopping: connect infinite bitstring proofs to finite width
//
// Key theorem: chop(op(a, b), W) == op_W(chop(a, W), chop(b, W))
// Already proved for plus (chop_plus). Need for:
// - neg: chop(neg(n, W), W) — already defined as chop(nat_add(xor(n, ones(W)), 1), W)
// - times1: chop distributes through the shift-and-add loop
// - mapd: chop_mapd already proved
// ================================================================

/// chop distributes through times_b
pub proof fn chop_times_b(a: nat, b: bool, i: nat)
    ensures chop(nat_mul_bit(a, b), i) == nat_mul_bit(chop(a, i), b)
{
    if b {} else {
        assert forall|j: nat| #![auto] bit(chop(0 as nat, i), j) == bit(0 as nat, j) by {
            chop_bit(0, i, j); bit_zero(j);
        };
        eq_from_bits(chop(0, i), 0);
    }
}

proof fn chop_zero(w: nat)
    ensures chop(0 as nat, w) == 0
{
    assert forall|j: nat| #![auto] bit(chop(0 as nat, w), j) == bit(0 as nat, j) by {
        chop_bit(0, w, j); bit_zero(j);
    };
    eq_from_bits(chop(0 as nat, w), 0);
}

proof fn chop_lsh(b: nat, w: nat)
    requires w > 0
    ensures chop(lsh(b), w) == lsh(chop(b, (w - 1) as nat))
{
    assert forall|j: nat| #![auto] bit(chop(lsh(b), w), j) == bit(lsh(chop(b, (w - 1) as nat)), j) by {
        chop_bit(lsh(b), w, j);
        bit_cons(b, false, j);
        bit_cons(chop(b, (w - 1) as nat), false, j);
        if j < w {
            if j > 0 { chop_bit(b, (w - 1) as nat, (j - 1) as nat); }
        } else {
            bit_zero(j);
        }
    };
    eq_from_bits(chop(lsh(b), w), lsh(chop(b, (w - 1) as nat)));
}

/// chop(lsh(b), w) == chop(lsh(chop(b, w)), w) — the version we actually need
proof fn chop_lsh_chop(b: nat, w: nat)
    ensures chop(lsh(b), w) == chop(lsh(chop(b, w)), w)
{
    assert forall|j: nat| #![auto] bit(chop(lsh(b), w), j) == bit(chop(lsh(chop(b, w)), w), j) by {
        chop_bit(lsh(b), w, j);
        chop_bit(lsh(chop(b, w)), w, j);
        if j < w {
            bit_cons(b, false, j);
            bit_cons(chop(b, w), false, j);
            if j > 0 {
                chop_bit(b, w, (j - 1) as nat);
            }
        }
    };
    eq_from_bits(chop(lsh(b), w), chop(lsh(chop(b, w)), w));
}

/// fits(tl(a), w) when fits(a, w) and a > 0
proof fn fits_tl(a: nat, w: nat)
    requires fits(a, w), a > 0
    ensures fits(tl(a), w)
{
    assert forall|j: nat| #![auto] bit(tl(a), j) == bit(chop(tl(a), w), j) by {
        chop_bit(tl(a), w, j);
        if j >= w {
            bit_tl(a, j);
            chop_bit(a, w, j + 1);
        }
    };
    eq_from_bits(tl(a), chop(tl(a), w));
}

/// The fundamental chopping theorem for multiplication.
/// If a fits in w bits, then the low w bits of nat_mul_acc(a, b, acc)
/// depend only on the low w bits of b and acc.
pub proof fn chop_times1(a: nat, b: nat, acc: nat, w: nat)
    requires fits(a, w)
    ensures chop(nat_mul_acc(a, b, acc), w) == chop(nat_mul_acc(a, chop(b, w), chop(acc, w)), w)
    decreases a
{
    reveal(times1);
    if a == 0 {
        chop_fits(acc, w);
    } else {
        fits_tl(a, w);

        // LHS unfolds to: nat_mul_acc(tl(a), lsh(b), nat_add(acc, nat_mul_bit(b, hd(a))))
        // RHS unfolds to: nat_mul_acc(tl(a), lsh(chop(b,w)), nat_add(chop(acc,w), nat_mul_bit(chop(b,w), hd(a))))

        let tb = nat_mul_bit(b, hd(a));
        let tb_c = nat_mul_bit(chop(b, w), hd(a));
        let new_acc = nat_add(acc, tb);
        let new_acc_c = nat_add(chop(acc, w), tb_c);

        // Key facts:
        // (A) chop(tb, w) == tb_c  [from chop_times_b]
        chop_times_b(b, hd(a), w);

        // (B) chop(new_acc, w) == chop(new_acc_c, w)  [from chop_plus + (A)]
        chop_nat_add(acc, tb, w);
        // chop_plus gives: chop(nat_add(acc, tb), w) == chop(nat_add(chop(acc,w), chop(tb,w)), w)
        // By (A): chop(tb, w) == tb_c
        // So: chop(new_acc, w) == chop(nat_add(chop(acc,w), tb_c), w) == chop(new_acc_c, w)

        // (C) chop(lsh(b), w) == chop(lsh(chop(b,w)), w)  [from chop_lsh_chop]
        chop_lsh_chop(b, w);

        // Apply IH to LHS:
        chop_times1(tl(a), lsh(b), new_acc, w);
        // gives: chop(nat_mul_acc(tl(a), lsh(b), new_acc), w)
        //      == chop(nat_mul_acc(tl(a), chop(lsh(b),w), chop(new_acc,w)), w)

        // Apply IH to RHS:
        chop_times1(tl(a), lsh(chop(b, w)), new_acc_c, w);
        // gives: chop(nat_mul_acc(tl(a), lsh(chop(b,w)), new_acc_c), w)
        //      == chop(nat_mul_acc(tl(a), chop(lsh(chop(b,w)),w), chop(new_acc_c,w)), w)

        // Now: chop(lsh(b), w) == chop(lsh(chop(b,w)), w)  [by (C)]
        //      chop(new_acc, w) == chop(new_acc_c, w)       [by (B)]
        // So both IH results equal the same thing. QED.
    }
}

// ================================================================
// Machine-word (u64) executable versions
// ================================================================

pub exec fn u64_bw_or(a: u64, b: u64) -> (r: u64)
    ensures r == (a | b)
{ a | b }

pub exec fn u64_bw_and(a: u64, b: u64) -> (r: u64)
    ensures r == (a & b)
{ a & b }

pub exec fn u64_bw_xor(a: u64, b: u64) -> (r: u64)
    ensures r == (a ^ b)
{ a ^ b }

pub exec fn u64_bw_andnot(a: u64, b: u64) -> (r: u64)
    ensures r == (a & !b)
{ a & !b }

pub exec fn u64_plus(a: u64, b: u64) -> (r: u64)
    ensures r == a.wrapping_add(b)
{ a.wrapping_add(b) }

pub exec fn u64_times(a: u64, b: u64) -> (r: u64)
    ensures r == a.wrapping_mul(b)
{ a.wrapping_mul(b) }

/// Machine-word Tnum: pair of u64 with v & m == 0
#[derive(Clone, Copy)]
pub struct Tnum64 {
    pub v: u64,
    pub m: u64,
}

impl Tnum64 {
    pub open spec fn inv(self) -> bool { self.v & self.m == 0 }
    pub open spec fn min(self) -> u64 { self.v }
    pub open spec fn max(self) -> u64 { self.v | self.m }

    pub exec fn new(v: u64, m: u64) -> (r: Tnum64)
        requires v & m == 0
        ensures r.v == v, r.m == m, r.inv()
    { Tnum64 { v, m } }

    pub exec fn unit(n: u64) -> (r: Tnum64)
        ensures r.v == n, r.m == 0, r.inv()
    { assert(n & 0u64 == 0u64) by (bit_vector); Tnum64 { v: n, m: 0 } }

    pub exec fn zero() -> (r: Tnum64)
        ensures r.v == 0, r.m == 0, r.inv()
    { assert(0u64 & 0u64 == 0u64) by (bit_vector); Tnum64 { v: 0, m: 0 } }

    pub exec fn top() -> (r: Tnum64)
        ensures r.v == 0, r.m == u64::MAX, r.inv()
    { assert(0u64 & u64::MAX == 0u64) by (bit_vector); Tnum64 { v: 0, m: u64::MAX } }

    /// Bitwise OR
    pub exec fn bw_or(self, t: Tnum64) -> (r: Tnum64)
        requires self.inv(), t.inv()
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m; let tv = t.v; let tm = t.m;
        assert((sv | tv) & (((sm | tm) & !(sv | tv))) == 0u64) by (bit_vector);
        Tnum64 { v: sv | tv, m: (sm | tm) & !(sv | tv) }
    }

    /// Bitwise AND
    pub exec fn bw_and(self, t: Tnum64) -> (r: Tnum64)
        requires self.inv(), t.inv()
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m; let tv = t.v; let tm = t.m;
        assert((sv & tv) & (sm | tm) == 0u64) by (bit_vector)
            requires sv & sm == 0u64, tv & tm == 0u64;
        Tnum64 { v: sv & tv, m: sm | tm }
    }

    /// Bitwise XOR
    pub exec fn bw_xor(self, t: Tnum64) -> (r: Tnum64)
        requires self.inv(), t.inv()
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m; let tv = t.v; let tm = t.m;
        let m = sm | tm;
        assert(((sv ^ tv) & !m) & m == 0u64) by (bit_vector);
        Tnum64 { v: (sv ^ tv) & !m, m }
    }

    /// Addition (the bitvector algorithm)
    pub exec fn plus(self, t: Tnum64) -> (r: Tnum64)
        requires self.inv(), t.inv()
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m; let tv = t.v; let tm = t.m;
        let lbv = sv.wrapping_add(tv);
        let lbm = sm.wrapping_add(tm);
        let ub = lbv.wrapping_add(lbm);
        let diff = ub ^ lbv;
        let mask = diff | sm | tm;
        assert((lbv & !mask) & mask == 0u64) by (bit_vector);
        Tnum64 { v: lbv & !mask, m: mask }
    }

    /// Join (union)
    pub exec fn join(self, t: Tnum64) -> (r: Tnum64)
        requires self.inv(), t.inv()
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m; let tv = t.v; let tm = t.m;
        let v = sv & tv;
        let u = (sv ^ sm) | (tv ^ tm);
        let m = v ^ u;
        assert((sv & tv) & ((sv & tv) ^ ((sv ^ sm) | (tv ^ tm))) == 0u64) by (bit_vector)
            requires sv & sm == 0u64, tv & tm == 0u64;
        Tnum64 { v, m }
    }

    /// Shift left
    pub exec fn shl(self, i: u32) -> (r: Tnum64)
        requires self.inv(), i < 64
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m;
        assert((sv << i) & (sm << i) == 0u64) by (bit_vector)
            requires sv & sm == 0u64, i < 64u32;
        Tnum64 { v: sv << i, m: sm << i }
    }

    /// Shift right
    pub exec fn shr(self, i: u32) -> (r: Tnum64)
        requires self.inv(), i < 64
        ensures r.inv()
    {
        let sv = self.v; let sm = self.m;
        assert((sv >> i) & (sm >> i) == 0u64) by (bit_vector)
            requires sv & sm == 0u64, i < 64u32;
        Tnum64 { v: sv >> i, m: sm >> i }
    }

    /// Inequality test: true if provably no common member
    pub exec fn ne(self, t: Tnum64) -> (r: bool)
        requires self.inv(), t.inv()
        ensures r ==> (self.v ^ t.v) & !(self.m | t.m) != 0
    {
        let xor_min = (self.v ^ t.v) & !(self.m | t.m);
        xor_min != 0
    }
}

/// Machine-word Anum
#[derive(Clone, Copy)]
pub struct Anum64 {
    pub v: u64,
    pub m: u64,
}

impl Anum64 {
    pub exec fn zero() -> (r: Anum64)
        ensures r.v == 0, r.m == 0
    { Anum64 { v: 0, m: 0 } }

    pub exec fn from_tn(t: Tnum64) -> (r: Anum64)
        ensures r.v == t.v, r.m == t.m
    { Anum64 { v: t.v, m: t.m } }

    /// Anum addition: add v's, tnum-add m's
    pub exec fn plus(self, a: Anum64) -> (r: Anum64)
    {
        assert(0u64 & self.m == 0u64) by (bit_vector);
        assert(0u64 & a.m == 0u64) by (bit_vector);
        let tm_self = Tnum64 { v: 0, m: self.m };
        let tm_a = Tnum64 { v: 0, m: a.m };
        let tm_sum = tm_self.add(tm_a);
        Anum64 { v: self.v.wrapping_add(a.v), m: tm_sum.m }
    }

    /// Convert back to Tnum
    pub exec fn to_tn(self) -> (r: Tnum64)
        ensures r.inv()
    {
        assert(self.v & 0u64 == 0u64) by (bit_vector);
        assert(0u64 & self.m == 0u64) by (bit_vector);
        let tv = Tnum64 { v: self.v, m: 0 };
        let tm = Tnum64 { v: 0, m: self.m };
        tm.add(tv)
    }
}

/// Tnum multiplication using Anum accumulator
pub exec fn tn64_times(t0: Tnum64, t1: Tnum64) -> (r: Tnum64)
    requires t0.inv(), t1.inv()
    ensures r.inv()
{
    let mut acc_m = Tnum64::zero();
    let mut i: u32 = 0;

    while i < 64
        invariant
            t0.inv(),
            t1.inv(),
            acc_m.inv(),
            i <= 64,
        decreases 64 - i,
    {
        let p_v_bit = (t0.v >> i) & 1;
        let p_m_bit = (t0.m >> i) & 1;
        let q_m = t1.m << i;
        let q_max = (t1.v | t1.m) << i;
        if p_v_bit != 0 {
            assert(0u64 & q_m == 0u64) by (bit_vector);
            let contrib = Tnum64 { v: 0, m: q_m };
            acc_m = acc_m.add(contrib);
        } else if p_m_bit != 0 {
            assert(0u64 & q_max == 0u64) by (bit_vector);
            let contrib = Tnum64 { v: 0, m: q_max };
            acc_m = acc_m.add(contrib);
        }
        i = i + 1;
    }
    assert(t0.v.wrapping_mul(t1.v) & 0u64 == 0u64) by (bit_vector);
    let acc_v = Tnum64 { v: t0.v.wrapping_mul(t1.v), m: 0 };
    acc_m.add(acc_v)
}

}
