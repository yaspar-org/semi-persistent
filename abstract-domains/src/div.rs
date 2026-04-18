// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
use crate::bools::*;
use crate::nats::*;
use crate::tbit::*;
use crate::tnum::*;
/// Division for Tnums: iterated subtraction (dual of multiplication).
///
/// Multiplication scans multiplier bits LSB→MSB, accumulating `acc += shifted × bit`.
/// Division scans dividend bits MSB→LSB, maintaining an abstract remainder:
///   - Shift remainder left, bring in next dividend bit
///   - If min(remainder) ≥ divisor: quotient bit = 1, subtract
///   - If max(remainder) < divisor: quotient bit = 0, keep
///   - Otherwise: quotient bit = X (uncertain), remainder = join(rem, rem - d)
///
/// Subtraction uses two's complement via `add_bitwise`: `sub(a, d, w) = add_bitwise(a, 2^w - d).chop(w)`.
/// Soundness is free from `add_bitwise_eq` + `chop_sound`.
///
/// The key loop invariant: `rv < dv` (concrete remainder < concrete divisor).
/// The ABSTRACT remainder may exceed `d` (due to over-approximation in sub_const),
/// but every CONCRETE value tracked by the abstract state satisfies `rv < dv`.
///
/// Also provides general Tnum/Tnum division via `neg_tn` (two's complement negation)
/// and `sub_tn` (abstract subtraction). Negation soundness proved via `xor_ones_complement`.
/// and building the quotient bit by bit via conditional subtraction.
use vstd::prelude::*;

verus! {

impl Tnum {
    /// Membership implies value is between min and max.
    pub proof fn has_bounds(self, n: nat)
        requires self.inv(), self.has(n)
        ensures self.min() <= n, n <= self.max()
    {
        self.has_equiv(n);
        assert forall|i: nat| #![auto] !(bit(bw_and_not(n, self.mask), i).b() && bit(bw_and(n, self.mask), i).b()) by {
            and_not_bit(n, self.mask, i); and_bit(n, self.mask, i);
        };
        disj_bits(bw_and_not(n, self.mask), bw_and(n, self.mask));
        nat_add_or(self.val, bw_and(n, self.mask));
        assert forall|i: nat| #![auto] bit(bw_or(bw_and_not(n, self.mask), bw_and(n, self.mask)), i) == bit(n, i) by {
            or_bit(bw_and_not(n, self.mask), bw_and(n, self.mask), i);
            and_not_bit(n, self.mask, i); and_bit(n, self.mask, i);
        };
        eq_from_bits(bw_or(bw_and_not(n, self.mask), bw_and(n, self.mask)), n);
        assert(n == nat_add(self.val, bw_and(n, self.mask)));
        nat_add_carry_correct(self.val, bw_and(n, self.mask), Bit::f());
        nat_add_or(self.val, self.mask);
        nat_add_carry_correct(self.val, self.mask, Bit::f());
        assert forall|i: nat| #![auto] !(bit(bw_and(n, self.mask), i).b() && bit(bw_and_not(self.mask, n), i).b()) by {
            and_bit(n, self.mask, i); and_not_bit(self.mask, n, i);
        };
        disj_bits(bw_and(n, self.mask), bw_and_not(self.mask, n));
        nat_add_or(bw_and(n, self.mask), bw_and_not(self.mask, n));
        assert forall|i: nat| #![auto] bit(bw_or(bw_and(n, self.mask), bw_and_not(self.mask, n)), i) == bit(self.mask, i) by {
            or_bit(bw_and(n, self.mask), bw_and_not(self.mask, n), i);
            and_bit(n, self.mask, i); and_not_bit(self.mask, n, i);
        };
        eq_from_bits(bw_or(bw_and(n, self.mask), bw_and_not(self.mask, n)), self.mask);
        nat_add_carry_correct(bw_and(n, self.mask), bw_and_not(self.mask, n), Bit::f());
    }

    /// Join preserves inv.
    pub proof fn join_inv(self, t: Tnum)
        requires self.inv(), t.inv()
        ensures self.join(t).inv()
    {
        let jv = bw_and(self.val, t.val);
        let jm = bw_xor(jv, bw_or(self.u(), t.u()));
        assert forall|i: nat| #![auto] !(bit(jv, i).b() && bit(jm, i).b()) by {
            and_bit(self.val, t.val, i);
            xor_bit(self.val, self.mask, i); xor_bit(t.val, t.mask, i);
            or_bit(bw_xor(self.val, self.mask), bw_xor(t.val, t.mask), i);
            xor_bit(jv, bw_or(self.u(), t.u()), i);
            disj_bits(self.val, self.mask); disj_bits(t.val, t.mask);
        };
        disj_bits(jv, jm);
    }

    /// Subtract constant d from self (bounded to w bits).
    pub open spec fn sub_const(self, d: nat, w: nat) -> Tnum {
        self.add_bitwise(Tnum::unit(twos_comp(d, w))).chop_tn(w)
    }
    /// The maximum value of a Tnum is always a member.
    pub proof fn max_has(self)
        requires self.inv()
        ensures self.has(self.max())
    {
        self.has_equiv(self.max());
        assert forall|i: nat| #![auto] bit(bw_and_not(self.max(), self.mask), i) == bit(self.val, i) by {
            and_not_bit(self.max(), self.mask, i);
            or_bit(self.val, self.mask, i);
            disj_bits(self.val, self.mask);
        };
        eq_from_bits(bw_and_not(self.max(), self.mask), self.val);
    }

    pub proof fn sub_const_sound(self, d: nat, w: nat)
        requires self.inv(), d > 0, d <= exp(w)
        ensures forall|n: nat| #![auto]
            self.has(n) && n >= d && n < exp(w) ==>
            self.sub_const(d, w).has((n - d) as nat)
    {
        let tc = twos_comp(d, w);
        let neg_d = Tnum::unit(tc);
        assert forall|j: nat| #![auto] !(bit(tc, j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(tc, 0);
        self.add_bitwise_eq(neg_d);
        self.add_sound(neg_d);
        let sum = self.add_bitwise(neg_d);
        Self::add_bitwise_inv(self, neg_d);
        assert forall|n: nat| #![auto]
            self.has(n) && n >= d && n < exp(w)
            implies self.sub_const(d, w).has((n - d) as nat) by {
            neg_d.has_equiv(tc);
            assert forall|i: nat| #![auto] bit(bw_and_not(tc, 0 as nat), i) == bit(tc, i) by {
                and_not_bit(tc, 0, i); bit_zero(i);
            };
            eq_from_bits(bw_and_not(tc, 0), tc);
            assert(neg_d.has(tc));
            assert(sum.has(nat_add(n, tc)));
            sum.chop_sound(w);
            nat_add_carry_correct(n, tc, Bit::f());
            let nd = (n - d) as nat;
            nat_add_carry_correct(nd, exp(w), Bit::f());
            assert(nat_add(n, tc) == nat_add(nd, exp(w)));
            chop_nat_add_pow2(nd, w);
            chop_id(nd, w);
            assert(sum.chop_tn(w).has(chop(nat_add(n, tc), w)));
        };
    }

    /// Shift self left by 1 and OR in a Tbit at bit 0.
    pub open spec fn lsh_or_tb(self, b: TBit) -> Tnum {
        Tnum { val: cons(self.val, b.val), mask: cons(self.mask, b.mask) }
    }

    pub proof fn lsh_or_tb_sound(self, b: TBit)
        ensures forall|r: nat, bv: Bit| #![auto]
            self.has(r) && b.has(bv) ==>
            self.lsh_or_tb(b).has(cons(r, bv))
    {
    }

    /// Abstract division of self by constant d, using w-bit long division.
    pub open spec fn div_const(self, d: nat, w: nat) -> (Tnum, Tnum)
        recommends d > 0
    {
        Self::div_const_loop(self, d, w, w, Tnum::zero(), Tnum::zero())
    }

    pub open spec fn div_const_loop(n: Tnum, d: nat, w: nat, i: nat, q: Tnum, r: Tnum) -> (Tnum, Tnum)
        recommends d > 0
        decreases i
    {
        if i == 0 { (q, r) }
        else {
            let i1 = (i - 1) as nat;
            let nbit = TBit { val: bit(n.val, i1), mask: bit(n.mask, i1) };
            let r1 = r.lsh_or_tb(nbit);
            if r1.min() >= d {
                let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                let r2 = r1.sub_const(d, w + 1);
                Self::div_const_loop(n, d, w, i1, q1, r2)
            } else if r1.max() < d {
                Self::div_const_loop(n, d, w, i1, q, r1)
            } else {
                let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                let r_sub = r1.sub_const(d, w + 1);
                let r2 = r1.join(r_sub);
                Self::div_const_loop(n, d, w, i1, q1, r2)
            }
        }
    }

    /// Soundness of div_const.
    pub proof fn div_const_sound(self, d: nat, w: nat)
        requires self.inv(), d > 0, d <= exp(w)
        ensures forall|n: nat| #![auto]
            self.has(n) ==>
            self.div_const(d, w).0.has(div1(n, d, 0, 0, w).0)
    {
        let z = Tnum::zero();
        disj_zero(0 as nat);
        assert(z.has(0 as nat));
        assert forall|j: nat| #![auto] j < w ==> bit(z.val, j) == Bit::f() && bit(z.mask, j) == Bit::f() by {
            bit_zero(j);
        };
        Self::div_const_loop_sound(self, d, w, w, z, z);
        assert forall|n: nat| #![auto] self.has(n)
            implies self.div_const(d, w).0.has(div1(n, d, 0, 0, w).0) by {
            assert(z.has(0 as nat));
            assert((0 as nat) < d);
        };
    }

    #[verifier::rlimit(5000)]
    proof fn div_const_loop_sound(n: Tnum, d: nat, w: nat, i: nat, q: Tnum, r: Tnum)
        requires n.inv(), d > 0, d <= exp(w), q.inv(), r.inv(),
                 forall|j: nat| #![auto] j < i ==> bit(q.val, j) == Bit::f() && bit(q.mask, j) == Bit::f()
        ensures forall|nv: nat, qv: nat, rv: nat| #![auto]
            n.has(nv) && q.has(qv) && r.has(rv) && rv < d ==>
            ({
                let (fq, fr) = div1(nv, d, qv, rv, i);
                let (aq, ar) = Self::div_const_loop(n, d, w, i, q, r);
                aq.has(fq) && ar.has(fr)
            })
        decreases i
    {
        if i == 0 {
        } else {
            let i1 = (i - 1) as nat;
            let nbit = TBit { val: bit(n.val, i1), mask: bit(n.mask, i1) };
            let r1 = r.lsh_or_tb(nbit);
            assert(!nbit.val.b() || !nbit.mask.b()) by { disj_bits(n.val, n.mask); };
            disj_cons(r.val, nbit.val, r.mask, nbit.mask);

            if r1.min() >= d {
                let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                let r2 = r1.sub_const(d, w + 1);
                assert(bit(q.mask, i1) == Bit::f());
                assert forall|j: nat| #![auto] !(bit(bw_or(q.val, exp(i1)), j).b() && bit(q.mask, j).b()) by {
                    or_bit(q.val, exp(i1), j); disj_bits(q.val, q.mask); bit_exp(i1, j);
                };
                disj_bits(bw_or(q.val, exp(i1)), q.mask);
                assert forall|j: nat| #![auto] !(bit(twos_comp(d, w + 1), j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
                disj_bits(twos_comp(d, w + 1), 0);
                Self::add_bitwise_inv(r1, Tnum::unit(twos_comp(d, w + 1)));
                r1.add_bitwise(Tnum::unit(twos_comp(d, w + 1))).chop_sound(w + 1);
                assert forall|j: nat| #![auto] j < i1 ==> bit(q1.val, j) == Bit::f() && bit(q1.mask, j) == Bit::f() by {
                    or_bit(q.val, exp(i1), j); bit_exp(i1, j);
                };
                // IH call for subtract case
                Self::div_const_loop_sound(n, d, w, i1, q1, r2);
            } else if r1.max() < d {
                assert forall|j: nat| #![auto] j < i1 ==> bit(q.val, j) == Bit::f() && bit(q.mask, j) == Bit::f() by {};
                Self::div_const_loop_sound(n, d, w, i1, q, r1);
            } else {
                let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                let r_sub = r1.sub_const(d, w + 1);
                let r2 = r1.join(r_sub);
                assert(bit(q.val, i1) == Bit::f());
                assert forall|j: nat| #![auto] !(bit(q.val, j).b() && bit(bw_or(q.mask, exp(i1)), j).b()) by {
                    or_bit(q.mask, exp(i1), j); disj_bits(q.val, q.mask); bit_exp(i1, j);
                };
                disj_bits(q.val, bw_or(q.mask, exp(i1)));
                assert forall|j: nat| #![auto] !(bit(twos_comp(d, w + 1), j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
                disj_bits(twos_comp(d, w + 1), 0);
                Self::add_bitwise_inv(r1, Tnum::unit(twos_comp(d, w + 1)));
                r1.add_bitwise(Tnum::unit(twos_comp(d, w + 1))).chop_sound(w + 1);
                r1.join_inv(r_sub);
                assert forall|j: nat| #![auto] j < i1 ==> bit(q1.val, j) == Bit::f() && bit(q1.mask, j) == Bit::f() by {
                    or_bit(q.mask, exp(i1), j); bit_exp(i1, j);
                };
                // r2 = join(r1, r_sub). IH call for uncertain case.
                Self::div_const_loop_sound(n, d, w, i1, q1, r2);
            }
            // Connect IH to postcondition via explicit case analysis
            assert forall|nv: nat, qv: nat, rv: nat| #![auto]
                n.has(nv) && q.has(qv) && r.has(rv) && rv < d
                implies ({
                    let (fq, fr) = div1(nv, d, qv, rv, i);
                    let (aq, ar) = Self::div_const_loop(n, d, w, i, q, r);
                    aq.has(fq) && ar.has(fr)
                }) by {
                let bv = bit(nv, i1);
                let r1_c = cons(rv, bv);
                n.has_equiv(nv);
                assert(nbit.has(bv)) by { and_not_bit(nv, n.mask, i1); };
                r.lsh_or_tb_sound(nbit);
                assert(r1.has(r1_c));
                hd_cons(rv, bv);
                nat_add_carry_correct(lsh(rv), bv.n(), Bit::f());
                if r1.min() >= d {
                    r1.has_bounds(r1_c);
                    let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                    let r2 = r1.sub_const(d, w + 1);
                    q.has_equiv(qv);
                    q1.has_equiv(bw_or(qv, exp(i1)));
                    assert forall|j: nat| #![auto] bit(bw_and_not(bw_or(qv, exp(i1)), q.mask), j) == bit(bw_or(q.val, exp(i1)), j) by {
                        and_not_bit(bw_or(qv, exp(i1)), q.mask, j);
                        and_not_bit(qv, q.mask, j);
                        or_bit(qv, exp(i1), j);
                        or_bit(q.val, exp(i1), j);
                        bit_exp(i1, j);
                    };
                    eq_from_bits(bw_and_not(bw_or(qv, exp(i1)), q.mask), bw_or(q.val, exp(i1)));
                    assert(q1.has(bw_or(qv, exp(i1))));
                    // r1_c < exp(w+1): rv < d <= exp(w), so r1_c = 2*rv+bv < 2*exp(w) = exp(w+1)
                    nat_add_carry_correct(rv, rv, Bit::f());
                    exp_pos(w);
                    assert(r1_c < exp(w + 1));
                    r1.sub_const_sound(d, w + 1);
                    assert(r2.has((r1_c - d) as nat));
                    // r2_c = r1_c - d < d (since r1_c < 2*d from rv < d)
                    let r2_c = (r1_c - d) as nat;
                    assert(r2_c < d);
                } else if r1.max() < d {
                    r1.has_bounds(r1_c);
                    // r2_c = r1_c < d (since r1.max() < d)
                } else {
                    let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                    let r_sub = r1.sub_const(d, w + 1);
                    let r2 = r1.join(r_sub);
                    r1.join_sound(r_sub);
                    q.has_equiv(qv);
                    // r1_c < exp(w+1)
                    nat_add_carry_correct(rv, rv, Bit::f());
                    exp_pos(w);
                    assert(r1_c < exp(w + 1));
                    r1.sub_const_sound(d, w + 1);
                    if r1_c >= d {                        q1.has_equiv(bw_or(qv, exp(i1)));
                        assert forall|j: nat| #![auto] bit(bw_and_not(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1))), j) == bit(q.val, j) by {
                            and_not_bit(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1)), j);
                            or_bit(qv, exp(i1), j); or_bit(q.mask, exp(i1), j);
                            bit_exp(i1, j); and_not_bit(qv, q.mask, j);
                        };
                        eq_from_bits(bw_and_not(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1))), q.val);
                        assert(q1.has(bw_or(qv, exp(i1))));
                        assert(r2.has((r1_c - d) as nat));
                        let r2_c2 = (r1_c - d) as nat;
                        assert(r2_c2 < d);
                    } else {
                        q1.has_equiv(qv);
                        assert forall|j: nat| #![auto] bit(bw_and_not(qv, bw_or(q.mask, exp(i1))), j) == bit(q.val, j) by {
                            and_not_bit(qv, bw_or(q.mask, exp(i1)), j);
                            or_bit(q.mask, exp(i1), j); bit_exp(i1, j);
                            and_not_bit(qv, q.mask, j);
                        };
                        eq_from_bits(bw_and_not(qv, bw_or(q.mask, exp(i1))), q.val);
                        assert(q1.has(qv));
                        assert(r2.has(r1_c));
                        // r1_c < d (since r1_c < d in this branch)
                    }
                }
            };
        }
    }
    // ================================================================
    // General division: Tnum / Tnum via iterated subtraction
    // ================================================================

    /// Two's complement negation of a Tnum (w-bit).
    pub open spec fn neg_tn(self, w: nat) -> Tnum {
        self.bw_xor(Tnum::unit(all_ones(w))).add_bitwise(Tnum::unit(1)).chop_tn(w)
    }

    /// Abstract subtraction of Tnum from Tnum (w-bit).
    pub open spec fn sub(self, t: Tnum, w: nat) -> Tnum {
        self.add_bitwise(t.neg_tn(w)).chop_tn(w)
    }

    /// Soundness of neg_tn.
    pub proof fn neg_tn_sound(self, w: nat)
        requires self.inv(), w > 0
        ensures forall|y: nat| #![auto]
            self.has(y) && y > 0 && y < exp(w) ==>
            self.neg_tn(w).has(twos_comp(y, w))
    {
        let ones_tn = Tnum::unit(all_ones(w));
        // ones_tn.inv(): disj(all_ones(w), 0)
        assert forall|j: nat| #![auto] !(bit(all_ones(w), j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(all_ones(w), 0);
        self.xor_sound(ones_tn);
        let flipped = self.bw_xor(ones_tn);
        // flipped.val = andnot(xor(self.val, all_ones(w)), or(self.mask, 0)) = andnot(xor(self.val, all_ones(w)), self.mask)
        // flipped.mask = or(self.mask, 0) = self.mask
        // disj(andnot(x, m), m) is always true
        assert forall|i: nat| #![auto] !(bit(flipped.val, i).b() && bit(flipped.mask, i).b()) by {
            or_bit(self.mask, 0 as nat, i);
            bit_zero(i);
            and_not_bit(bw_xor(self.val, all_ones(w)), bw_or(self.mask, 0), i);
        };
        disj_bits(flipped.val, flipped.mask);
        // unit(1).inv()
        assert forall|j: nat| #![auto] !(bit(1 as nat, j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(1 as nat, 0);
        flipped.add_sound(Tnum::unit(1));
        flipped.add_bitwise_eq(Tnum::unit(1));
        let sum = flipped.add_bitwise(Tnum::unit(1));
        Self::add_bitwise_inv(flipped, Tnum::unit(1));
        // unit(1).has(1)
        Tnum::unit(1).has_equiv(1 as nat);
        assert forall|i: nat| #![auto] bit(bw_and_not(1 as nat, 0 as nat), i) == bit(1 as nat, i) by {
            and_not_bit(1, 0, i); bit_zero(i);
        };
        eq_from_bits(bw_and_not(1, 0), 1);
        assert forall|y: nat| #![auto]
            self.has(y) && y > 0 && y < exp(w)
            implies self.neg_tn(w).has(twos_comp(y, w)) by {
            assert(flipped.has(bw_xor(y, all_ones(w)))) by {
                ones_tn.has_equiv(all_ones(w));
                assert forall|i: nat| #![auto] bit(bw_and_not(all_ones(w), 0 as nat), i) == bit(all_ones(w), i) by {
                    and_not_bit(all_ones(w), 0, i); bit_zero(i);
                };
                eq_from_bits(bw_and_not(all_ones(w), 0), all_ones(w));
            };
            assert(Tnum::unit(1).has(1 as nat)) by {
                Tnum::unit(1).has_equiv(1 as nat);
                assert forall|i: nat| #![auto] bit(bw_and_not(1 as nat, 0 as nat), i) == bit(1 as nat, i) by {
                    and_not_bit(1, 0, i); bit_zero(i);
                };
                eq_from_bits(bw_and_not(1, 0), 1);
            };
            nat_add_carry_correct(bw_xor(y, all_ones(w)), 1, Bit::f());
            // neg_tn(w) == sum.chop_tn(w)
            assert(self.neg_tn(w) == sum.chop_tn(w));
            // twos_comp(y, w) = exp(w) - y = bw_xor(y, all_ones(w)) + 1
            xor_ones_complement(y, w);
            exp_pos(w);
            // sum.has(nat_add(bw_xor(y, all_ones(w)), 1)) = sum.has(exp(w) - y) = sum.has(twos_comp(y, w))
            assert(nat_add(bw_xor(y, all_ones(w)), 1) == twos_comp(y, w));
            assert(sum.has(twos_comp(y, w)));
            // chop_sound: sum.chop_tn(w).has(chop(twos_comp(y, w), w))
            sum.chop_sound(w);
            // chop(twos_comp(y, w), w) = twos_comp(y, w) since twos_comp(y, w) < exp(w)
            chop_id(twos_comp(y, w), w);
        };
    }

    /// Soundness of sub_tn.
    pub proof fn sub_sound(self, t: Tnum, w: nat)
        requires self.inv(), t.inv(), w > 0
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) && x >= y && y > 0 && x < exp(w) && y < exp(w) ==>
            self.sub(t, w).has(chop((x - y) as nat, w))
    {
        t.neg_tn_sound(w);
        let neg_t = t.neg_tn(w);
        // neg_t.inv(): neg_tn = chop_tn(add_bitwise(flipped, unit(1)), w)
        // flipped.inv() (from xor with unit(all_ones(w)))
        let ones_tn = Tnum::unit(all_ones(w));
        assert forall|j: nat| #![auto] !(bit(all_ones(w), j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(all_ones(w), 0);
        let flipped = t.bw_xor(ones_tn);
        assert forall|i: nat| #![auto] !(bit(flipped.val, i).b() && bit(flipped.mask, i).b()) by {
            or_bit(t.mask, 0 as nat, i); bit_zero(i); and_not_bit(bw_xor(t.val, all_ones(w)), bw_or(t.mask, 0), i);
        };
        disj_bits(flipped.val, flipped.mask);
        assert forall|j: nat| #![auto] !(bit(1 as nat, j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(1 as nat, 0);
        Self::add_bitwise_inv(flipped, Tnum::unit(1));
        flipped.add_bitwise(Tnum::unit(1)).chop_sound(w);
        assert(neg_t.inv());
        self.add_bitwise_eq(neg_t);
        self.add_sound(neg_t);
        let sum = self.add_bitwise(neg_t);
        Self::add_bitwise_inv(self, neg_t);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) && x >= y && y > 0 && x < exp(w) && y < exp(w)
            implies self.sub(t, w).has(chop((x - y) as nat, w)) by {
            assert(neg_t.has(twos_comp(y, w)));
            assert(sum.has(nat_add(x, twos_comp(y, w))));
            sum.chop_sound(w);
            nat_add_carry_correct(x, twos_comp(y, w), Bit::f());
            let nd = (x - y) as nat;
            nat_add_carry_correct(nd, exp(w), Bit::f());
            exp_pos(w);
            assert(nat_add(x, twos_comp(y, w)) == nat_add(nd, exp(w)));
            chop_nat_add_pow2(nd, w);
            chop_id(nd, w);
        };
    }

    /// sub_tn preserves inv.
    pub proof fn sub_inv(self, t: Tnum, w: nat)
        requires self.inv(), t.inv(), w > 0
        ensures self.sub(t, w).inv()
    {
        let ones_tn = Tnum::unit(all_ones(w));
        assert forall|j: nat| #![auto] !(bit(all_ones(w), j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(all_ones(w), 0);
        let flipped = t.bw_xor(ones_tn);
        assert forall|i: nat| #![auto] !(bit(flipped.val, i).b() && bit(flipped.mask, i).b()) by {
            or_bit(t.mask, 0 as nat, i); bit_zero(i); and_not_bit(bw_xor(t.val, all_ones(w)), bw_or(t.mask, 0), i);
        };
        disj_bits(flipped.val, flipped.mask);
        assert forall|j: nat| #![auto] !(bit(1 as nat, j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
        disj_bits(1 as nat, 0);
        Self::add_bitwise_inv(flipped, Tnum::unit(1));
        flipped.add_bitwise(Tnum::unit(1)).chop_sound(w);
        let neg_t = t.neg_tn(w);
        assert(neg_t.inv());
        Self::add_bitwise_inv(self, neg_t);
        self.add_bitwise(neg_t).chop_sound(w);
    }

    /// General division: Tnum / Tnum using w-bit long division.
    pub open spec fn div(self, t: Tnum, w: nat) -> (Tnum, Tnum) {
        Self::div_loop(self, t, w, w, Tnum::zero(), Tnum::zero())
    }

    pub open spec fn div_loop(n: Tnum, d: Tnum, w: nat, i: nat, q: Tnum, r: Tnum) -> (Tnum, Tnum)
        decreases i
    {
        if i == 0 { (q, r) }
        else {
            let i1 = (i - 1) as nat;
            let nbit = TBit { val: bit(n.val, i1), mask: bit(n.mask, i1) };
            let r1 = r.lsh_or_tb(nbit);
            if r1.min() >= d.max() {
                let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                let r2 = r1.sub(d, w + 1);
                Self::div_loop(n, d, w, i1, q1, r2)
            } else if r1.max() < d.min() {
                Self::div_loop(n, d, w, i1, q, r1)
            } else {
                let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                let r_sub = r1.sub(d, w + 1);
                let r2 = r1.join(r_sub);
                Self::div_loop(n, d, w, i1, q1, r2)
            }
        }
    }

    /// Soundness of general Tnum division.
    pub proof fn div_sound(self, t: Tnum, w: nat)
        requires self.inv(), t.inv(), t.min() > 0, t.max() < exp(w)
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==>
            self.div(t, w).0.has(div1(x, y, 0, 0, w).0)
    {
        let z = Tnum::zero();
        disj_zero(0 as nat);
        assert forall|j: nat| #![auto] j < w ==> bit(z.val, j) == Bit::f() && bit(z.mask, j) == Bit::f() by {
            bit_zero(j);
        };
        Self::div_loop_sound(self, t, w, w, z, z);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.div(t, w).0.has(div1(x, y, 0, 0, w).0) by {
            assert(z.has(0 as nat));
            assert((0 as nat) < y) by { t.has_bounds(y); };
        };
    }

    #[verifier::rlimit(5000)]
    proof fn div_loop_sound(n: Tnum, d: Tnum, w: nat, i: nat, q: Tnum, r: Tnum)
        requires n.inv(), d.inv(), d.min() > 0, d.max() < exp(w), q.inv(), r.inv(),
                 forall|j: nat| #![auto] j < i ==> bit(q.val, j) == Bit::f() && bit(q.mask, j) == Bit::f()
        ensures forall|nv: nat, dv: nat, qv: nat, rv: nat| #![auto]
            n.has(nv) && d.has(dv) && q.has(qv) && r.has(rv) && rv < dv ==>
            ({
                let (fq, fr) = div1(nv, dv, qv, rv, i);
                let (aq, ar) = Self::div_loop(n, d, w, i, q, r);
                aq.has(fq) && ar.has(fr)
            })
        decreases i
    {
        if i == 0 {
        } else {
            let i1 = (i - 1) as nat;
            let nbit = TBit { val: bit(n.val, i1), mask: bit(n.mask, i1) };
            let r1 = r.lsh_or_tb(nbit);
            assert(!nbit.val.b() || !nbit.mask.b()) by { disj_bits(n.val, n.mask); };
            disj_cons(r.val, nbit.val, r.mask, nbit.mask);

            if r1.min() >= d.max() {
                let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                let r2 = r1.sub(d, w + 1);
                assert(bit(q.mask, i1) == Bit::f());
                assert forall|j: nat| #![auto] !(bit(bw_or(q.val, exp(i1)), j).b() && bit(q.mask, j).b()) by {
                    or_bit(q.val, exp(i1), j); disj_bits(q.val, q.mask); bit_exp(i1, j);
                };
                disj_bits(bw_or(q.val, exp(i1)), q.mask);
                assert forall|j: nat| #![auto] j < i1 ==> bit(q1.val, j) == Bit::f() && bit(q1.mask, j) == Bit::f() by {
                    or_bit(q.val, exp(i1), j); bit_exp(i1, j);
                };
                r1.sub_inv(d, w + 1);
                Self::div_loop_sound(n, d, w, i1, q1, r2);
            } else if r1.max() < d.min() {
                assert forall|j: nat| #![auto] j < i1 ==> bit(q.val, j) == Bit::f() && bit(q.mask, j) == Bit::f() by {};
                Self::div_loop_sound(n, d, w, i1, q, r1);
            } else {
                let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                let r_sub = r1.sub(d, w + 1);
                let r2 = r1.join(r_sub);
                assert(bit(q.val, i1) == Bit::f());
                assert forall|j: nat| #![auto] !(bit(q.val, j).b() && bit(bw_or(q.mask, exp(i1)), j).b()) by {
                    or_bit(q.mask, exp(i1), j); disj_bits(q.val, q.mask); bit_exp(i1, j);
                };
                disj_bits(q.val, bw_or(q.mask, exp(i1)));
                r1.sub_inv(d, w + 1);
                r1.join_inv(r_sub);
                assert forall|j: nat| #![auto] j < i1 ==> bit(q1.val, j) == Bit::f() && bit(q1.mask, j) == Bit::f() by {
                    or_bit(q.mask, exp(i1), j); bit_exp(i1, j);
                };
                Self::div_loop_sound(n, d, w, i1, q1, r2);
            }

            assert forall|nv: nat, dv: nat, qv: nat, rv: nat| #![auto]
                n.has(nv) && d.has(dv) && q.has(qv) && r.has(rv) && rv < dv
                implies ({
                    let (fq, fr) = div1(nv, dv, qv, rv, i);
                    let (aq, ar) = Self::div_loop(n, d, w, i, q, r);
                    aq.has(fq) && ar.has(fr)
                }) by {
                let bv = bit(nv, i1);
                let r1_c = cons(rv, bv);
                n.has_equiv(nv);
                assert(nbit.has(bv)) by { and_not_bit(nv, n.mask, i1); };
                r.lsh_or_tb_sound(nbit);
                assert(r1.has(r1_c));
                hd_cons(rv, bv);
                nat_add_carry_correct(lsh(rv), bv.n(), Bit::f());

                if r1.min() >= d.max() {
                    r1.has_bounds(r1_c); d.has_bounds(dv);
                    assert(r1_c >= dv);
                    let q1 = Tnum { val: bw_or(q.val, exp(i1)), mask: q.mask };
                    let r2 = r1.sub(d, w + 1);
                    q.has_equiv(qv);
                    q1.has_equiv(bw_or(qv, exp(i1)));
                    assert forall|j: nat| #![auto] bit(bw_and_not(bw_or(qv, exp(i1)), q.mask), j) == bit(bw_or(q.val, exp(i1)), j) by {
                        and_not_bit(bw_or(qv, exp(i1)), q.mask, j);
                        and_not_bit(qv, q.mask, j);
                        or_bit(qv, exp(i1), j); or_bit(q.val, exp(i1), j);
                        bit_exp(i1, j);
                    };
                    eq_from_bits(bw_and_not(bw_or(qv, exp(i1)), q.mask), bw_or(q.val, exp(i1)));
                    exp_pos(w);
                    d.has_bounds(dv); assert(dv < exp(w)); assert(r1_c < exp(w + 1));
                    r1.sub_sound(d, w + 1);
                    chop_id(((r1_c - dv) as nat), w + 1);
                } else if r1.max() < d.min() {
                    r1.has_bounds(r1_c); d.has_bounds(dv);
                } else {
                    let q1 = Tnum { val: q.val, mask: bw_or(q.mask, exp(i1)) };
                    let r_sub = r1.sub(d, w + 1);
                    let r2 = r1.join(r_sub);
                    r1.join_sound(r_sub);
                    q.has_equiv(qv);
                    exp_pos(w);
                    d.has_bounds(dv); assert(dv < exp(w)); assert(r1_c < exp(w + 1));
                    r1.sub_sound(d, w + 1);
                    if r1_c >= dv {
                        q1.has_equiv(bw_or(qv, exp(i1)));
                        assert forall|j: nat| #![auto] bit(bw_and_not(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1))), j) == bit(q.val, j) by {
                            and_not_bit(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1)), j);
                            or_bit(qv, exp(i1), j); or_bit(q.mask, exp(i1), j);
                            bit_exp(i1, j); and_not_bit(qv, q.mask, j);
                        };
                        eq_from_bits(bw_and_not(bw_or(qv, exp(i1)), bw_or(q.mask, exp(i1))), q.val);
                        chop_id(((r1_c - dv) as nat), w + 1);
                    } else {
                        q1.has_equiv(qv);
                        assert forall|j: nat| #![auto] bit(bw_and_not(qv, bw_or(q.mask, exp(i1))), j) == bit(q.val, j) by {
                            and_not_bit(qv, bw_or(q.mask, exp(i1)), j);
                            or_bit(q.mask, exp(i1), j); bit_exp(i1, j);
                            and_not_bit(qv, q.mask, j);
                        };
                        eq_from_bits(bw_and_not(qv, bw_or(q.mask, exp(i1))), q.val);
                    }
                }
            };
        }
    }
}

} // verus!
