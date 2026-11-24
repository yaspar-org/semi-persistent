// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Additive tristate numbers (Anums).
//!
//! has(x) <==> v <= x && Tn(0, m).has(x - v)

use crate::bools::Bit;
use crate::nats::*;
use crate::tbit::TBit;
use crate::tnum::Tnum;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Anum { pub base: nat, pub span: nat }

impl Anum {
    pub open spec fn mask_tnum(self) -> Tnum { Tnum::ctor(0, self.span) }
    pub open spec fn val_tnum(self) -> Tnum { Tnum::ctor(self.base, 0) }
    pub open spec fn to_tnum(self) -> Tnum { self.mask_tnum().add(self.val_tnum()) }
    pub open spec fn is_zero(self) -> bool { self.base == 0 && self.span == 0 }
    pub open spec fn size(self) -> nat { self.base + self.span }
    pub open spec fn zero() -> Anum { Anum { base: 0, span: 0 } }

    pub open spec fn has(self, x: nat) -> bool {
        x >= self.base && self.mask_tnum().has(nat_sub(x, self.base))
    }

    pub open spec fn from_tnum(t: Tnum) -> Anum { Anum { base: t.val, span: t.mask } }

    /// Subtraction of a smaller Anum: the base subtracts the other's maximum and
    /// the span is the same as for add, since y's offset d2 turns into the
    /// offset span - d2, again a bit subset of span.
    pub open spec fn sub(self, a: Anum) -> Anum {
        Anum {
            base: (self.base - nat_add(a.base, a.span)) as nat,
            span: self.mask_tnum().add(a.mask_tnum()).mask,
        }
    }

    pub proof fn sub_sound(self, a: Anum)
        requires self.base >= nat_add(a.base, a.span)
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && a.has(y) ==> self.sub(a).has((x - y) as nat)
    {
        nat_add_correct(a.base, a.span);
        let ms = self.mask_tnum();
        let ma = a.mask_tnum();
        let sum = ms.add(ma);
        ms.add_sound(ma);
        ms.add_carry_val_zero(ma, TBit { val: Bit::f(), mask: Bit::f() });
        assert(sum == Tnum::ctor(0, sum.mask));
        assert forall|x: nat, y: nat| #![auto] self.has(x) && a.has(y) implies self.sub(a).has((x - y) as nat) by {
            a.has_le_max(y);
            let d1 = (x - self.base) as nat;
            let d2 = (y - a.base) as nat;
            // d2 is a bit subset of a.span, so a.span - d2 is one too.
            ma.has_equiv(d2);
            sub_submask(a.span, d2);
            let e2 = (a.span - d2) as nat;
            ma.has_equiv(e2);
            assert(ms.has(d1) && ma.has(e2));
            assert(sum.has(nat_add(d1, e2)));
            nat_add_correct(d1, e2);
            assert((x - y) - self.sub(a).base == d1 + e2);
        };
    }

    /// Every member is at most base + span.
    pub proof fn has_le_max(self, x: nat)
        requires self.has(x)
        ensures x <= self.base + self.span
    {
        let d = nat_sub(x, self.base);
        self.mask_tnum().has_equiv(d);
        and_not_zero_le(d, self.span);
    }

    /// to_tnum is well formed for every Anum.
    pub proof fn to_tnum_inv(self)
        ensures self.to_tnum().inv()
    {
        disj_zero(self.span);
        disj_zero_r(self.base);
        self.mask_tnum().add_inv(self.val_tnum());
    }

    /// Key lemma: hasMinus — if Tn(v,m).has(n) then Tn(0,m).has(n - v)
    pub proof fn from_tnum_sound(t: Tnum)
        requires t.inv()
        ensures forall|n: nat| #![auto] t.has(n) ==> Anum::from_tnum(t).has(n)
    {
        assert forall|n: nat| #![auto] t.has(n) implies Anum::from_tnum(t).has(n) by {
            t.has_equiv(n);
            // t.has(n) <==> andnot(n, m) == v
            // Need: n >= v and Tn(0, m).has(n - v)
            // Tn(0,m).has(n-v) <==> andnot(n-v, m) == 0
            // From andnot(n, m) == v:
            //   n == v | (n & m)  [since n & !m == v means n = v on non-masked bits, free on masked bits]
            //   n - v == n & m    [the masked bits]
            //   andnot(n & m, m) == 0  [trivially, since (n&m) & !m == 0]
            // So n >= v and andnot(n-v, m) == 0.
            // This requires showing n >= v and n - v == bw_and(n, m).
            Anum::has_minus(t, n);
        };
    }

    proof fn has_minus(t: Tnum, n: nat)
        requires t.inv(), t.has(n)
        ensures n >= t.val, Tnum::ctor(0, t.mask).has(nat_sub(n, t.val))
        decreases t.size()
    {
        t.has_equiv(n);
        Tnum::ctor(0, t.mask).has_equiv(nat_sub(n, t.val));
        // andnot(n, m) == v, disj(v, m)
        // Need: n >= v and andnot(n - v, m) == 0

        // n >= v: since andnot(n, m) == v, every bit of v is a bit of n (on unmasked positions)
        // and v has no bits where m has bits (disj). So v <= n.
        // Formally: v == andnot(n, m), and n == v | (n & m), so n == v + (n & m) >= v
        // since n & m >= 0.
        // We prove this via plus_or: v and (n & m) are disjoint, so v + (n&m) == v | (n&m) == n

        // First: n == or(v, and(n, m))
        assert forall|i: nat| #![auto] bit(n, i) == bit(bw_or(t.val, bw_and(n, t.mask)), i) by {
            and_not_bit(n, t.mask, i);
            and_bit(n, t.mask, i);
            or_bit(t.val, bw_and(n, t.mask), i);
        };
        eq_from_bits(n, bw_or(t.val, bw_and(n, t.mask)));

        // v and (n & m) are disjoint
        disj_bits(t.val, bw_and(n, t.mask));
        assert forall|i: nat| #![auto] !(bit(t.val, i).b() && bit(bw_and(n, t.mask), i).b()) by {
            and_not_bit(n, t.mask, i);
            and_bit(n, t.mask, i);
            disj_bits(t.val, t.mask);
        };
        disj_bits(t.val, bw_and(n, t.mask));

        // So n == v + (n & m) by plus_or
        nat_add_or(t.val, bw_and(n, t.mask));
        nat_add_correct(t.val, bw_and(n, t.mask));
        // n == nat_add(v, and(n,m)) == v + and(n,m)
        assert(n >= t.val);

        // n - v == and(n, m)
        assert(nat_sub(n, t.val) == bw_and(n, t.mask));

        // andnot(and(n,m), m) == 0
        assert forall|i: nat| #![auto] bit(bw_and_not(bw_and(n, t.mask), t.mask), i) == bit(0 as nat, i) by {
            and_bit(n, t.mask, i);
            and_not_bit(bw_and(n, t.mask), t.mask, i);
            bit_zero(i);
        };
        eq_from_bits(bw_and_not(bw_and(n, t.mask), t.mask), 0);
    }

    pub open spec fn add(self, a: Anum) -> Anum {
        Anum { base: nat_add(self.base, a.base), span: self.mask_tnum().add(a.mask_tnum()).mask,
        }
    }

    pub proof fn add_sound(self, a: Anum)
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && a.has(y) ==> self.add(a).has(nat_add(x, y))
    {
        assert forall|x: nat, y: nat| #![auto] self.has(x) && a.has(y)
            implies self.add(a).has(nat_add(x, y)) by {
            // Unpack membership
            let dx = nat_sub(x, self.base);  // x - self.base
            let dy = nat_sub(y, a.base);     // y - a.base
            assert(self.mask_tnum().has(dx));
            assert(a.mask_tnum().has(dy));

            // Tnum plus is sound
            self.mask_tnum().add_sound(a.mask_tnum());
            assert(self.mask_tnum().add(a.mask_tnum()).has(nat_add(dx, dy)));

            // add of Tn(0,_) and Tn(0,_) has v == 0
            self.tm_plus_v_zero(a.mask_tnum());
            let result_tn = self.mask_tnum().add(a.mask_tnum());
            assert(result_tn.val == 0);
            // So result_tn == Tn(0, result_tn.mask) == Tn(0, self.add(a).mask)

            // Arithmetic: dx + dy == (x + y) - (sv + av)
            nat_add_correct(dx, dy);
            nat_add_correct(x, y);
            nat_add_correct(self.base, a.base);
            assert(dx + dy == (x + y) - (self.base + a.base));
            assert(nat_add(dx, dy) == dx + dy);
            assert(nat_add(x, y) == x + y);
            assert(nat_add(self.base, a.base) == self.base + a.base);

            // nat_add(x,y) >= nat_add(sv, av)
            assert(nat_add(x, y) >= nat_add(self.base, a.base));

            // Tn(0, result.mask).has(nat_add(x,y) - nat_add(sv, av))
            // == result_tn.has(nat_add(dx, dy))  [since result_tn.val == 0]
            // which we already have
            assert(nat_sub(nat_add(x, y), nat_add(self.base, a.base)) == nat_add(dx, dy));
        };
    }

    /// When both inputs have v=0, add result has v=0.
    proof fn tm_plus_v_zero(self, t: Tnum)
        requires self.mask_tnum().val == 0, t.val == 0
        ensures self.mask_tnum().add(t).val == 0
    {
        self.mask_tnum().add_carry_val_zero(t, TBit { val: Bit::f(), mask: Bit::f() });
    }

    /// add(zero) == self
    pub proof fn add_zero(self)
        ensures self.add(Anum::zero()) == self
    {
        nat_add_correct(self.base, 0);
        // tm() = Tn(0, self.span) has inv because disj(0, anything)
        disj_zero(self.span);
        self.mask_tnum().add_carry_zero();
    }

    /// a.has(z) ==> a.to_tnum().has(z)
    pub proof fn tnum_has_from_anum(a: Anum, z: nat)
        requires a.has(z)
        ensures a.to_tnum().has(z)
    {
        // a.to_tnum() = tm.add(tv), tm = Tn(0, a.span), tv = Tn(a.base, 0)
        // a.has(z) means z >= a.base and tm.has(z - a.base)
        // tv.has(a.base) since andnot(a.base, 0) == a.base
        a.val_tnum().has_equiv(a.base);
        assert forall|i: nat| #![auto] bit(bw_and_not(a.base, 0 as nat), i) == bit(a.base, i) by {
            and_not_bit(a.base, 0, i);
            bit_zero(i);
        };
        eq_from_bits(bw_and_not(a.base, 0), a.base);
        // tm.has(z - a.base) && tv.has(a.base) ==> add result has nat_add(z-a.base, a.base) == z
        a.mask_tnum().add_sound(a.val_tnum());
        nat_add_correct(nat_sub(z, a.base), a.base);
    }

    /// Step: the new accumulator contains nat_add(z, nat_mul_bit(y, hd(x)))
    proof fn mul_step_acc(t: Tnum, hd_t0: TBit, a: Anum, x: nat, y: nat, z: nat)
        requires t.inv(), t.has(y), a.has(z), hd_t0.has(hd(x))
        ensures a.add(Anum::from_tnum(t.mul_bit(hd_t0))).has(nat_add(z, nat_mul_bit(y, hd(x))))
            // when t0.head().has(hd(x)) — but we state it for any hd_t0 matching
    {
        // mul_bit_sound: t.has(y) && hd_t0.has(hd(x)) ==> t.mul_bit(hd_t0).has(nat_mul_bit(y, hd(x)))
        // But we need hd_t0.has(hd(x)) which comes from t0.has(x)
        // This helper is called with the right hd_t0, so we just need the chain
        t.mul_bit_sound(hd_t0);
        t.times_b_inv(hd_t0);
        Anum::from_tnum_sound(t.mul_bit(hd_t0));
        a.add_sound(Anum::from_tnum(t.mul_bit(hd_t0)));
    }

    /// rsh preserves inv
    pub proof fn rsh_inv(t: Tnum)
        requires t.inv()
        ensures t.rsh().inv()
    {
        disj_bits(t.val, t.mask);
        assert forall|i: nat| #![auto] !(bit(tl(t.val), i).b() && bit(tl(t.mask), i).b()) by {
            bit_tl(t.val, i);
            bit_tl(t.mask, i);
        };
        disj_bits(tl(t.val), tl(t.mask));
    }

    /// lsh preserves inv
    pub proof fn lsh_inv(t: Tnum)
        requires t.inv()
        ensures t.lsh().inv()
    {
        disj_bits(t.val, t.mask);
        assert forall|i: nat| #![auto] !(bit(lsh(t.val), i).b() && bit(lsh(t.mask), i).b()) by {
            bit_cons(t.val, Bit::f(), i);
            bit_cons(t.mask, Bit::f(), i);
        };
        disj_bits(lsh(t.val), lsh(t.mask));
    }

    /// times1 unfolds: nat_mul_acc(x, y, z) == nat_mul_acc(tl(x), lsh(y), nat_add(z, nat_mul_bit(y, hd(x))))
    proof fn times1_unfold(x: nat, y: nat, z: nat)
        ensures nat_mul_acc(x, y, z) == nat_mul_acc(tl(x), lsh(y), nat_add(z, nat_mul_bit(y, hd(x))))
    {
        if x == 0 {
            // nat_mul_acc(0, y, z) == z
            // tl(0) == 0, hd(0) == F, nat_mul_bit(y, F) == 0, nat_add(z, 0) == z
            // nat_mul_acc(0, lsh(y), nat_add(z, 0)) == nat_add(z, 0) == z
            nat_add_correct(z, 0);
        }
        // else: direct from definition
    }

    // ================================================================
    // Anum-level multiplication: Anum × An → An (preserves additive structure)
    // ================================================================

    /// Anum multiplication loop: shift-and-add with an Anum accumulator.
    /// The accumulator stays as An throughout, preserving the exact base.
    pub open spec fn mul_step_anum(t0: Tnum, t: Tnum, a: Anum) -> Anum
        decreases t0.size()
    {
        if t0.is_zero() { a }
        else {
            Anum::mul_step_anum(
                t0.rsh(),
                t.lsh(),
                a.add(Anum::from_tnum(t.mul_bit(t0.head()))),
            )
        }
    }

    /// Anum multiplication: Tnum × Tn → An.
    /// Returns An instead of Tnum, preserving the additive structure.
    pub open spec fn mul_anum(t0: Tnum, t1: Tnum) -> Anum {
        Anum::mul_step_anum(t0, t1, Anum::zero())
    }

    /// Soundness of mul_step_anum.
    pub proof fn mul_step_anum_sound(t0: Tnum, t: Tnum, a: Anum)
        requires t0.inv(), t.inv()
        ensures forall|x: nat, y: nat, z: nat| #![auto]
            t0.has(x) && t.has(y) && a.has(z) ==>
            Anum::mul_step_anum(t0, t, a).has(nat_mul_acc(x, y, z))
        decreases t0.size()
    {
        assert forall|x: nat, y: nat, z: nat| #![auto]
            t0.has(x) && t.has(y) && a.has(z)
            implies Anum::mul_step_anum(t0, t, a).has(nat_mul_acc(x, y, z)) by {
            Anum::mul_step_anum_sound1(t0, t, a, x, y, z);
        };
    }

    proof fn mul_step_anum_sound1(t0: Tnum, t: Tnum, a: Anum, x: nat, y: nat, z: nat)
        requires t0.inv(), t.inv(), t0.has(x), t.has(y), a.has(z)
        ensures Anum::mul_step_anum(t0, t, a).has(nat_mul_acc(x, y, z))
        decreases t0.size()
    {
        if t0.is_zero() {
            assert(x == 0);
        } else {
            let tb = t.mul_bit(t0.head());
            Anum::rsh_inv(t0);
            Anum::lsh_inv(t);
            t.times_b_inv(t0.head());
            let a1 = a.add(Anum::from_tnum(tb));
            Anum::from_tnum_sound(tb);
            a.add_sound(Anum::from_tnum(tb));
            t.mul_bit_sound(t0.head());
            t0.rsh_sound();
            t.lsh_sound();
            Anum::times1_unfold(x, y, z);
            Anum::mul_step_acc(t, t0.head(), a, x, y, z);
            Anum::mul_step_anum_sound1(t0.rsh(), t.lsh(), a1, rsh(x), lsh(y), nat_add(z, nat_mul_bit(y, hd(x))));
        }
    }

    /// Soundness of mul_anum.
    pub proof fn mul_anum_sound(t0: Tnum, t1: Tnum)
        requires t0.inv(), t1.inv()
        ensures forall|x: nat, y: nat| #![auto]
            t0.has(x) && t1.has(y) ==> Anum::mul_anum(t0, t1).has(nat_mul_acc(x, y, 0))
    {
        Anum::mul_step_anum_sound(t0, t1, Anum::zero());
    }


    // ================================================================
    // ================================================================
    // Anum subtraction and division
    // ================================================================

    pub open spec fn div_const(self, d: nat) -> Anum
        recommends d > 0
    {
        let min_q = self.base / d;
        let max_q = nat_add(self.base, self.span) / d;
        let range = (max_q - min_q) as nat;
        // Use all_ones(len(range)) to get a proper interval mask
        // all_ones(len(n)) >= n for all n, so this is a sound over-approximation
        Anum { base: min_q, span: all_ones(len(range)) }
    }

    /// Soundness of Anum division by constant.
    pub proof fn div_const_sound(self, d: nat)
        requires d > 0, self.to_tnum().inv()
        ensures forall|x: nat| #![auto]
            self.has(x) ==> self.div_const(d).has(x / d)
    {
        assert forall|x: nat| #![auto]
            self.has(x) implies self.div_const(d).has(x / d) by {
            disj_zero(self.span);
            Tnum::ctor(0, self.span).has_bounds(nat_sub(x, self.base));
            nat_add_carry_correct(self.base, self.span, Bit::f());
            // x/d - self.base/d <= range <= all_ones(len(range))
            let min_q = self.base / d;
            let max_q = nat_add(self.base, self.span) / d;
            let range = (max_q - min_q) as nat;
            let mask = all_ones(len(range));
            assert(x / d >= min_q) by {
                vstd::arithmetic::div_mod::lemma_div_is_ordered(self.base as int, x as int, d as int);
            };
            assert(x / d <= max_q) by {
                nat_add_carry_correct(self.base, self.span, Bit::f());
                let delta = nat_sub(x, self.base);
                // has_bounds: delta <= Tn(0, self.span).max() = bw_or(0, self.span) = self.span
                assert forall|i: nat| #![auto] bit(bw_or(0 as nat, self.span), i) == bit(self.span, i) by {
                    or_bit(0, self.span, i); bit_zero(i);
                };
                eq_from_bits(bw_or(0, self.span), self.span);
                assert(delta <= self.span);
                assert(x == self.base + delta);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, (self.base + self.span) as int, d as int);
            };
            let k = (x / d - min_q) as nat;
            assert(k <= range);
            // all_ones(len(range)) >= range >= k, so k < exp(len(range))
            len_bound(range);
            all_ones_covers(range);
            // k < exp(len(range)), so bw_and_not(k, all_ones(len(range))) == 0
            // which means Tn(0, mask).has(k)
            all_ones_has(k, len(range));
            Tnum::ctor(0, mask).has_equiv(k);
            assert forall|i: nat| #![auto] bit(bw_and_not(k, mask), i) == bit(0 as nat, i) by {
                and_not_bit(k, mask, i);
                bit_zero(i);
            };
            eq_from_bits(bw_and_not(k, mask), 0);
        };
    }

    // ================================================================
    // Shift, reflection and cover
    // ================================================================

    /// Left shift by k: x = base + d with d a bit subset of span gives
    /// x << k = (base << k) + (d << k), and d << k is a bit subset of span << k.
    pub open spec fn lshi(self, k: nat) -> Anum {
        Anum { base: lshi(self.base, k), span: lshi(self.span, k) }
    }

    pub proof fn lshi_sound(self, k: nat)
        ensures forall|x: nat| #![auto] self.has(x) ==> self.lshi(k).has(lshi(x, k))
    {
        self.mask_tnum().lshi_sound(k);
        lsh_exp(0, k);
        assert(self.mask_tnum().lshi(k) == self.lshi(k).mask_tnum());
        assert forall|x: nat| #![auto] self.has(x) implies self.lshi(k).has(lshi(x, k)) by {
            let d = nat_sub(x, self.base);
            lsh_exp(x, k);
            lsh_exp(self.base, k);
            lsh_exp(d, k);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(exp(k) as int, self.base as int, d as int);
            assert(nat_sub(lshi(x, k), lshi(self.base, k)) == lshi(d, k));
        };
    }

    /// Reflection through m >= base + span: m - x for every member x. The
    /// offset span - d of a bit subset d of span is again one (sub_submask).
    pub open spec fn reflect(self, m: nat) -> Anum {
        Anum { base: (m - (self.base + self.span)) as nat, span: self.span }
    }

    pub proof fn reflect_sound(self, m: nat)
        requires self.base + self.span <= m
        ensures forall|x: nat| #![auto] self.has(x) ==> self.reflect(m).has((m - x) as nat)
    {
        assert forall|x: nat| #![auto] self.has(x) implies self.reflect(m).has((m - x) as nat) by {
            self.has_le_max(x);
            let d = nat_sub(x, self.base);
            self.mask_tnum().has_equiv(d);
            sub_submask(self.span, d);
            let e = (self.span - d) as nat;
            self.mask_tnum().has_equiv(e);
            assert(nat_sub((m - x) as nat, self.reflect(m).base) == e);
        };
    }

    /// A member of a Tnum is a bit subset of its maximum val | mask.
    pub proof fn cover(t: Tnum, n: nat)
        requires t.has(n)
        ensures Tnum::ctor(0, t.max()).has(n)
    {
        t.has_equiv(n);
        Tnum::ctor(0, t.max()).has_equiv(n);
        assert forall|i: nat| #![auto] bit(bw_and_not(n, t.max()), i) == bit(0 as nat, i) by {
            and_not_bit(n, t.mask, i);
            or_bit(t.val, t.mask, i);
            and_not_bit(n, t.max(), i);
            bit_zero(i);
        };
        eq_from_bits(bw_and_not(n, t.max()), 0);
    }
}

} // verus!
