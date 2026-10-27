// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Pair-join Tnum multiplication (Layer 2, unbounded).
//!
//! Split the product by the unknown bits of each operand:
//!
//! ```text
//! x * y = x.v * y.v + sum_l v_l * (x.v << l) + sum_k u_k * (y << k)
//! ```
//!
//! where `v_l` ranges over the unknown bits of `y` and `u_k` over those of `x`.
//! Start from the exact product of the known parts; for each unknown bit, the
//! partial sum is either `acc` or `acc + c`, and `join(acc, acc + c)` holds both.
//! See doc/future/tnum-mul-div-precision.md, "Multiplication: pair-join".

use crate::bools::*;
use crate::nats::*;
use crate::tbit::*;
use crate::tnum::*;
use vstd::prelude::*;

verus! {

/// The bits of `d` are among those of `m`.
pub open spec fn submask(d: nat, m: nat) -> bool { bw_and_not(d, m) == 0 }

/// Peel the lowest bit of a submask: the tail is a submask of the tail, a set
/// head bit is set in `m`, and the only submask of 0 is 0.
pub proof fn submask_hd_tl(d: nat, m: nat)
    requires submask(d, m)
    ensures
        submask(tl(d), tl(m)),
        hd(d).b() ==> hd(m).b(),
        m == 0 ==> d == 0,
{
    mapd_hd_tl(d, m, |x: Bit, y: Bit| x.and_not(y));
    assert(hd(0 as nat) == Bit::f() && tl(0 as nat) == 0 as nat);
    and_not_zero_le(d, m);
}

impl Tnum {
    /// Pair-join over the unknown bits `ym` of the multiplier, with the constant
    /// `s` (the known part of the multiplicand, shifted to the current bit).
    pub open spec fn pj_const(s: nat, ym: nat, acc: Tnum) -> Tnum
        decreases ym
    {
        if ym == 0 { acc }
        else {
            let acc1 = if hd(ym).b() { acc.join(acc.add(Tnum::unit(s))) } else { acc };
            Tnum::pj_const(lsh(s), tl(ym), acc1)
        }
    }

    /// Pair-join over the unknown bits `xm` of the multiplicand, adding the
    /// multiplier `y` (shifted to the current bit) as a Tnum.
    pub open spec fn pj_tnum(y: Tnum, xm: nat, acc: Tnum) -> Tnum
        decreases xm
    {
        if xm == 0 { acc }
        else {
            let acc1 = if hd(xm).b() { acc.join(acc.add(y)) } else { acc };
            Tnum::pj_tnum(y.lsh(), tl(xm), acc1)
        }
    }

    /// Pair-join multiplication.
    pub open spec fn pair_mul(x: Tnum, y: Tnum) -> Tnum {
        Tnum::pj_tnum(y, x.mask, Tnum::pj_const(x.val, y.mask, Tnum::unit(prod(x.val, y.val))))
    }

    /// One pair-join step: `join(acc, acc + c)` holds `z` and `z + w`.
    pub proof fn pj_step_sound(acc: Tnum, c: Tnum, z: nat, w: nat)
        requires acc.has(z), c.has(w)
        ensures
            acc.join(acc.add(c)).has(z),
            acc.join(acc.add(c)).has(z + w),
    {
        acc.add_sound(c);
        nat_add_correct(z, w);
        acc.join_sound(acc.add(c));
    }

    /// One pair-join step preserves inv.
    pub proof fn pj_step_inv(acc: Tnum, c: Tnum)
        requires acc.inv(), c.inv()
        ensures acc.join(acc.add(c)).inv()
    {
        acc.add_inv(c);
        acc.join_inv(acc.add(c));
    }

    pub proof fn pj_const_inv(s: nat, ym: nat, acc: Tnum)
        requires acc.inv()
        ensures Tnum::pj_const(s, ym, acc).inv()
        decreases ym
    {
        if ym != 0 {
            disj_zero_r(s);
            if hd(ym).b() { Tnum::pj_step_inv(acc, Tnum::unit(s)); }
            let acc1 = if hd(ym).b() { acc.join(acc.add(Tnum::unit(s))) } else { acc };
            Tnum::pj_const_inv(lsh(s), tl(ym), acc1);
        }
    }

    pub proof fn pj_tnum_inv(y: Tnum, xm: nat, acc: Tnum)
        requires acc.inv(), y.inv()
        ensures Tnum::pj_tnum(y, xm, acc).inv()
        decreases xm
    {
        if xm != 0 {
            if hd(xm).b() { Tnum::pj_step_inv(acc, y); }
            let acc1 = if hd(xm).b() { acc.join(acc.add(y)) } else { acc };
            disj_cons(y.val, Bit::f(), y.mask, Bit::f());
            Tnum::pj_tnum_inv(y.lsh(), tl(xm), acc1);
        }
    }

    /// Lemma 1: `pj_const(s, ym, acc)` holds `z + s * d` for every member `z` of
    /// `acc` and every submask `d` of `ym`.
    pub proof fn pj_const_sound(s: nat, ym: nat, acc: Tnum, z: nat, d: nat)
        requires acc.has(z), submask(d, ym)
        ensures Tnum::pj_const(s, ym, acc).has(z + s * d)
        decreases ym
    {
        submask_hd_tl(d, ym);
        if ym == 0 {
            assert(s * d == 0) by(nonlinear_arith) requires d == 0;
        } else {
            let acc1 = if hd(ym).b() { acc.join(acc.add(Tnum::unit(s))) } else { acc };
            let h = hd(d).n();
            let z1 = z + s * h;
            assert(acc1.has(z1)) by {
                if hd(ym).b() {
                    Tnum::unit_has(s);
                    Tnum::pj_step_sound(acc, Tnum::unit(s), z, s);
                }
                if h == 1 { assert(s * h == s) by(nonlinear_arith) requires h == 1; }
                else { assert(s * h == 0) by(nonlinear_arith) requires h == 0; }
            };
            Tnum::pj_const_sound(lsh(s), tl(ym), acc1, z1, tl(d));
            hd_tl(d);
            let t = tl(d);
            assert(lsh(s) == 2 * s);
            assert(z1 + (2 * s) * t == z + s * d) by(nonlinear_arith)
                requires z1 == z + s * h, d == h + 2 * t;
        }
    }

    /// Lemma 2: `pj_tnum(y, xm, acc)` holds `z + w * d` for every member `z` of
    /// `acc`, member `w` of `y`, and submask `d` of `xm`.
    pub proof fn pj_tnum_sound(y: Tnum, xm: nat, acc: Tnum, z: nat, w: nat, d: nat)
        requires acc.has(z), y.has(w), submask(d, xm)
        ensures Tnum::pj_tnum(y, xm, acc).has(z + w * d)
        decreases xm
    {
        submask_hd_tl(d, xm);
        if xm == 0 {
            assert(w * d == 0) by(nonlinear_arith) requires d == 0;
        } else {
            let acc1 = if hd(xm).b() { acc.join(acc.add(y)) } else { acc };
            let h = hd(d).n();
            let z1 = z + w * h;
            assert(acc1.has(z1)) by {
                if hd(xm).b() {
                    Tnum::pj_step_sound(acc, y, z, w);
                }
                if h == 1 { assert(w * h == w) by(nonlinear_arith) requires h == 1; }
                else { assert(w * h == 0) by(nonlinear_arith) requires h == 0; }
            };
            y.lsh_sound();
            assert(y.lsh().has(lsh(w)));
            Tnum::pj_tnum_sound(y.lsh(), tl(xm), acc1, z1, lsh(w), tl(d));
            hd_tl(d);
            let t = tl(d);
            assert(lsh(w) == 2 * w);
            assert(z1 + (2 * w) * t == z + w * d) by(nonlinear_arith)
                requires z1 == z + w * h, d == h + 2 * t;
        }
    }

    /// A member is the known part plus a submask of the unknown part.
    pub proof fn has_split(self, n: nat)
        requires self.has(n)
        ensures
            n == self.val + bw_and(n, self.mask),
            submask(bw_and(n, self.mask), self.mask),
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
        nat_add_correct(self.val, bw_and(n, self.mask));
        assert forall|i: nat| #![auto] bit(bw_and_not(bw_and(n, self.mask), self.mask), i) == bit(0 as nat, i) by {
            and_not_bit(bw_and(n, self.mask), self.mask, i);
            and_bit(n, self.mask, i);
            bit_zero(i);
        };
        eq_from_bits(bw_and_not(bw_and(n, self.mask), self.mask), 0);
    }

    /// Chop distributes through join (needed by the exec simulation).
    pub proof fn chop_join(a: Tnum, b: Tnum, w: nat)
        ensures a.join(b).chop_tn(w) == a.chop_tn(w).join(b.chop_tn(w))
    {
        let jv = bw_and(a.val, b.val);
        let ju = bw_or(a.u(), b.u());
        chop_mapd(a.val, b.val, |x: Bit, y: Bit| x.and(y), w);
        chop_bw_xor(a.val, a.mask, w);
        chop_bw_xor(b.val, b.mask, w);
        chop_bw_or(a.u(), b.u(), w);
        chop_bw_xor(jv, ju, w);
    }

    /// Soundness of pair-join multiplication, stated as `Anum::tnum_mul_sound`.
    pub proof fn pair_mul_sound(x: Tnum, y: Tnum)
        requires x.inv(), y.inv()
        ensures
            Tnum::pair_mul(x, y).inv(),
            forall|a: nat, b: nat| #![auto]
                x.has(a) && y.has(b) ==> Tnum::pair_mul(x, y).has(nat_mul_acc(a, b, 0))
    {
        let c = Tnum::pj_const(x.val, y.mask, Tnum::unit(prod(x.val, y.val)));
        disj_zero_r(prod(x.val, y.val));
        Tnum::pj_const_inv(x.val, y.mask, Tnum::unit(prod(x.val, y.val)));
        Tnum::pj_tnum_inv(y, x.mask, c);
        assert forall|a: nat, b: nat| #![auto]
            x.has(a) && y.has(b) implies Tnum::pair_mul(x, y).has(nat_mul_acc(a, b, 0)) by {
            x.has_split(a);
            y.has_split(b);
            let da = bw_and(a, x.mask);
            let db = bw_and(b, y.mask);
            let p0 = prod(x.val, y.val);
            Tnum::unit_has(p0);
            Tnum::pj_const_sound(x.val, y.mask, Tnum::unit(p0), p0, db);
            Tnum::pj_tnum_sound(y, x.mask, c, p0 + x.val * db, b, da);
            nat_mul_acc_correct(a, b, 0);
            assert(p0 + x.val * db + b * da == a * b) by(nonlinear_arith)
                requires p0 == x.val * y.val, a == x.val + da, b == y.val + db;
        };
    }
}

} // verus!
