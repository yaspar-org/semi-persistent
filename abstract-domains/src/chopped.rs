// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
use crate::anum::*;
use crate::bools::*;
use crate::nats::*;
use crate::tbit::*;
use crate::tnum::*;
use crate::unum::*;
/// Layer 3: Bounded register simulation.
///
/// `ChoppedTnum{tn, w}` wraps an unbounded Tnum with a bit-width `w`.
/// Proves that all operations on w-bit values produce w-bit results:
/// - Bitwise ops preserve width (via `fits_mapd`)
/// - Arithmetic ops are chopped to w bits (via `chop_sound`)
/// - Soundness: `ChoppedTnum.has(x) && ChoppedTnum.has(y) ==> ChoppedTnum.op(x,y).has(chop(x op y, w))`
///
/// This is the bridge between the unbounded Layer 2 proofs and the
/// bounded Layer 4 executable implementations.
use vstd::prelude::*;

verus! {

/// A bounded Tnum: fits in w bits.
pub struct ChoppedTnum {
    pub tnum: Tnum,
    pub w: nat,
}

impl ChoppedTnum {
    pub open spec fn inv(self) -> bool {
        self.tnum.inv() && fits(self.tnum.val, self.w) && fits(self.tnum.mask, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.tnum.has(n) && fits(n, self.w)
    }

    // Helper to construct ChoppedTnum without struct literal in ensures
    pub open spec fn mk(tnum: Tnum, w: nat) -> ChoppedTnum { ChoppedTnum { tnum, w } }

    // ================================================================
    // Width preservation: bitwise ops on w-bit Tnums produce w-bit Tnums
    // ================================================================

    pub open spec fn bw_or(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_or(t.tnum), self.w) }
    pub open spec fn bw_and(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_and(t.tnum), self.w) }
    pub open spec fn bw_xor(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_xor(t.tnum), self.w) }

    /// Helper: mapd preserves fits when inputs fit.
    proof fn fits_mapd(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit, w: nat)
        requires fits(a, w), fits(b, w), f(Bit::f(), Bit::f()) == Bit::f()
        ensures fits(mapd(a, b, f), w)
    {
        chop_mapd(a, b, f, w);
        // chop(mapd(a,b,f), w) == mapd(chop(a,w), chop(b,w), f) == mapd(a,b,f)
    }

    pub proof fn or_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_or(t).inv()
    {
        let w = self.w;
        self.tnum.or_sound(t.tnum);
        // fits: or(sv,tv) and andnot(or(sm,tm), or(sv,tv))
        Self::fits_mapd(self.tnum.val, t.tnum.val, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(self.tnum.mask, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(bw_or(self.tnum.mask, t.tnum.mask), bw_or(self.tnum.val, t.tnum.val), |x: Bit, y: Bit| x.and_not(y), w);
    }

    pub proof fn and_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_and(t).inv()
    {
        let w = self.w;
        self.tnum.and_sound(t.tnum);
        Self::fits_mapd(self.tnum.val, t.tnum.val, |x: Bit, y: Bit| x.and(y), w);
        Self::fits_mapd(self.tnum.mask, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
    }

    pub proof fn xor_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_xor(t).inv()
    {
        let sv = self.tnum.val; let sm = self.tnum.mask;
        let tv = t.tnum.val; let tm = t.tnum.mask;
        let w = self.w;
        Self::fits_mapd(sv, tv, |x: Bit, y: Bit| x.xor(y), w);
        Self::fits_mapd(sm, tm, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(bw_xor(sv, tv), bw_or(sm, tm), |x: Bit, y: Bit| x.and_not(y), w);
        assert forall|i: nat| #![auto] !(bit(bw_and_not(bw_xor(sv, tv), bw_or(sm, tm)), i).b() && bit(bw_or(sm, tm), i).b()) by {
            and_not_bit(bw_xor(sv, tv), bw_or(sm, tm), i);
        };
        disj_bits(bw_and_not(bw_xor(sv, tv), bw_or(sm, tm)), bw_or(sm, tm));
    }

    // ================================================================
    // Bounded arithmetic: chop(op(a, b), w)
    // ================================================================

    /// Bounded addition: add_bitwise chopped to w bits.
    pub open spec fn add(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.add_bitwise(t.tnum).chop_tn(self.w), w: self.w }
    }

    pub proof fn add_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==>
            self.add(t).has(chop(nat_add(x, y), self.w))
    {
        self.tnum.add_sound(t.tnum);
        self.tnum.add_bitwise_eq(t.tnum);
        let sum = self.tnum.add_bitwise(t.tnum);
        Tnum::add_bitwise_inv(self.tnum, t.tnum);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.add(t).has(chop(nat_add(x, y), self.w)) by {
            assert(sum.has(nat_add(x, y)));
            sum.chop_sound(self.w);
            chop_idem(nat_add(x, y), self.w);
        };
    }

    pub proof fn add_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.add(t).inv()
    {
        Tnum::add_bitwise_inv(self.tnum, t.tnum);
        self.tnum.add_bitwise(t.tnum).chop_sound(self.w);
        // chop_tn always produces fits values
        chop_idem(self.tnum.add_bitwise(t.tnum).val, self.w);
        chop_idem(self.tnum.add_bitwise(t.tnum).mask, self.w);
        // chop_tn(x, w).v = chop(x.v, w), chop_tn(x, w).m = chop(x.m, w)
        // fits(chop(_, w), w) from chop_idem
    }

    /// Bounded multiplication: times chopped to w bits.
    pub open spec fn mul(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: Anum::tnum_mul(self.tnum, t.tnum).chop_tn(self.w), w: self.w }
    }

    pub proof fn mul_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==>
            self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w))
    {
        Anum::tnum_mul_sound(self.tnum, t.tnum);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w)) by {
            let prod = Anum::tnum_mul(self.tnum, t.tnum);
            assert(prod.has(nat_mul_acc(x, y, 0)));
            prod.chop_sound(self.w);
            chop_idem(nat_mul_acc(x, y, 0), self.w);
        };
    }

    /// Bounded division.
    pub open spec fn div(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.div(t.tnum, self.w).0, w: self.w }
    }

    /// Bounded negation.
    pub open spec fn neg(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.neg(self.w), w: self.w }
    }

    /// Bounded right shift.
    pub open spec fn rsh(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.rsh(), w: self.w }
    }

    proof fn fits_rsh(n: nat, w: nat)
        requires fits(n, w)
        ensures fits(rsh(n), w)
    {
        assert forall|j: nat| #![auto] bit(chop(rsh(n), w), j) == bit(rsh(n), j) by {
            chop_bit(rsh(n), w, j);
            if j >= w {
                bit_tl(n, j);
                chop_bit(n, w, j + 1);
            }
        };
        eq_from_bits(chop(rsh(n), w), rsh(n));
    }

    pub proof fn rsh_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rsh().has(rsh(n))
    {
        self.tnum.rsh_sound();
        assert forall|n: nat| #![auto] self.has(n) implies self.rsh().has(rsh(n)) by {
            Self::fits_rsh(n, self.w);
        };
    }

    /// Bounded left shift (with chop).
    pub open spec fn lsh(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.lsh().chop_tn(self.w), w: self.w }
    }

    pub proof fn lsh_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lsh().has(chop(lsh(n), self.w))
    {
        self.tnum.lsh_sound();
        assert forall|n: nat| #![auto] self.has(n)
            implies self.lsh().has(chop(lsh(n), self.w)) by {
            self.tnum.lsh().chop_sound(self.w);
            chop_idem(lsh(n), self.w);
        };
    }

    /// Bounded join.
    pub open spec fn join(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.join(t.tnum), w: self.w }
    }

    pub proof fn join_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            forall|n: nat| #![auto] self.has(n) ==> self.join(t).has(n),
            forall|n: nat| #![auto] t.has(n) ==> self.join(t).has(n),
    {
        self.tnum.join_sound(t.tnum);
    }

    /// Bounded meet.
    pub open spec fn meet(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.meet(t.tnum), w: self.w }
    }

    pub proof fn meet_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|n: nat| #![auto] self.has(n) && t.has(n) ==> self.meet(t).has(n)
    {
        self.tnum.meet_sound(t.tnum);
    }
}

/// A bounded Anum: fits in w bits.
pub struct ChoppedAnum {
    pub anum: Anum,
    pub w: nat,
}

impl ChoppedAnum {
    pub open spec fn inv(self) -> bool {
        self.anum.to_tnum().inv() && fits(self.anum.base, self.w) && fits(self.anum.span, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.anum.has(n) && fits(n, self.w)
    }

    /// add_sound: if both inputs and their sum fit, the result contains the sum.
    pub proof fn add_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) && fits(nat_add(x, y), self.w)
            ==> self.anum.add(t.anum).has(nat_add(x, y))
    {
        self.anum.add_sound(t.anum);
    }


    /// div_const_sound: delegates to Anum::div_const_sound.
    pub proof fn div_const_sound(self, d: nat)
        requires self.inv(), d > 0
        ensures forall|x: nat| #![auto] self.has(x) ==> self.anum.div_const(d).has(x / d)
    {
        self.anum.div_const_sound(d);
    }


}

/// A bounded Unum: fits in w bits.
pub struct ChoppedUnum {
    pub unum: Unum,
    pub w: nat,
}

impl ChoppedUnum {
    pub open spec fn inv(self) -> bool {
        fits(self.unum.base, self.w) && fits(self.unum.extent, self.w) && fits(self.unum.walls, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.inv() && self.unum.has(n) && fits(n, self.w)
    }

    pub proof fn add_sound(self, t: ChoppedUnum)
        requires self.inv(), t.inv(), self.w == t.w,
            fits(nat_add(self.unum.extent, t.unum.extent), self.w),
            fits(nat_add(self.unum.base, t.unum.base), self.w),
        ensures forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(nat_add(c1, c2), self.w)
            ==> self.unum.add(t.unum).truncate(self.w).has(nat_add(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(nat_add(c1, c2), self.w)
            implies self.unum.add(t.unum).truncate(self.w).has(nat_add(c1, c2)) by {
            nat_add_correct(c1, c2);
            chop_is_mod(nat_add(c1, c2), self.w);
            exp_pos(self.w);
            self.unum.add_bounded_sound(t.unum, c1, c2, self.w);
        };
    }

    pub proof fn mul_sound(self, t: ChoppedUnum)
        requires self.inv(), t.inv(), self.w == t.w,
            fits(prod(self.unum.base, t.unum.base), self.w),
            fits(prod(self.unum.base, t.unum.extent) + prod(t.unum.base, self.unum.extent) + prod(self.unum.extent, t.unum.extent), self.w),
        ensures forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(prod(c1, c2), self.w)
            ==> self.unum.mul(t.unum).truncate(self.w).has(prod(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(prod(c1, c2), self.w)
            implies self.unum.mul(t.unum).truncate(self.w).has(prod(c1, c2)) by {
            chop_is_mod(prod(c1, c2), self.w);
            exp_pos(self.w);
            self.unum.mul_bounded_sound(t.unum, c1, c2, self.w);
        };
    }
}

} // verus!
