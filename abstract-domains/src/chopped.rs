// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
use crate::anum::*;
use crate::bools::*;
use crate::div::*;
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
    // Bitwise soundness at width w: the L2 theorems, and w-bit operands
    // give a w-bit result
    // ================================================================

    pub proof fn or_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_or(t).has(bw_or(x, y))
    {
        self.tnum.or_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_or(t).has(bw_or(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.or(b), self.w);
        };
    }

    pub proof fn and_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_and(t).has(bw_and(x, y))
    {
        self.tnum.and_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_and(t).has(bw_and(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.and(b), self.w);
        };
    }

    pub proof fn xor_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_xor(t).has(bw_xor(x, y))
    {
        self.tnum.xor_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_xor(t).has(bw_xor(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.xor(b), self.w);
        };
    }

    pub open spec fn bw_and_not(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_and_not(t.tnum), self.w) }

    pub proof fn and_not_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_and_not(t).has(bw_and_not(x, y))
    {
        self.tnum.and_not_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_and_not(t).has(bw_and_not(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.and_not(b), self.w);
        };
    }

    /// Bounded NOT: XOR with the w-bit all-ones constant.
    pub open spec fn bw_not(self) -> ChoppedTnum {
        Self::mk(self.tnum.bw_xor(Tnum::unit(all_ones(self.w))), self.w)
    }

    pub proof fn not_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.bw_not().has(bw_xor(n, all_ones(self.w)))
    {
        let ones = all_ones(self.w);
        exp_pos(self.w);
        chop_id(ones, self.w);
        Tnum::unit_has(ones);
        self.tnum.xor_sound(Tnum::unit(ones));
        assert forall|n: nat| #![auto] self.has(n) implies self.bw_not().has(bw_xor(n, ones)) by {
            Self::fits_mapd(n, ones, |a: Bit, b: Bit| a.xor(b), self.w);
        };
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

    /// Bounded multiplication: pair-join (`Tnum::pair_mul`) chopped to w bits.
    pub open spec fn mul(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: Tnum::pair_mul(self.tnum, t.tnum).chop_tn(self.w), w: self.w }
    }

    pub proof fn mul_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.mul(t).inv(),
            forall|x: nat, y: nat| #![auto]
                self.has(x) && t.has(y) ==>
                self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w))
    {
        let prod = Tnum::pair_mul(self.tnum, t.tnum);
        Tnum::pair_mul_sound(self.tnum, t.tnum);
        prod.chop_sound(self.w);
        chop_idem(prod.val, self.w);
        chop_idem(prod.mask, self.w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w)) by {
            assert(prod.has(nat_mul_acc(x, y, 0)));
            chop_idem(nat_mul_acc(x, y, 0), self.w);
        };
    }

    /// Bounded division.
    pub open spec fn div(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.div(t.tnum, self.w).0, w: self.w }
    }

    /// Bounded guarded division: Tnum::div_g with w iterations and the remainder
    /// width k = len(t.max()), the bit length of the largest divisor; quotient and
    /// remainder are chopped to w bits.
    pub open spec fn div_g(self, t: ChoppedTnum) -> (ChoppedTnum, ChoppedTnum) {
        let (q, r) = self.tnum.div_g(t.tnum, self.w, len(t.tnum.max()));
        (ChoppedTnum { tnum: q.chop_tn(self.w), w: self.w }, ChoppedTnum { tnum: r.chop_tn(self.w), w: self.w })
    }

    /// div_g is well formed and contains x / y and x % y for all members x, y.
    pub proof fn div_g_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w, t.tnum.min() > 0
        ensures
            self.div_g(t).0.inv(),
            self.div_g(t).1.inv(),
            forall|x: nat, y: nat| #![auto]
                self.has(x) && t.has(y) ==> self.div_g(t).0.has(x / y) && self.div_g(t).1.has(x % y),
    {
        let w = self.w;
        let k = len(t.tnum.max());
        Self::fits_mapd(t.tnum.val, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_lt(t.tnum.max(), w);
        len_bound(t.tnum.max());
        self.tnum.div_g_sound(t.tnum, w, k);
        let (q, r) = self.tnum.div_g(t.tnum, w, k);
        q.chop_sound(w);
        r.chop_sound(w);
        chop_idem(q.val, w); chop_idem(q.mask, w);
        chop_idem(r.val, w); chop_idem(r.mask, w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) implies self.div_g(t).0.has(x / y) && self.div_g(t).1.has(x % y) by {
            Self::fits_lt(x, w);
            t.tnum.has_bounds(y);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, y as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, y as int);
            assert(x / y <= x && x % y <= x) by(nonlinear_arith)
                requires x == y * (x / y) + x % y, y > 0, x / y >= 0, x % y >= 0;
            chop_id(x / y, w);
            chop_id(x % y, w);
        };
    }

    /// The members of t whose highest set bit is i, for t.val == 0: bit i set,
    /// the unknown bits below i free. Its min is 2^i > 0, so div_g applies.
    pub open spec fn top_piece(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: Tnum::ctor(exp(i), chop(self.tnum.mask, i)), w: self.w }
    }

    /// div_g over the top pieces of t at its unknown bits below j, joined;
    /// None when t has no unknown bit below j.
    pub open spec fn div_z(self, t: ChoppedTnum, j: nat) -> Option<(ChoppedTnum, ChoppedTnum)>
        decreases j
    {
        if j == 0 { None }
        else {
            let i = (j - 1) as nat;
            let acc = self.div_z(t, i);
            if bit(t.tnum.mask, i).b() {
                let p = self.div_g(t.top_piece(i));
                match acc {
                    None => Some(p),
                    Some(a) => Some((a.0.join(p.0), a.1.join(p.1))),
                }
            } else { acc }
        }
    }

    /// Division by the nonzero members of t: div_g when t.min() > 0, otherwise
    /// the join of div_g over the top pieces of t. None when t is {0}.
    pub open spec fn div_nz(self, t: ChoppedTnum) -> Option<(ChoppedTnum, ChoppedTnum)> {
        if t.tnum.val > 0 { Some(self.div_g(t)) } else { self.div_z(t, self.w) }
    }

    /// A nonzero member y of t (t.val == 0) is in the top piece at bit
    /// len(y) - 1, which is an unknown bit of t below w.
    pub proof fn top_piece_has(self, y: nat)
        requires self.inv(), self.tnum.val == 0, self.has(y), y > 0
        ensures
            len(y) > 0,
            (len(y) - 1) < self.w,
            bit(self.tnum.mask, (len(y) - 1) as nat).b(),
            self.top_piece((len(y) - 1) as nat).has(y),
    {
        let m = self.tnum.mask;
        top_bit(y);
        let i = (len(y) - 1) as nat;
        Self::fits_lt(y, self.w);
        len_le(y, self.w);
        self.tnum.has_equiv(y);
        assert forall|j: nat| #![auto] bit(y, j).b() implies bit(m, j).b() by {
            and_not_bit(y, m, j);
            bit_zero(j);
        };
        let p = self.top_piece(i).tnum;
        p.has_equiv(y);
        assert forall|j: nat| #![auto] bit(bw_and_not(y, chop(m, i)), j) == bit(exp(i), j) by {
            and_not_bit(y, chop(m, i), j);
            chop_bit(m, i, j);
            bit_exp(i, j);
            if j > i {
                assert(j >= len(y));
            }
        };
        eq_from_bits(bw_and_not(y, chop(m, i)), exp(i));
    }

    /// A top piece below w is well formed and has a positive min.
    pub proof fn top_piece_inv(self, i: nat)
        requires self.inv(), i < self.w
        ensures self.top_piece(i).inv(), self.top_piece(i).tnum.min() > 0
    {
        let m = self.tnum.mask;
        exp_pos(i);
        assert forall|j: nat| #![auto] !(bit(exp(i), j).b() && bit(chop(m, i), j).b()) by {
            bit_exp(i, j);
            chop_bit(m, i, j);
        };
        disj_bits(exp(i), chop(m, i));
        exp_succ(i);
        exp_le(i + 1, self.w);
        chop_id(exp(i), self.w);
        chop_lt(m, i);
        chop_id(chop(m, i), self.w);
    }

    /// div_z is Some exactly when t has an unknown bit below j; then it is well
    /// formed and contains x / y and x % y for every member y != 0 of t below 2^j.
    pub proof fn div_z_sound(self, t: ChoppedTnum, j: nat)
        requires self.inv(), t.inv(), self.w == t.w, t.tnum.val == 0, j <= self.w
        ensures
            self.div_z(t, j) is Some <==> exists|i: nat| i < j && #[trigger] bit(t.tnum.mask, i).b(),
            match self.div_z(t, j) {
                Some(p) => p.0.inv() && p.1.inv() && p.0.w == self.w && p.1.w == self.w
                    && forall|x: nat, y: nat| #![auto]
                        self.has(x) && t.has(y) && y > 0 && len(y) <= j ==> p.0.has(x / y) && p.1.has(x % y),
                None => true,
            },
        decreases j
    {
        if j > 0 {
            let i = (j - 1) as nat;
            self.div_z_sound(t, i);
            let acc = self.div_z(t, i);
            if bit(t.tnum.mask, i).b() {
                let tp = t.top_piece(i);
                t.top_piece_inv(i);
                self.div_g_sound(tp);
                let p = self.div_g(tp);
                if let Some(a) = acc {
                    a.0.tnum.join_inv(p.0.tnum);
                    a.1.tnum.join_inv(p.1.tnum);
                    a.0.tnum.join_sound(p.0.tnum);
                    a.1.tnum.join_sound(p.1.tnum);
                    Self::join_fits(a.0, p.0);
                    Self::join_fits(a.1, p.1);
                }
                assert forall|x: nat, y: nat| #![auto]
                    self.has(x) && t.has(y) && y > 0 && len(y) <= j
                    implies self.div_z(t, j).unwrap().0.has(x / y) && self.div_z(t, j).unwrap().1.has(x % y) by {
                    t.top_piece_has(y);
                    if len(y) == j {
                        assert(tp.has(y));
                    } else {
                        assert(bit(t.tnum.mask, (len(y) - 1) as nat).b());
                    }
                };
            } else {
                assert forall|x: nat, y: nat| #![auto]
                    self.has(x) && t.has(y) && y > 0 && len(y) <= j
                    implies len(y) <= i by {
                    t.top_piece_has(y);
                };
            }
            if exists|k: nat| k < j && #[trigger] bit(t.tnum.mask, k).b() {
                let k = choose|k: nat| k < j && #[trigger] bit(t.tnum.mask, k).b();
                if k < i { assert(bit(t.tnum.mask, k).b()); }
            }
        }
    }

    /// The join of two w-bit Tnums fits in w bits.
    proof fn join_fits(a: ChoppedTnum, b: ChoppedTnum)
        requires a.inv(), b.inv(), a.w == b.w
        ensures fits(a.join(b).tnum.val, a.w), fits(a.join(b).tnum.mask, a.w)
    {
        let (av, bv) = (a.tnum.val, b.tnum.val);
        Self::fits_mapd(av, bv, |x: Bit, y: Bit| x.and(y), a.w);
        Self::fits_mapd(av, a.tnum.mask, |x: Bit, y: Bit| x.xor(y), a.w);
        Self::fits_mapd(bv, b.tnum.mask, |x: Bit, y: Bit| x.xor(y), a.w);
        Self::fits_mapd(a.tnum.u(), b.tnum.u(), |x: Bit, y: Bit| x.or(y), a.w);
        Self::fits_mapd(bw_and(av, bv), bw_or(a.tnum.u(), b.tnum.u()), |x: Bit, y: Bit| x.xor(y), a.w);
    }

    /// div_nz is None exactly when t is {0}; otherwise it is well formed and
    /// contains x / y and x % y for every member x of self and member y != 0 of t.
    pub proof fn div_nz_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.div_nz(t) is None <==> (t.tnum.val == 0 && t.tnum.mask == 0),
            match self.div_nz(t) {
                Some(p) => p.0.inv() && p.1.inv() && p.0.w == self.w && p.1.w == self.w
                    && forall|x: nat, y: nat| #![auto]
                        self.has(x) && t.has(y) && y > 0 ==> p.0.has(x / y) && p.1.has(x % y),
                None => true,
            },
    {
        if t.tnum.val > 0 {
            self.div_g_sound(t);
        } else {
            let m = t.tnum.mask;
            self.div_z_sound(t, self.w);
            assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) && y > 0 implies len(y) <= self.w by {
                t.top_piece_has(y);
            };
            if m == 0 {
                assert forall|i: nat| #![auto] !bit(m, i).b() by { bit_zero(i); };
            } else {
                top_bit(m);
                Self::fits_lt(m, self.w);
                len_le(m, self.w);
                assert(bit(m, (len(m) - 1) as nat).b());
            }
        }
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

    /// Bounded right shift by i bits.
    pub open spec fn rshi(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.rshi(i), w: self.w }
    }

    proof fn fits_rshi(n: nat, w: nat, i: nat)
        requires fits(n, w)
        ensures fits(rshi(n, i), w)
        decreases i
    {
        if i > 0 {
            Self::fits_rsh(n, w);
            Self::fits_rshi(rsh(n), w, (i - 1) as nat);
        }
    }

    pub proof fn rshi_sound(self, i: nat)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rshi(i).has(rshi(n, i))
    {
        self.tnum.rshi_sound(i);
        assert forall|n: nat| #![auto] self.has(n) implies self.rshi(i).has(rshi(n, i)) by {
            Self::fits_rshi(n, self.w, i);
        };
    }

    pub proof fn rshi_inv(self, i: nat)
        requires self.inv()
        ensures self.rshi(i).inv()
    {
        let t = self.tnum;
        disj_bits(t.val, t.mask);
        assert forall|j: nat| #![auto] !(bit(rshi(t.val, i), j).b() && bit(rshi(t.mask, i), j).b()) by {
            bit_rshi_add(t.val, i, j);
            bit_rshi_add(t.mask, i, j);
        };
        disj_bits(rshi(t.val, i), rshi(t.mask, i));
        Self::fits_rshi(t.val, self.w, i);
        Self::fits_rshi(t.mask, self.w, i);
    }

    /// Bounded left shift by i bits (with chop).
    pub open spec fn lshi(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.lshi(i).chop_tn(self.w), w: self.w }
    }

    pub proof fn lshi_sound(self, i: nat)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lshi(i).has(chop(lshi(n, i), self.w))
    {
        self.tnum.lshi_sound(i);
        self.tnum.lshi_inv(i);
        assert forall|n: nat| #![auto] self.has(n)
            implies self.lshi(i).has(chop(lshi(n, i), self.w)) by {
            self.tnum.lshi(i).chop_sound(self.w);
            chop_idem(lshi(n, i), self.w);
        };
    }

    /// A w-bit value is below 2^w.
    proof fn fits_lt(n: nat, w: nat)
        requires fits(n, w)
        ensures n < exp(w)
    {
        chop_is_mod(n, w);
        exp_pos(w);
        vstd::arithmetic::div_mod::lemma_mod_bound(n as int, exp(w) as int);
    }

    pub proof fn neg_sound(self)
        requires self.inv(), self.w > 0
        ensures forall|n: nat| #![auto] self.has(n) ==> self.neg().has(chop((exp(self.w) - n) as nat, self.w))
    {
        self.tnum.neg_sound(self.w);
        assert forall|n: nat| #![auto] self.has(n) implies self.neg().has(chop((exp(self.w) - n) as nat, self.w)) by {
            Self::fits_lt(n, self.w);
            chop_idem((exp(self.w) - n) as nat, self.w);
        };
    }

    /// Bounded subtraction: add the bounded negation.
    pub open spec fn sub(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.sub(t.tnum, self.w), w: self.w }
    }

    pub proof fn sub_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w, self.w > 0
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==> self.sub(t).has(chop(nat_add(x, (exp(self.w) - y) as nat), self.w))
    {
        self.tnum.sub_sound_all(t.tnum, self.w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) implies self.sub(t).has(chop(nat_add(x, (exp(self.w) - y) as nat), self.w)) by {
            Self::fits_lt(x, self.w);
            Self::fits_lt(y, self.w);
            chop_idem(nat_add(x, (exp(self.w) - y) as nat), self.w);
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


    /// A w-bit Tnum read as an Anum: base is the known bits, span the unknown ones.
    pub open spec fn from_tnum(t: ChoppedTnum) -> ChoppedAnum {
        ChoppedAnum { anum: Anum::from_tnum(t.tnum), w: t.w }
    }

    pub proof fn from_tnum_sound(t: ChoppedTnum)
        requires t.inv()
        ensures forall|n: nat| #![auto] t.has(n) ==> Self::from_tnum(t).has(n)
    {
        Anum::from_tnum_sound(t.tnum);
    }

    /// A w-bit Anum read as a Tnum: Tn(0, span) + Tn(base, 0), chopped to w bits.
    pub open spec fn to_tnum(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.anum.to_tnum().chop_tn(self.w), w: self.w }
    }

    pub proof fn to_tnum_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.to_tnum().has(n)
    {
        self.anum.to_tnum_inv();
        self.anum.to_tnum().chop_sound(self.w);
        assert forall|n: nat| #![auto] self.has(n) implies self.to_tnum().has(n) by {
            Anum::tnum_has_from_anum(self.anum, n);
            chop_idem(n, self.w);
        };
    }

    /// Bounded subtraction: the L2 sub with its span chopped to w bits.
    pub open spec fn sub(self, t: ChoppedAnum) -> ChoppedAnum {
        ChoppedAnum {
            anum: Anum {
                base: self.anum.sub(t.anum).base,
                span: chop(self.anum.sub(t.anum).span, self.w),
            },
            w: self.w,
        }
    }

    /// sub_sound: when self's base is at least t's maximum, no difference of
    /// members wraps, and every difference is a member of the bounded sub.
    pub proof fn sub_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w, self.anum.base >= nat_add(t.anum.base, t.anum.span)
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.sub(t).has((x - y) as nat)
    {
        self.anum.sub_sound(t.anum);
        let s = self.anum.sub(t.anum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.sub(t).has((x - y) as nat) by {
            ChoppedTnum::fits_lt(x, self.w);
            // y <= t's maximum <= self's base <= x
            t.anum.has_le_max(y);
            nat_add_correct(t.anum.base, t.anum.span);
            assert(y <= x);
            assert(s.has((x - y) as nat));
            let off = ((x - y) - s.base) as nat;
            // The offset is a bit subset of the span and below 2^w, so it is a
            // bit subset of the chopped span too.
            s.mask_tnum().has_equiv(off);
            chop_bw_and_not(off, s.span, self.w);
            exp_pos(self.w);
            chop_id(off, self.w);
            chop_id(0, self.w);
            Tnum::ctor(0, chop(s.span, self.w)).has_equiv(off);
            chop_id((x - y) as nat, self.w);
        };
    }

    /// div_const_sound: delegates to Anum::div_const_sound.
    pub proof fn div_const_sound(self, d: nat)
        requires self.inv(), d > 0
        ensures forall|x: nat| #![auto] self.has(x) ==> self.anum.div_const(d).has(x / d)
    {
        self.anum.div_const_sound(d);
    }

    // ================================================================
    // Bounded Anum operations
    // ================================================================

    /// The Anum of every w-bit value.
    pub open spec fn top(w: nat) -> ChoppedAnum {
        ChoppedAnum { anum: Anum { base: 0, span: all_ones(w) }, w }
    }

    pub proof fn top_sound(w: nat)
        ensures Self::top(w).inv(), forall|n: nat| #![auto] fits(n, w) ==> Self::top(w).has(n)
    {
        exp_pos(w);
        chop_id(0, w);
        chop_id(all_ones(w), w);
        Self::top(w).anum.to_tnum_inv();
        assert forall|n: nat| #![auto] fits(n, w) implies Self::top(w).has(n) by {
            Tnum::ctor(0, all_ones(w)).has_equiv(n);
            assert forall|i: nat| #![auto] bit(bw_and_not(n, all_ones(w)), i) == bit(0 as nat, i) by {
                and_not_bit(n, all_ones(w), i);
                all_ones_bit(w, i);
                bit_zero(i);
                chop_bit(n, w, i);
            };
            eq_from_bits(bw_and_not(n, all_ones(w)), 0);
        };
    }

    pub open spec fn zero(w: nat) -> ChoppedAnum {
        ChoppedAnum { anum: Anum::zero(), w }
    }

    /// to_tnum is a w-bit Tnum.
    pub proof fn to_tnum_inv(self)
        requires self.inv()
        ensures self.to_tnum().inv()
    {
        self.anum.to_tnum_inv();
        self.anum.to_tnum().chop_sound(self.w);
        chop_idem(self.anum.to_tnum().val, self.w);
        chop_idem(self.anum.to_tnum().mask, self.w);
    }

    pub proof fn from_tnum_inv(t: ChoppedTnum)
        requires t.inv()
        ensures Self::from_tnum(t).inv()
    {
        Anum::from_tnum(t.tnum).to_tnum_inv();
    }

    /// The span of an L2 add, when the two spans sum below 2^w: the add_bitwise
    /// mask (s1 + s2) | s1 | s2, each part below 2^w.
    proof fn add_span_fits(s1: nat, s2: nat, w: nat)
        requires s1 + s2 < exp(w)
        ensures fits(Tnum::ctor(0, s1).add(Tnum::ctor(0, s2)).mask, w)
    {
        disj_zero(s1);
        disj_zero(s2);
        Tnum::ctor(0, s1).add_bitwise_eq(Tnum::ctor(0, s2));
        nat_add_correct(0, 0);
        nat_add_correct(s1, s2);
        nat_add_correct(0, nat_add(s1, s2));
        exp_pos(w);
        chop_id(0, w);
        chop_id(s1, w);
        chop_id(s2, w);
        chop_id(nat_add(s1, s2), w);
        ChoppedTnum::fits_mapd(nat_add(s1, s2), 0, |a: Bit, b: Bit| a.xor(b), w);
        let x = bw_xor(nat_add(s1, s2), 0);
        ChoppedTnum::fits_mapd(x, s1, |a: Bit, b: Bit| a.or(b), w);
        ChoppedTnum::fits_mapd(bw_or(x, s1), s2, |a: Bit, b: Bit| a.or(b), w);
    }

    /// Bounded addition: the L2 add when the two maxima sum below 2^w, so no
    /// member sum wraps; top otherwise.
    pub open spec fn add_w(self, t: ChoppedAnum) -> ChoppedAnum {
        if self.anum.base + self.anum.span + t.anum.base + t.anum.span < exp(self.w) {
            ChoppedAnum { anum: self.anum.add(t.anum), w: self.w }
        } else {
            Self::top(self.w)
        }
    }

    pub proof fn add_w_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.add_w(t).inv(),
            forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.add_w(t).has(chop(x + y, self.w)),
    {
        let w = self.w;
        Self::top_sound(w);
        let (b1, s1, b2, s2) = (self.anum.base, self.anum.span, t.anum.base, t.anum.span);
        if b1 + s1 + b2 + s2 < exp(w) {
            self.anum.add_sound(t.anum);
            self.anum.add(t.anum).to_tnum_inv();
            nat_add_correct(b1, b2);
            chop_id(nat_add(b1, b2), w);
            Self::add_span_fits(s1, s2, w);
            assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.add_w(t).has(chop(x + y, w)) by {
                self.anum.has_le_max(x);
                t.anum.has_le_max(y);
                nat_add_correct(x, y);
                chop_id(x + y, w);
            };
        } else {
            assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.add_w(t).has(chop(x + y, w)) by {
                chop_idem(x + y, w);
            };
        }
    }

    /// n <= m < 2^(w-k) shifts left by k below 2^w.
    proof fn shift_fits(n: nat, m: nat, k: nat, w: nat)
        requires n <= m, m < exp((w - k) as nat), k <= w
        ensures lshi(n, k) < exp(w), fits(lshi(n, k), w)
    {
        lsh_exp(n, k);
        exp_add((w - k) as nat, k);
        exp_pos(k);
        vstd::arithmetic::mul::lemma_mul_inequality(n as int, m as int, exp(k) as int);
        vstd::arithmetic::mul::lemma_mul_strict_inequality(m as int, exp((w - k) as nat) as int, exp(k) as int);
        chop_id(lshi(n, k), w);
    }

    /// Bounded left shift by k <= w: the L2 lshi when base + span < 2^(w-k),
    /// so no member loses a bit; top otherwise.
    pub open spec fn lshi(self, k: nat) -> ChoppedAnum {
        if self.anum.base + self.anum.span < exp((self.w - k) as nat) {
            ChoppedAnum { anum: self.anum.lshi(k), w: self.w }
        } else {
            Self::top(self.w)
        }
    }

    pub proof fn lshi_sound(self, k: nat)
        requires self.inv(), k <= self.w
        ensures
            self.lshi(k).inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.lshi(k).has(chop(lshi(n, k), self.w)),
    {
        let w = self.w;
        let (b, s) = (self.anum.base, self.anum.span);
        Self::top_sound(w);
        if b + s < exp((w - k) as nat) {
            self.anum.lshi_sound(k);
            self.anum.lshi(k).to_tnum_inv();
            Self::shift_fits(b, b + s, k, w);
            Self::shift_fits(s, b + s, k, w);
            assert forall|n: nat| #![auto] self.has(n) implies self.lshi(k).has(chop(lshi(n, k), w)) by {
                self.anum.has_le_max(n);
                Self::shift_fits(n, b + s, k, w);
            };
        } else {
            assert forall|n: nat| #![auto] self.has(n) implies self.lshi(k).has(chop(lshi(n, k), w)) by {
                chop_idem(lshi(n, k), w);
            };
        }
    }

    /// Bounded negation, 2^w - x mod 2^w: {0} stays; a positive base whose
    /// base + span does not wrap reflects through 2^w; otherwise top, since the
    /// members then wrap around 0.
    pub open spec fn neg(self) -> ChoppedAnum {
        let (b, s) = (self.anum.base, self.anum.span);
        if b == 0 && s == 0 {
            self
        } else if b > 0 && b + s < exp(self.w) {
            ChoppedAnum { anum: self.anum.reflect(exp(self.w)), w: self.w }
        } else {
            Self::top(self.w)
        }
    }

    pub proof fn neg_sound(self)
        requires self.inv()
        ensures
            self.neg().inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.neg().has(chop((exp(self.w) - n) as nat, self.w)),
    {
        let w = self.w;
        let (b, s) = (self.anum.base, self.anum.span);
        Self::top_sound(w);
        exp_pos(w);
        if b == 0 && s == 0 {
            chop_is_mod(exp(w), w);
            vstd::arithmetic::div_mod::lemma_mod_self_0(exp(w) as int);
            assert forall|n: nat| #![auto] self.has(n) implies self.neg().has(chop((exp(w) - n) as nat, w)) by {
                self.anum.has_le_max(n);
            };
        } else if b > 0 && b + s < exp(w) {
            self.anum.reflect_sound(exp(w));
            self.anum.reflect(exp(w)).to_tnum_inv();
            chop_id((exp(w) - (b + s)) as nat, w);
            assert forall|n: nat| #![auto] self.has(n) implies self.neg().has(chop((exp(w) - n) as nat, w)) by {
                ChoppedTnum::fits_lt(n, w);
                chop_id((exp(w) - n) as nat, w);
            };
        } else {
            assert forall|n: nat| #![auto] self.has(n) implies self.neg().has(chop((exp(w) - n) as nat, w)) by {
                chop_idem((exp(w) - n) as nat, w);
            };
        }
    }

    /// The offsets of the members above lo <= base, as a w-bit Tnum: the
    /// bounded Tnum add of Tn(0, span) and Tn(base - lo, 0).
    pub open spec fn offsets(self, lo: nat) -> ChoppedTnum {
        ChoppedTnum::mk(Tnum::ctor(0, self.anum.span), self.w)
            .add(ChoppedTnum::mk(Tnum::ctor((self.anum.base - lo) as nat, 0), self.w))
    }

    proof fn offsets_sound(self, lo: nat)
        requires self.inv(), lo <= self.anum.base
        ensures
            self.offsets(lo).inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.offsets(lo).has((n - lo) as nat),
    {
        let w = self.w;
        let (b, s) = (self.anum.base, self.anum.span);
        let m = ChoppedTnum::mk(Tnum::ctor(0, s), w);
        let v = ChoppedTnum::mk(Tnum::ctor((b - lo) as nat, 0), w);
        disj_zero(s);
        disj_zero_r((b - lo) as nat);
        exp_pos(w);
        chop_id(0, w);
        ChoppedTnum::fits_lt(b, w);
        chop_id((b - lo) as nat, w);
        m.add_inv(v);
        m.add_sound(v);
        Tnum::unit_has((b - lo) as nat);
        assert forall|n: nat| #![auto] self.has(n) implies self.offsets(lo).has((n - lo) as nat) by {
            let d = nat_sub(n, b);
            ChoppedTnum::fits_lt(n, w);
            chop_id(d, w);
            assert(m.has(d) && v.has((b - lo) as nat));
            nat_add_correct(d, (b - lo) as nat);
            chop_id((n - lo) as nat, w);
        };
    }

    /// Join: the lower base, and the span covering the join of both offset
    /// Tnums above it (each member's offset is a bit subset of val | mask).
    pub open spec fn join(self, t: ChoppedAnum) -> ChoppedAnum {
        let lo = if self.anum.base <= t.anum.base { self.anum.base } else { t.anum.base };
        let j = self.offsets(lo).join(t.offsets(lo)).tnum;
        ChoppedAnum { anum: Anum { base: lo, span: j.max() }, w: self.w }
    }

    pub proof fn join_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.join(t).inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.join(t).has(n),
            forall|n: nat| #![auto] t.has(n) ==> self.join(t).has(n),
    {
        let w = self.w;
        let lo = if self.anum.base <= t.anum.base { self.anum.base } else { t.anum.base };
        let (o1, o2) = (self.offsets(lo), t.offsets(lo));
        self.offsets_sound(lo);
        t.offsets_sound(lo);
        o1.join_sound(o2);
        ChoppedTnum::join_fits(o1, o2);
        let j = o1.join(o2).tnum;
        ChoppedTnum::fits_mapd(j.val, j.mask, |a: Bit, b: Bit| a.or(b), w);
        self.join(t).anum.to_tnum_inv();
        assert forall|n: nat| #![auto] self.has(n) implies self.join(t).has(n) by {
            assert(o1.has((n - lo) as nat));
            Anum::cover(j, (n - lo) as nat);
        };
        assert forall|n: nat| #![auto] t.has(n) implies self.join(t).has(n) by {
            assert(o2.has((n - lo) as nat));
            Anum::cover(j, (n - lo) as nat);
        };
    }

    // ----------------------------------------------------------------
    // Through Tnum: from_tnum(op(to_tnum(a), to_tnum(b)))
    // ----------------------------------------------------------------

    pub open spec fn bw_and(self, t: ChoppedAnum) -> ChoppedAnum {
        Self::from_tnum(self.to_tnum().bw_and(t.to_tnum()))
    }

    pub open spec fn bw_or(self, t: ChoppedAnum) -> ChoppedAnum {
        Self::from_tnum(self.to_tnum().bw_or(t.to_tnum()))
    }

    pub open spec fn bw_xor(self, t: ChoppedAnum) -> ChoppedAnum {
        Self::from_tnum(self.to_tnum().bw_xor(t.to_tnum()))
    }

    pub open spec fn bw_not(self) -> ChoppedAnum {
        Self::from_tnum(self.to_tnum().bw_not())
    }

    pub open spec fn rshi(self, k: nat) -> ChoppedAnum {
        Self::from_tnum(self.to_tnum().rshi(k))
    }

    pub proof fn and_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.bw_and(t).inv(),
            forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_and(t).has(bw_and(x, y)),
    {
        let (a, b) = (self.to_tnum(), t.to_tnum());
        self.to_tnum_inv(); t.to_tnum_inv();
        self.to_tnum_sound(); t.to_tnum_sound();
        a.and_inv(b);
        a.and_sound(b);
        Self::from_tnum_inv(a.bw_and(b));
        Self::from_tnum_sound(a.bw_and(b));
    }

    pub proof fn or_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.bw_or(t).inv(),
            forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_or(t).has(bw_or(x, y)),
    {
        let (a, b) = (self.to_tnum(), t.to_tnum());
        self.to_tnum_inv(); t.to_tnum_inv();
        self.to_tnum_sound(); t.to_tnum_sound();
        a.or_inv(b);
        a.or_sound(b);
        Self::from_tnum_inv(a.bw_or(b));
        Self::from_tnum_sound(a.bw_or(b));
    }

    pub proof fn xor_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.bw_xor(t).inv(),
            forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_xor(t).has(bw_xor(x, y)),
    {
        let (a, b) = (self.to_tnum(), t.to_tnum());
        self.to_tnum_inv(); t.to_tnum_inv();
        self.to_tnum_sound(); t.to_tnum_sound();
        a.xor_inv(b);
        a.xor_sound(b);
        Self::from_tnum_inv(a.bw_xor(b));
        Self::from_tnum_sound(a.bw_xor(b));
    }

    pub proof fn not_sound(self)
        requires self.inv()
        ensures
            self.bw_not().inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.bw_not().has(bw_xor(n, all_ones(self.w))),
    {
        let w = self.w;
        let a = self.to_tnum();
        let ones = ChoppedTnum::mk(Tnum::unit(all_ones(w)), w);
        self.to_tnum_inv();
        self.to_tnum_sound();
        exp_pos(w);
        chop_id(0, w);
        chop_id(all_ones(w), w);
        disj_zero_r(all_ones(w));
        a.xor_inv(ones);
        assert(a.bw_not() == a.bw_xor(ones));
        a.not_sound();
        Self::from_tnum_inv(a.bw_not());
        Self::from_tnum_sound(a.bw_not());
    }

    pub proof fn rshi_sound(self, k: nat)
        requires self.inv()
        ensures
            self.rshi(k).inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.rshi(k).has(rshi(n, k)),
    {
        let a = self.to_tnum();
        self.to_tnum_inv();
        self.to_tnum_sound();
        a.rshi_inv(k);
        a.rshi_sound(k);
        Self::from_tnum_inv(a.rshi(k));
        Self::from_tnum_sound(a.rshi(k));
    }

    // ----------------------------------------------------------------
    // Multiplication: the bounded Anum::mul_step_anum
    // ----------------------------------------------------------------

    /// One step adds the partial product t * head(p) to the accumulator by
    /// add_w, then shifts p right and t left (chopped to w bits).
    pub open spec fn mul_step(p: Tnum, t: Tnum, a: ChoppedAnum) -> ChoppedAnum
        decreases p.size()
    {
        if p.is_zero() {
            a
        } else {
            Self::mul_step(
                p.rsh(),
                t.lsh().chop_tn(a.w),
                a.add_w(ChoppedAnum { anum: Anum::from_tnum(t.mul_bit(p.head())), w: a.w }),
            )
        }
    }

    /// Bounded multiplication: mul_step over the Tnums of both operands, from
    /// the zero accumulator.
    pub open spec fn mul(self, t: ChoppedAnum) -> ChoppedAnum {
        Self::mul_step(self.to_tnum().tnum, t.to_tnum().tnum, Self::zero(self.w))
    }

    /// t * b is a w-bit Tnum.
    proof fn mul_bit_fits(t: Tnum, b: TBit, w: nat)
        requires ChoppedTnum::mk(t, w).inv()
        ensures fits(t.mul_bit(b).val, w), fits(t.mul_bit(b).mask, w)
    {
        exp_pos(w);
        chop_id(0, w);
        ChoppedTnum::fits_mapd(t.val, t.mask, |a: Bit, b: Bit| a.or(b), w);
    }

    /// One step of the multiplication, modulo 2^w: the shifted operand and the
    /// accumulator may be chopped.
    proof fn mul_step_arith(x: nat, y: nat, z: nat, w: nat)
        ensures chop(tl(x) * chop(lsh(y), w) + chop(z + nat_mul_bit(y, hd(x)), w), w) == chop(x * y + z, w)
    {
        let m = exp(w) as int;
        let r = tl(x);
        let h = hd(x).n();
        let y2 = lsh(y);
        let zm = z + nat_mul_bit(y, hd(x));
        exp_pos(w);
        lsh_is_times2(y);
        hd_tl(x);
        if hd(x).b() { assert(h == 1); } else { assert(h == 0); }
        vstd::arithmetic::mul::lemma_mul_basics(y as int);
        assert(nat_mul_bit(y, hd(x)) == y * h);
        chop_is_mod(y2, w);
        chop_is_mod(zm, w);
        chop_is_mod(r * chop(y2, w) + chop(zm, w), w);
        chop_is_mod(x * y + z, w);
        let a = (r * chop(y2, w)) as int;
        vstd::arithmetic::div_mod::lemma_add_mod_noop_right(a, zm as int, m);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a, zm as int, m);
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(r as int, y2 as int, m);
        vstd::arithmetic::div_mod::lemma_add_mod_noop((r * y2) as int, zm as int, m);
        assert(r * y2 + zm == x * y + z) by(nonlinear_arith)
            requires y2 == 2 * y, x == h + 2 * r, zm == z + y * h;
    }

    pub proof fn mul_step_sound(p: Tnum, t: Tnum, a: ChoppedAnum)
        requires p.inv(), ChoppedTnum::mk(t, a.w).inv(), a.inv()
        ensures
            Self::mul_step(p, t, a).inv(),
            forall|x: nat, y: nat, z: nat| #![auto]
                p.has(x) && ChoppedTnum::mk(t, a.w).has(y) && a.has(z)
                ==> Self::mul_step(p, t, a).has(chop(x * y + z, a.w)),
        decreases p.size()
    {
        let w = a.w;
        exp_pos(w);
        if p.is_zero() {
            assert forall|x: nat, y: nat, z: nat| #![auto]
                p.has(x) && ChoppedTnum::mk(t, w).has(y) && a.has(z)
                implies Self::mul_step(p, t, a).has(chop(x * y + z, w)) by {
                assert(x == 0);
            };
        } else {
            let ct = ChoppedTnum::mk(t, w);
            let pb = t.mul_bit(p.head());
            let pa = ChoppedAnum { anum: Anum::from_tnum(pb), w };
            let a1 = a.add_w(pa);
            let t1 = t.lsh().chop_tn(w);
            t.times_b_inv(p.head());
            t.mul_bit_sound(p.head());
            Self::mul_bit_fits(t, p.head(), w);
            Self::from_tnum_inv(ChoppedTnum::mk(pb, w));
            Anum::from_tnum_sound(pb);
            a.add_w_sound(pa);
            Anum::rsh_inv(p);
            p.rsh_sound();
            Anum::lsh_inv(t);
            t.lsh().chop_sound(w);
            chop_idem(t.lsh().val, w);
            chop_idem(t.lsh().mask, w);
            ct.lsh_sound();
            Self::mul_step_sound(p.rsh(), t1, a1);
            assert forall|x: nat, y: nat, z: nat| #![auto]
                p.has(x) && ct.has(y) && a.has(z)
                implies Self::mul_step(p, t, a).has(chop(x * y + z, w)) by {
                let m = nat_mul_bit(y, hd(x));
                assert(p.head().has(hd(x)));
                assert(pb.has(m));
                chop_id(0, w);
                assert(pa.has(m));
                assert(a1.has(chop(z + m, w)));
                assert(ChoppedTnum::mk(t1, w).has(chop(lsh(y), w)));
                assert(p.rsh().has(rsh(x)));
                Self::mul_step_arith(x, y, z, w);
            };
        }
    }

    pub proof fn mul_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.mul(t).inv(),
            forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.mul(t).has(chop(x * y, self.w)),
    {
        let w = self.w;
        self.to_tnum_inv(); t.to_tnum_inv();
        self.to_tnum_sound(); t.to_tnum_sound();
        exp_pos(w);
        chop_id(0, w);
        Anum::zero().to_tnum_inv();
        Self::mul_step_sound(self.to_tnum().tnum, t.to_tnum().tnum, Self::zero(w));
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.mul(t).has(chop(x * y, w)) by {
            assert(Self::zero(w).has(0)) by {
                Anum::zero().mask_tnum().has_equiv(0);
                and_not_zero_left(0);
            };
            let (p, q) = (self.to_tnum().tnum, t.to_tnum().tnum);
            assert(self.to_tnum().has(x) && t.to_tnum().has(y));
            assert(p.has(x) && ChoppedTnum::mk(q, w).has(y));
            assert(Self::mul_step(p, q, Self::zero(w)).has(chop(x * y + 0, w)));
            assert(x * y + 0 == x * y);
        };
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
