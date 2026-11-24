// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Layer 4: the executable Tnum, generic over the word width.
//!
//! `ExecTnum<W>` stores a Tnum in two native words. Every operation is the
//! Layer-3 `ChoppedTnum` operation at width `W::bits()`: each method ensures
//! `r.to_tn() == ct.op().tnum`, proved through the `BitWord` bridges, and takes
//! well-formedness and containment from the Layer-3 theorems.
#![allow(unused_imports)]
use crate::bitword::*;
use crate::bools::Bit;
use crate::chopped::*;
use crate::div::*;
use crate::facts::Facts;
use crate::interval::Interval;
use crate::lattice::*;
use crate::nats::*;
use crate::reduce::Refine;
use crate::tbit::TBit;
use crate::tnum::*;
use crate::word::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ExecTnum<W> {
    pub val: W,
    pub mask: W,
}

/// The bits of a cleared by m are disjoint from m.
pub proof fn disj_and_not(a: nat, m: nat)
    ensures disj(bw_and_not(a, m), m), disj(m, bw_and_not(a, m))
{
    assert forall|i: nat| #![auto] !(bit(bw_and_not(a, m), i).b() && bit(m, i).b()) by {
        and_not_bit(a, m, i);
    };
    disj_bits(bw_and_not(a, m), m);
    disj_bits(m, bw_and_not(a, m));
}

/// a - b for b <= a: no wrap.
pub fn sub_le<W: BitWord>(a: W, b: W) -> (r: W)
    requires b.view() <= a.view()
    ensures r.view() == a.view() - b.view()
{
    match a.checked_sub(b) {
        Some(d) => d,
        None => a,
    }
}

/// The low bit of a word is its head bit.
pub fn low_bit<W: BitWord>(x: W) -> (b: bool)
    ensures b == hd(x.view()).b()
{
    let one = W::one();
    proof { lemma_low_bit(x, one); }
    x.bit_and(one).eq(one)
}

/// 2^i as a word, for i < W.
pub fn pow2_word<W: BitWord>(i: u32) -> (r: W)
    requires (i as nat) < W::bits()
    ensures r.view() == exp(i as nat), r.view() > 0
{
    let r = W::one().shl_wrap(i);
    proof {
        lemma_exp_bits::<W>();
        assert(lshi(1, i as nat) == exp(i as nat));
        exp_pos(i as nat);
        exp_succ(i as nat);
        exp_le(i as nat + 1, W::bits());
        chop_id(exp(i as nat), W::bits());
    }
    r
}

/// Bit length of x, len(x), by a shift loop.
pub fn bit_len<W: BitWord>(x: W) -> (r: u32)
    ensures r as nat == len(x.view()), r as nat <= W::bits()
{
    let mut y = x;
    let mut n: u32 = 0;
    proof {
        lemma_fits(x);
        len_le(x.view(), W::bits());
        W::lemma_modulus();
    }
    while !y.eq(W::zero())
        invariant len(x.view()) == n as nat + len(y.view()), len(x.view()) <= W::bits(), 8 <= W::bits() <= 128
        decreases y.view()
    {
        let y1 = y.shr(1);
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            lemma_shr(y, 1, y1);
            assert(rshi(rsh(y.view()), 0) == rsh(y.view()));
        }
        y = y1;
        n += 1;
    }
    n
}

/// all_ones(p) as a word, for p <= W.
pub fn ones<W: BitWord>(p: u32) -> (r: W)
    requires (p as nat) <= W::bits()
    ensures r.view() == all_ones(p as nat)
{
    proof { lemma_exp_bits::<W>(); }
    if p == W::bit_width() {
        W::max()
    } else {
        let e = pow2_word::<W>(p);
        sub_le(e, W::one())
    }
}

/// Shift a remainder of fewer than W bits left by one and bring in bit i1 of
/// s: lsh_or_tb on the spec side.
pub fn shift_in<W: BitWord>(r: W, s: W, i1: u32, Ghost(e): Ghost<nat>) -> (out: W)
    requires (i1 as nat) < W::bits(), r.view() < exp(e), e + 1 <= W::bits()
    ensures out.view() == cons(r.view(), bit(s.view(), i1 as nat))
{
    let ghost w = W::bits();
    let sh = s.shr(i1);
    let bb = low_bit(sh);
    let b = if bb { W::one() } else { W::zero() };
    proof { W::lemma_modulus(); }
    let r2 = r.shl_wrap(1);
    let out = r2.bit_or(b);
    proof {
        let bt = bit(s.view(), i1 as nat);
        lemma_shr(s, i1 as nat, sh);
        bit_rshi(s.view(), i1 as nat);
        assert(b.view() == cons(0, bt));
        assert(lshi(r.view(), 1) == lsh(r.view())) by { assert(lshi(r.view(), 0) == r.view()); };
        lsh_is_times2(r.view());
        exp_succ(e);
        exp_le(e + 1, w);
        chop_id(lsh(r.view()), w);
        W::lemma_or(r2, b);
        assert forall|j: nat| #![auto] bit(bw_or(lsh(r.view()), cons(0, bt)), j) == bit(cons(r.view(), bt), j) by {
            or_bit(lsh(r.view()), cons(0, bt), j);
            bit_cons(r.view(), Bit::f(), j);
            bit_cons(0, bt, j);
            bit_cons(r.view(), bt, j);
            if j > 0 { bit_zero((j - 1) as nat); }
        };
        eq_from_bits(bw_or(lsh(r.view()), cons(0, bt)), cons(r.view(), bt));
    }
    out
}

impl<W: BitWord> ExecTnum<W> {
    pub open spec fn to_tn(self) -> Tnum {
        Tnum { val: self.val.view(), mask: self.mask.view() }
    }

    pub open spec fn wf(self) -> bool {
        self.to_tn().inv()
    }

    pub open spec fn has(self, x: W) -> bool {
        self.to_tn().has(x.view())
    }

    /// The Layer-3 Tnum at the word width.
    pub open spec fn ct(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.to_tn(), w: W::bits() }
    }

    pub proof fn lemma_ct(self)
        requires self.wf()
        ensures self.ct().inv()
    {
        lemma_fits(self.val);
        lemma_fits(self.mask);
    }

    /// A member of a word Tnum is a member of its Layer-3 Tnum.
    pub proof fn lemma_ct_has(self, c: W)
        requires self.has(c)
        ensures self.ct().has(c.view())
    {
        lemma_fits(c);
    }

    pub fn constant(n: W) -> (r: Self)
        ensures r.wf(), r.has(n), r.to_tn() == Tnum::unit(n.view())
    {
        let r = ExecTnum { val: n, mask: W::zero() };
        proof {
            disj_zero_r(n.view());
            Tnum::unit_has(n.view());
        }
        r
    }

    pub fn top() -> (r: Self)
        ensures r.wf(), forall|c: W| #![auto] r.has(c)
    {
        let r = ExecTnum { val: W::zero(), mask: W::max() };
        proof {
            lemma_exp_bits::<W>();
            disj_zero(r.mask.view());
            assert forall|c: W| #![auto] r.has(c) by {
                lemma_fits(c);
                r.to_tn().has_equiv(c.view());
                assert forall|i: nat| #![auto] bit(bw_and_not(c.view(), r.mask.view()), i) == bit(0, i) by {
                    and_not_bit(c.view(), r.mask.view(), i);
                    all_ones_bit(W::bits(), i);
                    bit_zero(i);
                    if i >= W::bits() { bit_above(c.view(), W::bits(), i); }
                };
                eq_from_bits(bw_and_not(c.view(), r.mask.view()), 0);
            };
        }
        r
    }

    pub fn bw_or(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.or(c2)),
            r.to_tn() == self.ct().bw_or(t.ct()).tnum,
    {
        let v = self.val.bit_or(t.val);
        let m = self.mask.bit_or(t.mask).bit_and(v.bit_not());
        let r = ExecTnum { val: v, mask: m };
        proof {
            W::lemma_or(self.val, t.val);
            W::lemma_or(self.mask, t.mask);
            lemma_and_not(self.mask.or(t.mask), v);
            disj_and_not(bw_or(self.mask.view(), t.mask.view()), v.view());
            self.lemma_ct(); t.lemma_ct();
            self.ct().or_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.or(c2)) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                W::lemma_or(c1, c2);
            };
        }
        r
    }

    pub fn bw_and(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.and(c2)),
            r.to_tn() == self.ct().bw_and(t.ct()).tnum,
    {
        let r = ExecTnum { val: self.val.bit_and(t.val), mask: self.mask.bit_or(t.mask) };
        proof {
            W::lemma_and(self.val, t.val);
            W::lemma_or(self.mask, t.mask);
            self.lemma_ct(); t.lemma_ct();
            self.ct().and_inv(t.ct());
            self.ct().and_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.and(c2)) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                W::lemma_and(c1, c2);
            };
        }
        r
    }

    pub fn bw_xor(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.xor(c2)),
            r.to_tn() == self.ct().bw_xor(t.ct()).tnum,
    {
        let v = self.val.bit_xor(t.val);
        let m = self.mask.bit_or(t.mask);
        let r = ExecTnum { val: v.bit_and(m.bit_not()), mask: m };
        proof {
            W::lemma_xor(self.val, t.val);
            W::lemma_or(self.mask, t.mask);
            lemma_and_not(v, m);
            disj_and_not(v.view(), m.view());
            self.lemma_ct(); t.lemma_ct();
            self.ct().xor_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.xor(c2)) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                W::lemma_xor(c1, c2);
            };
        }
        r
    }

    /// Bitwise NOT: flip the known bits, keep the unknown ones, the spec XOR
    /// with the all-ones word.
    pub fn bw_not(&self) -> (r: Self)
        requires self.wf()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.has(c.not()),
            r.to_tn() == self.ct().bw_not().tnum,
    {
        let ones = W::max();
        let x = self.val.bit_xor(ones);
        let r = ExecTnum { val: x.bit_and(self.mask.bit_not()), mask: self.mask };
        proof {
            let w = W::bits();
            lemma_exp_bits::<W>();
            assert(ones.view() == all_ones(w));
            W::lemma_xor(self.val, ones);
            lemma_and_not(x, self.mask);
            or_zero_r(self.mask.view());
            disj_and_not(x.view(), self.mask.view());
            self.lemma_ct();
            self.ct().not_sound();
            assert forall|c: W| #![auto] self.has(c) implies r.has(c.not()) by {
                self.lemma_ct_has(c);
                lemma_not(c);
            };
        }
        r
    }

    /// AND with the complement of the second operand, the spec bw_and_not.
    pub fn bw_and_not(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.and(c2.not())),
            r.to_tn() == self.ct().bw_and_not(t.ct()).tnum,
    {
        let a = self.val.bit_and(t.val.bit_not());
        let v = a.bit_and(t.mask.bit_not());
        let m = self.mask.bit_or(t.mask);
        let r = ExecTnum { val: v, mask: m };
        proof {
            lemma_and_not(self.val, t.val);
            lemma_and_not(a, t.mask);
            W::lemma_or(self.mask, t.mask);
            self.lemma_ct(); t.lemma_ct();
            self.ct().and_not_sound(t.ct());
            Self::and_not_inv(self.to_tn(), t.to_tn());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.and(c2.not())) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                lemma_and_not(c1, c2);
            };
        }
        r
    }

    /// bw_and_not preserves inv.
    proof fn and_not_inv(s: Tnum, t: Tnum)
        requires s.inv()
        ensures s.bw_and_not(t).inv()
    {
        let v = bw_and_not(bw_and_not(s.val, t.val), t.mask);
        let m = bw_or(s.mask, t.mask);
        disj_bits(s.val, s.mask);
        assert forall|i: nat| #![auto] !(bit(v, i).b() && bit(m, i).b()) by {
            and_not_bit(bw_and_not(s.val, t.val), t.mask, i);
            and_not_bit(s.val, t.val, i);
            or_bit(s.mask, t.mask, i);
        };
        disj_bits(v, m);
    }

    /// Logical shift right by k bits.
    pub fn rshi(&self, k: u32) -> (r: Self)
        requires self.wf(), (k as nat) < W::bits()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.to_tn().has(rshi(c.view(), k as nat)),
            r.to_tn() == self.ct().rshi(k as nat).tnum,
    {
        let r = ExecTnum { val: self.val.shr(k), mask: self.mask.shr(k) };
        proof {
            lemma_shr(self.val, k as nat, r.val);
            lemma_shr(self.mask, k as nat, r.mask);
            self.lemma_ct();
            self.ct().rshi_sound(k as nat);
            Self::rshi_inv(self.to_tn(), k as nat);
            assert forall|c: W| #![auto] self.has(c) implies r.to_tn().has(rshi(c.view(), k as nat)) by {
                self.lemma_ct_has(c);
            };
        }
        r
    }

    /// rshi preserves inv.
    proof fn rshi_inv(t: Tnum, k: nat)
        requires t.inv()
        ensures t.rshi(k).inv()
    {
        disj_bits(t.val, t.mask);
        assert forall|i: nat| #![auto] !(bit(rshi(t.val, k), i).b() && bit(rshi(t.mask, k), i).b()) by {
            bit_rshi_add(t.val, k, i);
            bit_rshi_add(t.mask, k, i);
        };
        disj_bits(rshi(t.val, k), rshi(t.mask, k));
    }

    /// Shift left by k bits, truncated to the width.
    pub fn lshi(&self, k: u32) -> (r: Self)
        requires self.wf(), (k as nat) < W::bits()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.to_tn().has(chop(lshi(c.view(), k as nat), W::bits())),
            r.to_tn() == self.ct().lshi(k as nat).tnum,
    {
        let r = ExecTnum { val: self.val.shl_wrap(k), mask: self.mask.shl_wrap(k) };
        proof {
            self.lemma_ct();
            self.ct().lshi_sound(k as nat);
            self.to_tn().lshi_inv(k as nat);
            chop_disj(lshi(self.val.view(), k as nat), lshi(self.mask.view(), k as nat), W::bits());
            assert forall|c: W| #![auto] self.has(c) implies r.to_tn().has(chop(lshi(c.view(), k as nat), W::bits())) by {
                self.lemma_ct_has(c);
            };
        }
        r
    }

    pub fn add(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int + c2.view() as int)),
            r.to_tn() == self.ct().add(t.ct()).tnum,
    {
        let lbv = self.val.wrapping_add(t.val);
        let lbm = self.mask.wrapping_add(t.mask);
        let ub = lbv.wrapping_add(lbm);
        let mask = ub.bit_xor(lbv).bit_or(self.mask).bit_or(t.mask);
        let r = ExecTnum { val: lbv.bit_and(mask.bit_not()), mask };
        proof {
            let w = W::bits();
            let (sv, sm, tv, tm) = (self.val.view(), self.mask.view(), t.val.view(), t.mask.view());
            lemma_add(self.val, t.val);
            lemma_add(self.mask, t.mask);
            lemma_add(lbv, lbm);
            W::lemma_xor(ub, lbv);
            W::lemma_or(ub.xor(lbv), self.mask);
            W::lemma_or(ub.xor(lbv).or(self.mask), t.mask);
            lemma_and_not(lbv, mask);
            disj_and_not(lbv.view(), mask.view());
            // The Layer-3 intermediates, chopped step by step.
            let lbv_s = nat_add(sv, tv);
            let lbm_s = nat_add(sm, tm);
            let ub_s = nat_add(lbv_s, lbm_s);
            let mask_s = bw_or(bw_or(bw_xor(ub_s, lbv_s), sm), tm);
            lemma_fits(self.val); lemma_fits(self.mask); lemma_fits(t.val); lemma_fits(t.mask);
            chop_nat_add(lbv_s, lbm_s, w);
            assert(ub.view() == chop(ub_s, w));
            chop_bw_xor(ub_s, lbv_s, w);
            chop_bw_or(bw_xor(ub_s, lbv_s), sm, w);
            chop_bw_or(bw_or(bw_xor(ub_s, lbv_s), sm), tm, w);
            chop_bw_and_not(lbv_s, mask_s, w);
            assert(chop(mask_s, w) == mask.view());
            assert(chop(bw_and_not(lbv_s, mask_s), w) == r.val.view());
            assert(r.to_tn() == self.ct().add(t.ct()).tnum);
            self.lemma_ct(); t.lemma_ct();
            self.ct().add_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int + c2.view() as int)) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                lemma_add(c1, c2);
            };
        }
        r
    }

    /// Two's complement negation, encoded as NOT then add one: the spec neg
    /// is bw_not followed by add of the unit 1.
    pub fn neg(&self) -> (r: Self)
        requires self.wf()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.has(W::from_int(0 - c.view() as int)),
            r.to_tn() == self.ct().neg().tnum,
    {
        let n = self.bw_not();
        let one = Self::constant(W::one());
        let r = n.add(&one);
        proof {
            W::lemma_modulus();
            self.lemma_ct();
            self.ct().neg_sound();
            assert(one.to_tn() == Tnum::unit(1));
            assert(r.to_tn() == self.ct().neg().tnum);
            assert forall|c: W| #![auto] self.has(c) implies r.has(W::from_int(0 - c.view() as int)) by {
                self.lemma_ct_has(c);
                lemma_neg(c);
            };
        }
        r
    }

    /// Subtraction, encoded as adding the negation: the spec sub.
    pub fn sub(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int - c2.view() as int)),
            r.to_tn() == self.ct().sub(t.ct()).tnum,
    {
        let nt = t.neg();
        let r = self.add(&nt);
        proof {
            W::lemma_modulus();
            self.lemma_ct(); t.lemma_ct();
            self.ct().sub_sound(t.ct());
            assert(r.to_tn() == self.ct().sub(t.ct()).tnum);
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int - c2.view() as int)) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                lemma_sub(c1, c2);
            };
        }
        r
    }

    pub fn join(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.has(c),
            forall|c: W| #![auto] t.has(c) ==> r.has(c),
            r.to_tn() == self.ct().join(t.ct()).tnum,
    {
        let v = self.val.bit_and(t.val);
        let u = self.val.bit_xor(self.mask).bit_or(t.val.bit_xor(t.mask));
        let r = ExecTnum { val: v, mask: v.bit_xor(u) };
        proof {
            W::lemma_and(self.val, t.val);
            W::lemma_xor(self.val, self.mask);
            W::lemma_xor(t.val, t.mask);
            W::lemma_or(self.val.xor(self.mask), t.val.xor(t.mask));
            W::lemma_xor(v, u);
            self.to_tn().join_inv(t.to_tn());
            self.to_tn().join_sound(t.to_tn());
        }
        r
    }

    /// Meet: known where either operand is known. `Bot` when the operands
    /// disagree on a bit both know; otherwise exactly the common members
    /// (`Tnum::meet_exact`).
    pub fn meet(&self, t: &Self) -> (r: BotOr<Self>)
        requires self.wf(), t.wf()
        ensures
            match r {
                BotOr::Bot => forall|c: W| #![auto] self.has(c) ==> !t.has(c),
                BotOr::Val(m) => m.wf() && forall|c: W| #![auto] m.has(c) == (self.has(c) && t.has(c)),
            },
    {
        let k = self.val.bit_xor(t.val).bit_and(self.mask.bit_or(t.mask).bit_not());
        proof {
            W::lemma_xor(self.val, t.val);
            W::lemma_or(self.mask, t.mask);
            lemma_and_not(self.val.xor(t.val), self.mask.or(t.mask));
        }
        if !k.eq(W::zero()) {
            proof {
                assert forall|c: W| #![auto] self.has(c) implies !t.has(c) by {
                    self.to_tn().conflict_empty(t.to_tn(), c.view());
                };
            }
            return BotOr::Bot;
        }
        let v = self.val.bit_or(t.val);
        let u = self.val.bit_xor(self.mask).bit_and(t.val.bit_xor(t.mask));
        let m = v.bit_xor(u);
        let r = ExecTnum { val: v.bit_and(m.bit_not()), mask: m };
        proof {
            W::lemma_or(self.val, t.val);
            W::lemma_xor(self.val, self.mask);
            W::lemma_xor(t.val, t.mask);
            W::lemma_and(self.val.xor(self.mask), t.val.xor(t.mask));
            W::lemma_xor(v, u);
            lemma_and_not(v, m);
            self.to_tn().meet_exact(t.to_tn());
            assert(r.to_tn() == self.to_tn().meet_n(t.to_tn()));
        }
        BotOr::Val(r)
    }

    /// Multiplication by pair-join (Tnum::pair_mul on W-bit registers). Start
    /// from the exact product of the known parts; for each unknown bit l of t,
    /// join the accumulator with itself plus the constant self.val << l; then
    /// for each unknown bit k of self, join it with itself plus t << k. The two
    /// loops shift the registers as the L2 recursions pj_const and pj_tnum do,
    /// and each step is the chopped L2 step (chop_add_bitwise, chop_join,
    /// chop_lsh_tn).
    pub fn mul(&self, t: &Self) -> (r: Self)
        requires self.wf(), t.wf()
        ensures
            r.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.to_tn().has(chop(prod(c1.view(), c2.view()), W::bits())),
            r.to_tn() == self.ct().mul(t.ct()).tnum,
    {
        let ghost w: nat = W::bits();
        let ghost t0 = self.to_tn();
        let ghost t1 = t.to_tn();
        let ghost acc0 = Tnum::unit(prod(t0.val, t1.val));
        let ghost cst = Tnum::pj_const(t0.val, t1.mask, acc0);
        let ghost whole = Tnum::pj_tnum(t1, t0.mask, cst);
        let pv = self.val.mul_wrap(t.val);
        let mut acc = ExecTnum { val: pv, mask: W::zero() };
        let mut s = self.val;
        let mut ym = t.mask;
        let ghost mut ss: nat = t0.val;
        let ghost mut acc_s: Tnum = acc0;
        proof {
            W::lemma_modulus();
            lemma_exp_bits::<W>();
            exp_pos(w);
            chop_id(0, w);
            lemma_fits(self.val);
            disj_zero_r(pv.view());
            disj_zero_r(prod(t0.val, t1.val));
        }
        // Phase 1: the unknown bits of t, with the shifted known part of self.
        while !ym.eq(W::zero())
            invariant
                w == W::bits(), 8 <= w,
                acc.wf(),
                acc.to_tn() == acc_s.chop_tn(w),
                acc_s.inv(),
                s.view() == chop(ss, w),
                Tnum::pj_const(ss, ym.view(), acc_s) == cst,
            decreases ym.view()
        {
            let ghost acc_s0 = acc_s;
            let ghost ss0 = ss;
            if low_bit(ym) {
                let c = Self::constant(s);
                let sum = acc.add(&c);
                acc = acc.join(&sum);
                proof {
                    let u = Tnum::unit(ss0);
                    exp_pos(w);
                    chop_id(0, w);
                    assert(c.to_tn() == u.chop_tn(w));
                    disj_zero_r(ss0);
                    Tnum::chop_add_bitwise(acc_s0, u, w);
                    acc_s0.add_bitwise_eq(u);
                    Tnum::chop_join(acc_s0, acc_s0.add(u), w);
                    Tnum::pj_step_inv(acc_s0, u);
                    acc_s = acc_s0.join(acc_s0.add(u));
                }
            }
            let ym1 = ym.shr(1);
            let s1 = s.shl_wrap(1);
            proof {
                vstd::arithmetic::power2::lemma2_to64();
                lemma_shr(ym, 1, ym1);
                assert(rshi(rsh(ym.view()), 0) == rsh(ym.view()));
                assert(lshi(s.view(), 1) == lsh(s.view())) by { assert(lshi(s.view(), 0) == s.view()); };
                chop_lsh(ss0, w);
                ss = lsh(ss0);
            }
            s = s1;
            ym = ym1;
        }
        let mut y = *t;
        let mut xm = self.mask;
        let ghost mut ys: Tnum = t1;
        proof {
            lemma_fits(t.val);
            lemma_fits(t.mask);
        }
        // Phase 2: the unknown bits of self, with t shifted.
        while !xm.eq(W::zero())
            invariant
                w == W::bits(), 8 <= w,
                acc.wf(), y.wf(),
                acc.to_tn() == acc_s.chop_tn(w),
                y.to_tn() == ys.chop_tn(w),
                acc_s.inv(), ys.inv(),
                Tnum::pj_tnum(ys, xm.view(), acc_s) == whole,
            decreases xm.view()
        {
            let ghost acc_s0 = acc_s;
            let ghost ys0 = ys;
            if low_bit(xm) {
                let sum = acc.add(&y);
                acc = acc.join(&sum);
                proof {
                    Tnum::chop_add_bitwise(acc_s0, ys0, w);
                    acc_s0.add_bitwise_eq(ys0);
                    Tnum::chop_join(acc_s0, acc_s0.add(ys0), w);
                    Tnum::pj_step_inv(acc_s0, ys0);
                    acc_s = acc_s0.join(acc_s0.add(ys0));
                }
            }
            y = y.lsh();
            let xm1 = xm.shr(1);
            proof {
                Tnum::chop_lsh_tn(ys0, w);
                disj_cons(ys0.val, Bit::f(), ys0.mask, Bit::f());
                ys = ys0.lsh();
                vstd::arithmetic::power2::lemma2_to64();
                lemma_shr(xm, 1, xm1);
                assert(rshi(rsh(xm.view()), 0) == rsh(xm.view()));
            }
            xm = xm1;
        }
        let r = acc;
        proof {
            self.lemma_ct(); t.lemma_ct();
            assert(r.to_tn() == self.ct().mul(t.ct()).tnum);
            self.ct().mul_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2)
                implies r.to_tn().has(chop(prod(c1.view(), c2.view()), W::bits())) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                nat_mul_acc_correct(c1.view(), c2.view(), 0);
            };
        }
        r
    }

    /// Meet by masks (Tnum::meet_m): unknown where both are unknown, the known
    /// bits of either elsewhere. Unlike meet, no normalization; well formed even
    /// for disjoint operands.
    pub fn meet_m(&self, t: &Self) -> (r: Self)
        ensures r.wf(), r.to_tn() == self.to_tn().meet_m(t.to_tn())
    {
        let m = self.mask.bit_and(t.mask);
        let o = self.val.bit_or(t.val);
        let v = o.bit_and(m.bit_not());
        proof {
            W::lemma_and(self.mask, t.mask);
            W::lemma_or(self.val, t.val);
            lemma_and_not(o, m);
            disj_and_not(o.view(), m.view());
        }
        ExecTnum { val: v, mask: m }
    }

    /// The Tnum of the range [lo, hi] (Tnum::range_tn): the common prefix of lo
    /// and hi, unknown from the highest differing bit down.
    pub fn range_tn(lo: W, hi: W) -> (r: Self)
        ensures r.wf(), r.to_tn() == Tnum::range_tn(lo.view(), hi.view())
    {
        let x = lo.bit_xor(hi);
        let p = bit_len(x);
        let m: W = ones(p);
        proof {
            W::lemma_xor(lo, hi);
            lemma_and_not(lo, m);
            Tnum::range_tn_inv(lo.view(), hi.view());
        }
        ExecTnum { val: lo.bit_and(m.bit_not()), mask: m }
    }

    /// Chop to the low p bits (Tnum::chop_tn), p <= W.
    pub fn chop_to(&self, p: u32) -> (r: Self)
        requires self.wf(), (p as nat) <= W::bits()
        ensures
            r.wf(),
            r.to_tn() == self.to_tn().chop_tn(p as nat),
            r.val.view() < exp(p as nat),
            r.mask.view() < exp(p as nat),
    {
        let o: W = ones(p);
        let r = ExecTnum { val: self.val.bit_and(o), mask: self.mask.bit_and(o) };
        proof {
            W::lemma_and(self.val, o);
            W::lemma_and(self.mask, o);
            chop_and_ones(self.val.view(), p as nat);
            chop_and_ones(self.mask.view(), p as nat);
            chop_lt(self.val.view(), p as nat);
            chop_lt(self.mask.view(), p as nat);
            chop_disj(self.val.view(), self.mask.view(), p as nat);
        }
        r
    }

    /// Guarded long division (Tnum::div_g on W-bit registers): scan the
    /// dividend from the top bit; subtract when the shifted remainder is surely
    /// at least the divisor, keep it when surely below, and otherwise join the
    /// kept side (below d.max()) with the subtracted side (at most
    /// r1.max() - d.min() and below d.max()). After step j the remainder is
    /// chopped to min(j, k) bits, k = len(d.max()); quotient and remainder are
    /// finally met with their range bounds. The subtraction runs at W bits
    /// where the spec uses w + 1; the chop to min(j, k) <= W bits makes them
    /// agree (Tnum::sub_chop_width, Tnum::div_guard_chop_width).
    ///
    /// Requires t.val > 0, i.e. no member of t is zero; divrem handles a
    /// divisor that may be zero.
    pub fn divrem_g(&self, t: &Self) -> (res: (Self, Self))
        requires self.wf(), t.wf(), t.val.view() > 0
        ensures
            res.0.wf(), res.1.wf(),
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2)
                ==> res.0.to_tn().has(c1.view() / c2.view()) && res.1.to_tn().has(c1.view() % c2.view()),
            res.0.to_tn() == self.ct().div_g(t.ct()).0.tnum,
            res.1.to_tn() == self.ct().div_g(t.ct()).1.tnum,
    {
        let ghost w: nat = W::bits();
        let ghost n0 = self.to_tn();
        let ghost d0 = t.to_tn();
        let bits = W::bit_width();
        let dmin = t.val;
        let dmax = t.val.bit_or(t.mask);
        let k = bit_len(dmax);
        proof {
            W::lemma_modulus();
            lemma_exp_bits::<W>();
            W::lemma_or(t.val, t.mask);
            W::lemma_or_ge(t.val, t.mask);
        }
        let ghost whole = Tnum::div_loop_g(n0, d0, w, k as nat, w, Tnum::zero(), Tnum::zero());
        let mut q = ExecTnum { val: W::zero(), mask: W::zero() };
        let mut r = ExecTnum { val: W::zero(), mask: W::zero() };
        let ghost mut qs = Tnum::zero();
        let ghost mut rs = Tnum::zero();
        let mut i: u32 = bits;
        proof {
            disj_zero(0);
            assert(exp(0) == 1) by { assert(lshi(1, 0) == 1); }
        }
        while i > 0
            invariant
                w == W::bits(), bits as nat == w, 8 <= w <= 128, i <= bits,
                k as nat == len(d0.max()), k <= bits,
                dmax.view() == d0.max(), dmin.view() == d0.min(), dmin.view() > 0, dmax.view() >= dmin.view(),
                n0 == self.to_tn(), d0 == t.to_tn(), self.wf(), t.wf(),
                r.wf(), r.to_tn() == rs, q.to_tn() == qs,
                r.val.view() < exp((w - i) as nat), r.mask.view() < exp((w - i) as nat),
                Tnum::div_loop_g(n0, d0, w, k as nat, i as nat, qs, rs) == whole,
            decreases i
        {
            let i1 = i - 1;
            let ghost i1n = i1 as nat;
            let ghost nbit = TBit { val: bit(n0.val, i1n), mask: bit(n0.mask, i1n) };
            let ghost rs0 = rs;
            let ghost qs0 = qs;
            let ghost r1s = rs0.lsh_or_tb(nbit);
            let r1v = shift_in(r.val, self.val, i1, Ghost((w - i) as nat));
            let r1m = shift_in(r.mask, self.mask, i1, Ghost((w - i) as nat));
            let r1 = ExecTnum { val: r1v, mask: r1m };
            proof {
                disj_bits(r.val.view(), r.mask.view());
                disj_bits(self.val.view(), self.mask.view());
                assert forall|j: nat| #![auto] !(bit(r1v.view(), j).b() && bit(r1m.view(), j).b()) by {
                    bit_cons(r.val.view(), bit(self.val.view(), i1n), j);
                    bit_cons(r.mask.view(), bit(self.mask.view(), i1n), j);
                };
                disj_bits(r1v.view(), r1m.view());
                assert(r1.to_tn() == r1s);
            }
            let j = bits - i1;
            let m = if j <= k { j } else { k };
            let r1max = r1v.bit_or(r1m);
            proof {
                W::lemma_or(r1v, r1m);
                assert(m as nat == nmin((w - i1n) as nat, k as nat));
            }
            let ghost q0 = q;
            if dmax.le(r1v) {
                let p2: W = pow2_word(i1);
                q = ExecTnum { val: q.val.bit_or(p2), mask: q.mask };
                let r2 = r1.sub(t);
                r = r2.chop_to(m);
                proof {
                    W::lemma_or(q0.val, p2);
                    qs = Tnum { val: bw_or(qs0.val, exp(i1n)), mask: qs0.mask };
                    Tnum::sub_chop_width(r1s, d0, w, w + 1, m as nat);
                    rs = r1s.sub(d0, w + 1).chop_tn(m as nat);
                }
            } else if r1max.lt(dmin) {
                r = r1.chop_to(m);
                proof { rs = r1s.chop_tn(m as nat); }
            } else {
                let p2: W = pow2_word(i1);
                q = ExecTnum { val: q.val, mask: q.mask.bit_or(p2) };
                let one = W::one();
                let dm1 = sub_le(dmax, one);
                let rk = Self::range_tn(W::zero(), dm1);
                let keep = r1.meet_m(&rk);
                let diff = sub_le(r1max, dmin);
                let hi = if diff.lt(dmax) { diff } else { dm1 };
                let rh = Self::range_tn(W::zero(), hi);
                let sb = r1.sub(t);
                let sm = sb.meet_m(&rh);
                let r2 = keep.join(&sm);
                r = r2.chop_to(m);
                proof {
                    W::lemma_or(q0.mask, p2);
                    qs = Tnum { val: qs0.val, mask: bw_or(qs0.mask, exp(i1n)) };
                    Tnum::div_guard_chop_width(r1s, d0, w, m as nat);
                    rs = Tnum::div_guard(r1s, d0, w).chop_tn(m as nat);
                }
            }
            proof {
                assert(r.to_tn() == rs);
                assert(q.to_tn() == qs);
                exp_le(m as nat, (w - i1n) as nat);
            }
            i = i1;
        }
        let nlo = self.val;
        let nhi = self.val.bit_or(self.mask);
        let one = W::one();
        let rq = Self::range_tn(nlo.udiv(dmax), nhi.udiv(dmin));
        let qf = q.meet_m(&rq);
        proof { W::lemma_or(self.val, self.mask); }
        let rhi = if nhi.lt(dmax) { nhi } else { sub_le(dmax, one) };
        let rr = Self::range_tn(W::zero(), rhi);
        let rf = r.meet_m(&rr);
        proof {
            self.lemma_ct(); t.lemma_ct();
            let sp = n0.div_g(d0, w, k as nat);
            assert(qf.to_tn() == sp.0);
            assert(rf.to_tn() == sp.1);
            lemma_fits(qf.val); lemma_fits(qf.mask);
            lemma_fits(rf.val); lemma_fits(rf.mask);
            assert(qf.to_tn() == self.ct().div_g(t.ct()).0.tnum);
            assert(rf.to_tn() == self.ct().div_g(t.ct()).1.tnum);
            self.ct().div_g_sound(t.ct());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2)
                implies qf.to_tn().has(c1.view() / c2.view()) && rf.to_tn().has(c1.view() % c2.view()) by {
                self.lemma_ct_has(c1); t.lemma_ct_has(c2);
            };
        }
        (qf, rf)
    }

    /// Equality of an executable division result with the Layer-3 one.
    pub open spec fn eq_div(res: Option<(Self, Self)>, g: Option<(ChoppedTnum, ChoppedTnum)>) -> bool {
        match (res, g) {
            (None, None) => true,
            (Some(p), Some(c)) => p.0.wf() && p.1.wf() && p.0.to_tn() == c.0.tnum && p.1.to_tn() == c.1.tnum,
            _ => false,
        }
    }

    /// Division by the nonzero members of t (ChoppedTnum::div_nz on W-bit
    /// registers). When t.val > 0 this is divrem_g. Otherwise t may be zero:
    /// divrem_g runs on the top piece (2^i, t.mask & (2^i - 1)) of each unknown
    /// bit i of t, the members whose highest set bit is i, and the results are
    /// joined. None when t is {0}, i.e. every divisor is zero; t.val == 0 tells
    /// the caller that some may be.
    pub fn divrem(&self, t: &Self) -> (res: Option<(Self, Self)>)
        requires self.wf(), t.wf()
        ensures
            res is None <==> (t.val.view() == 0 && t.mask.view() == 0),
            Self::eq_div(res, self.ct().div_nz(t.ct())),
            match res {
                Some(p) => p.0.wf() && p.1.wf()
                    && forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) && c2.view() != 0
                        ==> p.0.to_tn().has(c1.view() / c2.view()) && p.1.to_tn().has(c1.view() % c2.view()),
                None => true,
            },
    {
        let ghost w: nat = W::bits();
        let ghost ct_s = self.ct();
        let ghost ct_t = t.ct();
        proof {
            self.lemma_ct(); t.lemma_ct();
            ct_s.div_nz_sound(ct_t);
        }
        if !t.val.eq(W::zero()) {
            return Some(self.divrem_g(t));
        }
        let bits = W::bit_width();
        let mut acc: Option<(Self, Self)> = None;
        let mut i: u32 = 0;
        while i < bits
            invariant
                w == W::bits(), bits as nat == w,
                i <= bits,
                t.val.view() == 0, self.wf(), t.wf(),
                ct_s == self.ct(), ct_t == t.ct(),
                ct_s.inv(), ct_t.inv(),
                Self::eq_div(acc, ct_s.div_z(ct_t, i as nat)),
            decreases bits - i
        {
            let ghost iv: nat = i as nat;
            let sh = t.mask.shr(i);
            proof {
                lemma_shr(t.mask, iv, sh);
                bit_rshi(t.mask.view(), iv);
            }
            if low_bit(sh) {
                let bitv: W = pow2_word(i);
                let lowm = sub_le(bitv, W::one());
                let piece = ExecTnum { val: bitv, mask: t.mask.bit_and(lowm) };
                proof {
                    W::lemma_and(t.mask, lowm);
                    chop_and_ones(t.mask.view(), iv);
                    assert(piece.to_tn() == ct_t.top_piece(iv).tnum);
                    ct_t.top_piece_inv(iv);
                    assert(piece.ct() == ct_t.top_piece(iv));
                }
                let p = self.divrem_g(&piece);
                acc = match acc {
                    None => Some(p),
                    Some(a) => Some((a.0.join(&p.0), a.1.join(&p.1))),
                };
            }
            i += 1;
        }
        proof {
            // The loop ran over every bit, so acc is div_z(t, w), which is div_nz.
            if let Some(pp) = acc {
                assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) && c2.view() != 0
                    implies pp.0.to_tn().has(c1.view() / c2.view()) && pp.1.to_tn().has(c1.view() % c2.view()) by {
                    self.lemma_ct_has(c1); t.lemma_ct_has(c2);
                };
            }
        }
        acc
    }

    pub fn min_val(&self) -> (r: W)
        ensures r == self.val
    {
        self.val
    }

    pub fn max_val(&self) -> (r: W)
        ensures r.view() == bw_or(self.val.view(), self.mask.view())
    {
        proof { W::lemma_or(self.val, self.mask); }
        self.val.bit_or(self.mask)
    }

    pub fn is_const(&self) -> (b: bool)
        ensures b == (self.mask.view() == 0)
    {
        self.mask.eq(W::zero())
    }

    pub fn rsh(&self) -> (r: Self)
        requires self.wf()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.to_tn().has(rsh(c.view())),
            r.to_tn() == self.ct().rsh().tnum,
    {
        proof { W::lemma_modulus(); }
        let r = self.rshi(1);
        proof {
            assert(rshi(rsh(self.val.view()), 0) == rsh(self.val.view()));
            assert(rshi(rsh(self.mask.view()), 0) == rsh(self.mask.view()));
            assert forall|c: W| #![auto] self.has(c) implies r.to_tn().has(rsh(c.view())) by {
                assert(rshi(rsh(c.view()), 0) == rsh(c.view()));
            };
        }
        r
    }

    pub fn lsh(&self) -> (r: Self)
        requires self.wf()
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.to_tn().has(chop(lsh(c.view()), W::bits())),
            r.to_tn() == self.ct().lsh().tnum,
    {
        proof { W::lemma_modulus(); }
        let r = self.lshi(1);
        proof {
            assert(lshi(self.val.view(), 0) == self.val.view());
            assert(lshi(self.mask.view(), 0) == self.mask.view());
            assert forall|c: W| #![auto] self.has(c) implies r.to_tn().has(chop(lsh(c.view()), W::bits())) by {
                assert(lshi(c.view(), 0) == c.view());
            };
        }
        r
    }
}

/// The Tnum lattice: `leq` is mask inclusion with agreeing known bits, `join`
/// and `meet` are the operations above, and `widen` is `join` (a chain of
/// Tnums gains at least one unknown bit per strict step, so it stabilizes
/// within W + 1 steps).
impl<W: BitWord> Domain for ExecTnum<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        self.to_tn().inv()
    }

    open spec fn gamma(&self, c: W) -> bool {
        self.has(c)
    }

    fn dup(&self) -> (r: Self) {
        *self
    }

    fn top() -> (r: Self) {
        ExecTnum::top()
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        let a = self.mask.bit_and(o.mask.bit_not());
        let v = self.val.bit_and(o.mask.bit_not());
        let b = a.eq(W::zero()) && v.eq(o.val);
        proof {
            lemma_and_not(self.mask, o.mask);
            lemma_and_not(self.val, o.mask);
            if b {
                self.to_tn().leq_sound(o.to_tn());
            }
        }
        b
    }

    fn join(&self, o: &Self) -> (r: Self) {
        ExecTnum::join(self, o)
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        ExecTnum::meet(self, o)
    }

    fn widen(&self, o: &Self) -> (r: Self) {
        ExecTnum::join(self, o)
    }
}

/// A well-formed Tnum holds its value, and is determined by its value and its
/// maximum `val | mask` (`Tnum::canonical`).
impl<W: BitWord> Canonical for ExecTnum<W> {
    proof fn lemma_nonempty(&self) {
        self.to_tn().val_max_has();
        assert(self.gamma(self.val));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        let (am, bm) = (a.val.or(a.mask), b.val.or(b.mask));
        W::lemma_or(a.val, a.mask);
        W::lemma_or(b.val, b.mask);
        a.to_tn().val_max_has();
        b.to_tn().val_max_has();
        assert(a.gamma(a.val) == b.gamma(a.val));
        assert(a.gamma(am) == b.gamma(am));
        assert(a.gamma(b.val) == b.gamma(b.val));
        assert(a.gamma(bm) == b.gamma(bm));
        a.to_tn().canonical(b.to_tn());
        W::lemma_view_injective(a.val, b.val);
        W::lemma_view_injective(a.mask, b.mask);
    }
}

/// A Tnum writes its bounds `[val, val | mask]` to the unsigned interval
/// field, and refines by meeting with the Tnum of the interval's range
/// (`range_tn`: the common prefix of its bounds is known).
impl<W: BitWord> Refine for ExecTnum<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        let hi = self.max_val();
        match Interval::new(self.val, hi) {
            Some(iv) => {
                let f = Facts::from_interval(iv);
                proof {
                    assert forall|x: W| self.gamma(x) implies #[trigger] f.gamma(x) by {
                        self.to_tn().has_bounds(x.view());
                    }
                }
                BotOr::Val(f)
            },
            None => BotOr::Val(Facts::top()),
        }
    }

    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        let u = f.interval();
        let (lo, hi) = u.bounds();
        let g = Self::range_tn(lo, hi);
        let r = ExecTnum::meet(self, &g);
        proof {
            assert forall|x: W| self.gamma(x) && f.gamma(x) implies #[trigger] r.gamma(x) by {
                assert(u.gamma(x));
                Tnum::range_tn_has(lo.view(), hi.view(), x.view());
                assert(g.has(x));
            }
        }
        r
    }
}

} // verus!
