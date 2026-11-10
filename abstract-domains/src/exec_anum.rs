// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Layer 4: the executable Anum, generic over the word width.
//!
//! `ExecAnum<W>` stores an Anum's base and span in two native words. Every
//! operation is the Layer-3 `ChoppedAnum` operation at width `W::bits()`: each
//! method ensures `r.to_an() == ca.op().anum` (except `sub` and `div_const`,
//! which ensure containment only, and `meet`, which normalizes), proved through
//! the `BitWord` bridges, and takes containment from the Layer-3 theorems.
#![allow(unused_imports)]
use crate::anum::Anum;
use crate::bitword::*;
use crate::bools::Bit;
use crate::chopped::*;
use crate::div::*;
use crate::exec_tnum::*;
use crate::lattice::BotOr;
use crate::nats::*;
use crate::tbit::TBit;
use crate::tnum::*;
use crate::word::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ExecAnum<W> {
    pub base: W,
    pub span: W,
}

/// from_int is the identity below the modulus.
pub proof fn lemma_no_wrap<W: Word>(i: int)
    requires 0 <= i < W::modulus()
    ensures W::from_int(i).view() == i
{
    W::lemma_from_int(i);
    vstd::arithmetic::div_mod::lemma_small_mod(i as nat, W::modulus());
}

/// a + b + c + d < 2^W, by checked additions.
pub fn sum4_fits<W: Word>(a: W, b: W, c: W, d: W) -> (r: bool)
    ensures r == (a.view() + b.view() + c.view() + d.view() < W::modulus())
{
    match a.checked_add(b) {
        None => false,
        Some(x) => match c.checked_add(d) {
            None => false,
            Some(y) => match x.checked_add(y) {
                None => false,
                Some(_z) => {
                    proof { _z.lemma_view_bounded(); }
                    true
                },
            },
        },
    }
}

/// The number of set bits of x, by a shift loop.
fn popcount<W: BitWord>(x: W) -> (r: u32)
    ensures r as nat <= W::bits()
{
    let mut y = x;
    let mut n: u32 = 0;
    proof {
        lemma_fits(x);
        len_le(x.view(), W::bits());
        W::lemma_modulus();
    }
    while !y.eq(W::zero())
        invariant n as nat + len(y.view()) <= W::bits(), 8 <= W::bits() <= 128
        decreases y.view()
    {
        if low_bit(y) {
            n += 1;
        }
        let y1 = y.shr(1);
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            lemma_shr(y, 1, y1);
            assert(rshi(rsh(y.view()), 0) == rsh(y.view()));
        }
        y = y1;
    }
    n
}

/// x ^ 0 == x.
pub proof fn xor_zero(n: nat)
    ensures bw_xor(n, 0) == n
{
    assert forall|i: nat| #![auto] bit(bw_xor(n, 0), i) == bit(n, i) by {
        xor_bit(n, 0, i);
        bit_zero(i);
    };
    eq_from_bits(bw_xor(n, 0), n);
}

/// The span of an L2 Anum add: the add_bitwise mask (s1 + s2) | s1 | s2.
pub proof fn add_span(s1: nat, s2: nat)
    ensures Tnum::ctor(0, s1).add(Tnum::ctor(0, s2)).mask == bw_or(bw_or(nat_add(s1, s2), s1), s2)
{
    disj_zero(s1);
    disj_zero(s2);
    Tnum::ctor(0, s1).add_bitwise_eq(Tnum::ctor(0, s2));
    nat_add_correct(0, 0);
    nat_add_correct(0, nat_add(s1, s2));
    xor_zero(nat_add(s1, s2));
}

impl<W: BitWord> ExecAnum<W> {
    pub open spec fn to_an(self) -> Anum {
        Anum { base: self.base.view(), span: self.span.view() }
    }

    pub open spec fn has(self, x: W) -> bool {
        self.to_an().has(x.view())
    }

    /// The Layer-3 Anum at the word width.
    pub open spec fn ca(self) -> ChoppedAnum {
        ChoppedAnum { anum: self.to_an(), w: W::bits() }
    }

    pub proof fn lemma_ca(self)
        ensures self.ca().inv()
    {
        self.to_an().to_tnum_inv();
        lemma_fits(self.base);
        lemma_fits(self.span);
    }

    /// A member of a word Anum is a member of its Layer-3 Anum.
    pub proof fn lemma_ca_has(self, c: W)
        requires self.has(c)
        ensures self.ca().has(c.view())
    {
        lemma_fits(c);
    }

    /// The Layer-3 top holds every value below 2^W.
    proof fn lemma_top_has(n: nat)
        requires n < W::modulus()
        ensures ChoppedAnum::top(W::bits()).anum.has(n)
    {
        lemma_exp_bits::<W>();
        ChoppedAnum::top_sound(W::bits());
        chop_id(n, W::bits());
        assert(fits(n, W::bits()));
        assert(ChoppedAnum::top(W::bits()).has(n));
    }

    pub fn constant(n: W) -> (r: Self)
        ensures r.has(n), r.to_an() == (Anum { base: n.view(), span: 0 })
    {
        let r = ExecAnum { base: n, span: W::zero() };
        proof {
            Tnum::unit_has(0);
            assert(nat_sub(n.view(), n.view()) == 0);
        }
        r
    }

    pub fn top() -> (r: Self)
        ensures forall|n: W| #![auto] r.has(n), r.to_an() == ChoppedAnum::top(W::bits()).anum
    {
        let r = ExecAnum { base: W::zero(), span: W::max() };
        proof {
            lemma_exp_bits::<W>();
            assert forall|n: W| #![auto] r.has(n) by {
                n.lemma_view_bounded();
                Self::lemma_top_has(n.view());
            };
        }
        r
    }

    /// Bounded addition, ChoppedAnum::add_w: the L2 add when the two maxima sum
    /// below 2^W, so no member sum wraps; top otherwise.
    pub fn add(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int + c2.view() as int)),
            r.to_an() == self.ca().add_w(t.ca()).anum,
    {
        let (b1, s1, b2, s2) = (self.base, self.span, t.base, t.span);
        let fit = sum4_fits(b1, s1, b2, s2);
        let s12 = s1.wrapping_add(s2);
        let r = if fit {
            ExecAnum { base: b1.wrapping_add(b2), span: s12.bit_or(s1).bit_or(s2) }
        } else {
            Self::top()
        };
        proof {
            lemma_exp_bits::<W>();
            self.lemma_ca(); t.lemma_ca();
            self.ca().add_w_sound(t.ca());
            if fit {
                lemma_no_wrap::<W>(b1.view() + b2.view() as int);
                lemma_no_wrap::<W>(s1.view() + s2.view() as int);
                nat_add_correct(b1.view(), b2.view());
                nat_add_correct(s1.view(), s2.view());
                W::lemma_or(s12, s1);
                W::lemma_or(s12.or(s1), s2);
                add_span(s1.view(), s2.view());
            }
            assert(r.to_an() == self.ca().add_w(t.ca()).anum);
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int + c2.view() as int)) by {
                self.lemma_ca_has(c1); t.lemma_ca_has(c2);
                lemma_add(c1, c2);
                nat_add_correct(c1.view(), c2.view());
            };
        }
        r
    }

    /// Bounded subtraction, through ChoppedAnum::sub_sound: top when t's
    /// maximum exceeds self's base, otherwise the spec sub, whose differences
    /// cannot wrap because every member of t is at most t's maximum.
    pub fn sub(&self, t: &Self) -> (r: Self)
        ensures forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int - c2.view() as int))
    {
        let (b1, s1, b2, s2) = (self.base, self.span, t.base, t.span);
        match b2.checked_add(s2) {
            Some(max2) => match b1.checked_sub(max2) {
                Some(v) => {
                    let s12 = s1.wrapping_add(s2);
                    let r = ExecAnum { base: v, span: s12.bit_or(s1).bit_or(s2) };
                    proof {
                        let w = W::bits();
                        lemma_exp_bits::<W>();
                        self.lemma_ca(); t.lemma_ca();
                        nat_add_correct(b2.view(), s2.view());
                        self.ca().sub_sound(t.ca());
                        // The span is the chopped spec span (s1 + s2) | s1 | s2.
                        let sn = nat_add(s1.view(), s2.view());
                        lemma_add(s1, s2);
                        W::lemma_or(s12, s1);
                        W::lemma_or(s12.or(s1), s2);
                        add_span(s1.view(), s2.view());
                        chop_bw_or(bw_or(sn, s1.view()), s2.view(), w);
                        chop_bw_or(sn, s1.view(), w);
                        assert(r.to_an() == self.ca().sub(t.ca()).anum);
                        assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int - c2.view() as int)) by {
                            self.lemma_ca_has(c1); t.lemma_ca_has(c2);
                            // Every member of t is at most max2 <= b1 <= c1, so no wrap.
                            t.to_an().has_le_max(c2.view());
                            c1.lemma_view_bounded();
                            lemma_no_wrap::<W>(c1.view() - c2.view());
                        };
                    }
                    r
                },
                None => {
                    let r = Self::top();
                    proof { lemma_sub_top(self, t, r); }
                    r
                },
            },
            None => {
                let r = Self::top();
                proof { lemma_sub_top(self, t, r); }
                r
            },
        }
    }

    /// Division by a nonzero constant, the spec Anum::div_const when base + span
    /// does not wrap; top otherwise.
    pub fn div_const(&self, d: W) -> (r: Self)
        requires d.view() > 0
        ensures forall|c: W| #![auto] self.has(c) ==> r.to_an().has(c.view() / d.view())
    {
        let min_q = self.base.udiv(d);
        match self.base.checked_add(self.span) {
            Some(max_v) => {
                let max_q = max_v.udiv(d);
                proof {
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(self.base.view() as int, max_v.view() as int, d.view() as int);
                }
                let range = sub_le(max_q, min_q);
                let r = ExecAnum { base: min_q, span: Self::ones_mask(range) };
                proof {
                    self.lemma_ca();
                    self.ca().div_const_sound(d.view());
                    nat_add_correct(self.base.view(), self.span.view());
                    assert(r.to_an() == self.to_an().div_const(d.view()));
                    assert forall|c: W| #![auto] self.has(c) implies r.to_an().has(c.view() / d.view()) by {
                        self.lemma_ca_has(c);
                    };
                }
                r
            },
            None => {
                let r = Self::top();
                proof {
                    assert forall|c: W| #![auto] self.has(c) implies r.to_an().has(c.view() / d.view()) by {
                        c.lemma_view_bounded();
                        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(c.view() as int, 1, d.view() as int);
                        Self::lemma_top_has(c.view() / d.view());
                    };
                }
                r
            },
        }
    }

    /// The least 2^k - 1 at or above n, the spec all_ones(len(n)).
    pub fn ones_mask(n: W) -> (r: W)
        ensures r.view() == all_ones(len(n.view()))
    {
        ones::<W>(bit_len(n))
    }

    /// An Anum read as a Tnum: Tn(0, span) + Tn(base, 0), the spec
    /// ChoppedAnum::to_tnum. The addition carries the base into the span, so a
    /// base whose bits overlap the span is covered.
    pub fn to_etn(&self) -> (r: ExecTnum<W>)
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.has(c),
            r.to_tn() == self.ca().to_tnum().tnum,
    {
        proof {
            disj_zero(self.span.view());
            disj_zero_r(self.base.view());
        }
        let m = ExecTnum { val: W::zero(), mask: self.span };
        let v = ExecTnum { val: self.base, mask: W::zero() };
        let r = m.add(&v);
        proof {
            self.lemma_ca();
            let ca = self.ca();
            ca.to_tnum_sound();
            let an = self.to_an();
            an.mask_tnum().add_bitwise_eq(an.val_tnum());
            assert(m.to_tn() == an.mask_tnum() && v.to_tn() == an.val_tnum());
            assert(r.to_tn() == ca.to_tnum().tnum);
            assert forall|c: W| #![auto] self.has(c) implies r.has(c) by {
                self.lemma_ca_has(c);
            };
        }
        r
    }

    /// A Tnum read as an Anum: the spec ChoppedAnum::from_tnum.
    pub fn from_etn(t: &ExecTnum<W>) -> (r: Self)
        requires t.wf()
        ensures
            forall|c: W| #![auto] t.has(c) ==> r.has(c),
            r.to_an() == ChoppedAnum::from_tnum(t.ct()).anum,
    {
        let r = ExecAnum { base: t.val, span: t.mask };
        proof {
            t.lemma_ct();
            ChoppedAnum::from_tnum_sound(t.ct());
            assert forall|c: W| #![auto] t.has(c) implies r.has(c) by {
                t.lemma_ct_has(c);
            };
        }
        r
    }

    /// Negation through ChoppedAnum::neg_sound: {0} stays {0}; a positive base
    /// whose maximum does not wrap reflects through 2^W with the same span; top
    /// otherwise.
    pub fn neg(&self) -> (r: Self)
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.has(W::from_int(0 - c.view() as int)),
            r.to_an() == self.ca().neg().anum,
    {
        let (b, s) = (self.base, self.span);
        let r = if b.eq(W::zero()) {
            if s.eq(W::zero()) { ExecAnum { base: b, span: s } } else { Self::top() }
        } else {
            match b.checked_add(s) {
                Some(max) => {
                    proof { max.lemma_view_bounded(); }
                    ExecAnum { base: max.neg_nonzero(), span: s }
                },
                None => Self::top(),
            }
        };
        proof {
            lemma_exp_bits::<W>();
            self.lemma_ca();
            self.ca().neg_sound();
            let (bv, sv) = (b.view(), s.view());
            if bv == 0 && sv == 0 {
                assert(r.to_an() == self.to_an());
            } else if bv > 0 && bv + sv < exp(W::bits()) {
                assert(r.to_an() == self.to_an().reflect(exp(W::bits())));
            } else {
                assert(r.to_an() == ChoppedAnum::top(W::bits()).anum);
            }
            assert(r.to_an() == self.ca().neg().anum);
            assert forall|c: W| #![auto] self.has(c) implies r.has(W::from_int(0 - c.view() as int)) by {
                self.lemma_ca_has(c);
                lemma_neg(c);
            };
        }
        r
    }

    /// Left shift by k < W through ChoppedAnum::lshi_sound: base and span shift
    /// together when the maximum is below 2^(W-k); top otherwise.
    pub fn lshi(&self, k: u32) -> (r: Self)
        requires (k as nat) < W::bits()
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.to_an().has(chop(lshi(c.view(), k as nat), W::bits())),
            r.to_an() == self.ca().lshi(k as nat).anum,
    {
        let (b, s) = (self.base, self.span);
        let r = match b.checked_add(s) {
            None => Self::top(),
            Some(max) => {
                proof { max.lemma_view_bounded(); }
                if k == 0 {
                    ExecAnum { base: b, span: s }
                } else if max.lt(pow2_word::<W>(W::bit_width() - k)) {
                    ExecAnum { base: b.shl_wrap(k), span: s.shl_wrap(k) }
                } else {
                    Self::top()
                }
            },
        };
        proof {
            let w = W::bits();
            lemma_exp_bits::<W>();
            exp_le((w - k) as nat, w);
            self.lemma_ca();
            self.ca().lshi_sound(k as nat);
            assert(lshi(b.view(), 0) == b.view());
            assert(lshi(s.view(), 0) == s.view());
            if b.view() + s.view() < exp((w - k) as nat) {
                if k == 0 {
                    assert(r.to_an() == self.to_an());
                } else {
                    assert(r.to_an() == self.to_an().lshi(k as nat));
                }
            } else {
                assert(r.to_an() == ChoppedAnum::top(w).anum);
            }
            assert(r.to_an() == self.ca().lshi(k as nat).anum);
            assert forall|c: W| #![auto] self.has(c) implies r.to_an().has(chop(lshi(c.view(), k as nat), w)) by {
                self.lemma_ca_has(c);
            };
        }
        r
    }

    /// Join through ChoppedAnum::join_sound: the lower base, and the span
    /// val | mask of the join of both offset Tnums above it.
    pub fn join(&self, t: &Self) -> (r: Self)
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.has(c),
            forall|c: W| #![auto] t.has(c) ==> r.has(c),
            r.to_an() == self.ca().join(t.ca()).anum,
    {
        let lo = if self.base.le(t.base) { self.base } else { t.base };
        let d1 = sub_le(self.base, lo);
        let d2 = sub_le(t.base, lo);
        proof {
            disj_zero(self.span.view());
            disj_zero(t.span.view());
            disj_zero_r(d1.view());
            disj_zero_r(d2.view());
        }
        let m1 = ExecTnum { val: W::zero(), mask: self.span };
        let v1 = ExecTnum { val: d1, mask: W::zero() };
        let m2 = ExecTnum { val: W::zero(), mask: t.span };
        let v2 = ExecTnum { val: d2, mask: W::zero() };
        let o1 = m1.add(&v1);
        let o2 = m2.add(&v2);
        let j = o1.join(&o2);
        let r = ExecAnum { base: lo, span: j.val.bit_or(j.mask) };
        proof {
            W::lemma_or(j.val, j.mask);
            self.lemma_ca(); t.lemma_ca();
            self.ca().join_sound(t.ca());
            assert(r.to_an() == self.ca().join(t.ca()).anum);
            assert forall|c: W| #![auto] self.has(c) implies r.has(c) by {
                self.lemma_ca_has(c);
            };
            assert forall|c: W| #![auto] t.has(c) implies r.has(c) by {
                t.lemma_ca_has(c);
            };
        }
        r
    }

    /// AND through Tnum (ChoppedAnum::and_sound).
    pub fn bw_and(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.and(c2)),
            r.to_an() == self.ca().bw_and(t.ca()).anum,
    {
        let x = self.to_etn().bw_and(&t.to_etn());
        let r = Self::from_etn(&x);
        proof {
            self.lemma_ca(); t.lemma_ca();
            self.ca().and_sound(t.ca());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.and(c2)) by {
                self.lemma_ca_has(c1); t.lemma_ca_has(c2);
                W::lemma_and(c1, c2);
            };
        }
        r
    }

    /// OR through Tnum (ChoppedAnum::or_sound).
    pub fn bw_or(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.or(c2)),
            r.to_an() == self.ca().bw_or(t.ca()).anum,
    {
        let x = self.to_etn().bw_or(&t.to_etn());
        let r = Self::from_etn(&x);
        proof {
            self.lemma_ca(); t.lemma_ca();
            self.ca().or_sound(t.ca());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.or(c2)) by {
                self.lemma_ca_has(c1); t.lemma_ca_has(c2);
                W::lemma_or(c1, c2);
            };
        }
        r
    }

    /// XOR through Tnum (ChoppedAnum::xor_sound).
    pub fn bw_xor(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.xor(c2)),
            r.to_an() == self.ca().bw_xor(t.ca()).anum,
    {
        let x = self.to_etn().bw_xor(&t.to_etn());
        let r = Self::from_etn(&x);
        proof {
            self.lemma_ca(); t.lemma_ca();
            self.ca().xor_sound(t.ca());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.xor(c2)) by {
                self.lemma_ca_has(c1); t.lemma_ca_has(c2);
                W::lemma_xor(c1, c2);
            };
        }
        r
    }

    /// NOT through Tnum (ChoppedAnum::not_sound).
    pub fn bw_not(&self) -> (r: Self)
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.has(c.not()),
            r.to_an() == self.ca().bw_not().anum,
    {
        let x = self.to_etn().bw_not();
        let r = Self::from_etn(&x);
        proof {
            self.lemma_ca();
            self.ca().not_sound();
            assert forall|c: W| #![auto] self.has(c) implies r.has(c.not()) by {
                self.lemma_ca_has(c);
                lemma_not(c);
            };
        }
        r
    }

    /// Logical right shift by k < W through Tnum (ChoppedAnum::rshi_sound).
    pub fn rshi(&self, k: u32) -> (r: Self)
        requires (k as nat) < W::bits()
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.to_an().has(rshi(c.view(), k as nat)),
            r.to_an() == self.ca().rshi(k as nat).anum,
    {
        let x = self.to_etn().rshi(k);
        let r = Self::from_etn(&x);
        proof {
            self.lemma_ca();
            self.ca().rshi_sound(k as nat);
            assert forall|c: W| #![auto] self.has(c) implies r.to_an().has(rshi(c.view(), k as nat)) by {
                self.lemma_ca_has(c);
            };
        }
        r
    }

    /// Meet through Tnum: the Anum of the Tnum meet, so it has a containment
    /// contract but no spec equality. When the Tnums conflict there is no
    /// common member, and `self` is returned.
    pub fn meet(&self, t: &Self) -> (r: Self)
        ensures forall|c: W| #![auto] self.has(c) && t.has(c) ==> r.has(c)
    {
        let (x, y) = (self.to_etn(), t.to_etn());
        match x.meet(&y) {
            BotOr::Val(m) => Self::from_etn(&m),
            BotOr::Bot => *self,
        }
    }

    /// Multiplication, the bounded Anum::mul_anum (ChoppedAnum::mul): for each
    /// bit of self's Tnum, add the partial product t * bit to an Anum
    /// accumulator by add, then shift. The loop follows ChoppedAnum::mul_step,
    /// so the result is the spec mul.
    pub fn mul(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.to_an().has(chop(prod(c1.view(), c2.view()), W::bits())),
            r.to_an() == self.ca().mul(t.ca()).anum,
    {
        let ghost w = W::bits();
        let ghost whole = self.ca().mul(t.ca());
        let mut p = self.to_etn();
        let mut y = t.to_etn();
        let mut acc = ExecAnum { base: W::zero(), span: W::zero() };
        proof {
            self.lemma_ca(); t.lemma_ca();
            self.ca().to_tnum_inv(); t.ca().to_tnum_inv();
            assert(acc.ca() == ChoppedAnum::zero(w));
        }
        while !(p.val.eq(W::zero()) && p.mask.eq(W::zero()))
            invariant
                w == W::bits(),
                p.wf(), y.wf(),
                ChoppedAnum::mul_step(p.to_tn(), y.to_tn(), acc.ca()) == whole,
            decreases p.val.view() + p.mask.view()
        {
            let ghost (p0, y0, acc0) = (p.to_tn(), y.to_tn(), acc.ca());
            let hv = low_bit(p.val);
            let hm = low_bit(p.mask);
            proof {
                disj_zero(bw_or(y.val.view(), y.mask.view()));
                disj_zero(0);
                W::lemma_or(y.val, y.mask);
            }
            let pb = if hv {
                y
            } else if hm {
                ExecTnum { val: W::zero(), mask: y.val.bit_or(y.mask) }
            } else {
                ExecTnum { val: W::zero(), mask: W::zero() }
            };
            proof {
                assert(pb.to_tn() == y0.mul_bit(p0.head()));
            }
            let part = Self::from_etn(&pb);
            acc = acc.add(&part);
            p = p.rsh();
            y = y.lsh();
            proof {
                assert(acc.ca() == acc0.add_w(ChoppedAnum { anum: Anum::from_tnum(y0.mul_bit(p0.head())), w }));
                assert(ChoppedAnum::mul_step(p0, y0, acc0) == ChoppedAnum::mul_step(p.to_tn(), y.to_tn(), acc.ca()));
            }
        }
        proof {
            assert(ChoppedAnum::mul_step(p.to_tn(), y.to_tn(), acc.ca()) == acc.ca());
            self.ca().mul_sound(t.ca());
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies acc.to_an().has(chop(prod(c1.view(), c2.view()), w)) by {
                self.lemma_ca_has(c1); t.lemma_ca_has(c2);
            };
        }
        acc
    }

    /// The more precise multiplication: mul, and its meet with pair-join
    /// multiplication of the two Tnums (ExecTnum::mul), whichever has fewer
    /// span bits. The meet alone can be looser than mul, since reading an Anum
    /// as a Tnum carries the base into the span. It costs both products and a
    /// meet, and has a containment contract but no spec equality.
    pub fn mul_precise(&self, t: &Self) -> (r: Self)
        ensures
            forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.to_an().has(chop(prod(c1.view(), c2.view()), W::bits())),
    {
        let a = self.mul(t);
        let (x, y) = (self.to_etn(), t.to_etn());
        let pt = x.mul(&y);
        let p = Self::from_etn(&pt);
        let m = a.meet(&p);
        let r = if popcount(m.span) < popcount(a.span) { m } else { a };
        proof {
            let w = W::bits();
            lemma_exp_bits::<W>();
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.to_an().has(chop(prod(c1.view(), c2.view()), w)) by {
                // The product as a word: from_int wraps as chop does.
                let c = W::from_int(prod(c1.view(), c2.view()) as int);
                W::lemma_from_int(prod(c1.view(), c2.view()) as int);
                chop_is_mod(prod(c1.view(), c2.view()), w);
                assert(c.view() == chop(prod(c1.view(), c2.view()), w));
                assert(x.has(c1) && y.has(c2));
                assert(a.has(c) && pt.has(c) && p.has(c));
            };
        }
        r
    }

    pub fn min_val(&self) -> (r: W)
        ensures r == self.base
    {
        self.base
    }

    pub fn max_val(&self) -> (r: W)
        ensures r == W::from_int(self.base.view() as int + self.span.view() as int)
    {
        self.base.wrapping_add(self.span)
    }
}

/// The top branches of sub: top holds every difference.
proof fn lemma_sub_top<W: BitWord>(a: &ExecAnum<W>, t: &ExecAnum<W>, r: ExecAnum<W>)
    requires forall|n: W| #![auto] r.has(n)
    ensures forall|c1: W, c2: W| #![auto] a.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int - c2.view() as int))
{
}

} // verus!
