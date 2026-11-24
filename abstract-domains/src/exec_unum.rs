// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Layer 4: the executable Unum, generic over the word width.
//!
//! A Unum represents a set {v + d | d in D} where D is described by bitfields
//! in (walls, extent). Register walls marks bitfield boundaries:
//!
//! - A 1-bit in walls starts a new bitfield (the "leader").
//! - A 0-bit in walls continues the previous bitfield (a "follower").
//!
//! Register extent stores the maximum value for each bitfield.
//!
//! The set D is the set of all sums of per-bitfield values, where each
//! bitfield's value ranges from 0 to its max.
//!
//! The unbounded operation has the precise carry-boundary formula. The
//! executable operations below prove soundness at fixed width and widen to top
//! whenever a represented bound or result range would wrap.
#![allow(unused_imports)]
use crate::bitword::*;
use crate::bools::Bit;
use crate::chopped::*;
use crate::div::*;
use crate::exec_anum::*;
use crate::exec_tnum::*;
use crate::interval::Interval;
use crate::lattice::*;
use crate::nats::*;
use crate::unum::Unum;
use crate::word::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ExecUnum<W> {
    pub base: W,
    pub walls: W,
    pub extent: W,
}

/// The base and extent of the product of v1 + [0, x1] and v2 + [0, x2], when
/// (v1 + x1) * (v2 + x2) and every part of the bilinear expansion fit.
fn mul_parts<W: Word>(v1: W, x1: W, v2: W, x2: W) -> (r: Option<(W, W)>)
    ensures
        match r {
            Some((b, u)) => b.view() == v1.view() * v2.view()
                && u.view() == v1.view() * x2.view() + v2.view() * x1.view() + x1.view() * x2.view()
                && (v1.view() + x1.view()) * (v2.view() + x2.view()) < W::modulus(),
            None => true,
        },
{
    let max1 = v1.checked_add(x1)?;
    let max2 = v2.checked_add(x2)?;
    let _max_product = max1.checked_mul(max2)?;
    let base = v1.checked_mul(v2)?;
    let v1x2 = v1.checked_mul(x2)?;
    let v2x1 = v2.checked_mul(x1)?;
    let x1x2 = x1.checked_mul(x2)?;
    let unc1 = v1x2.checked_add(v2x1)?;
    let unc = unc1.checked_add(x1x2)?;
    let _upper = base.checked_add(unc)?;
    proof { _max_product.lemma_view_bounded(); }
    Some((base, unc))
}

impl<W: BitWord> ExecUnum<W> {
    pub open spec fn to_un(self) -> Unum {
        Unum { base: self.base.view(), walls: self.walls.view(), extent: self.extent.view() }
    }

    pub open spec fn has(self, n: W) -> bool {
        self.to_un().has(n.view())
    }

    /// The Layer-3 Unum at the word width.
    pub open spec fn cu(self) -> ChoppedUnum {
        ChoppedUnum { unum: self.to_un(), w: W::bits() }
    }

    pub proof fn lemma_cu(self)
        ensures self.cu().inv()
    {
        lemma_fits(self.base);
        lemma_fits(self.walls);
        lemma_fits(self.extent);
    }

    /// Every member is at most base + extent.
    proof fn has_upper_bound(self, c: W)
        requires self.has(c)
        ensures c.view() <= self.base.view() + self.extent.view()
    {
        Unum::offset_bounded(self.walls.view(), self.extent.view(), nat_sub(c.view(), self.base.view()));
    }

    /// top holds every value below 2^W.
    proof fn lemma_top_has(r: Self, n: nat)
        requires r.base.view() == 0, r.walls.view() == 0, r.extent.view() == W::modulus() - 1, n < W::modulus()
        ensures r.to_un().has(n)
    {
        Unum::offset_from_bound(r.extent.view(), n);
    }

    pub fn constant(n: W) -> (r: Self)
        ensures r.has(n)
    {
        let r = ExecUnum { base: n, walls: W::max(), extent: W::zero() };
        proof {
            Unum::zero_offset_admitted(r.walls.view(), true);
            assert(nat_sub(n.view(), n.view()) == 0);
        }
        r
    }

    pub fn top() -> (r: Self)
        ensures
            forall|n: W| #![auto] r.has(n),
            forall|n: nat| n < W::modulus() ==> #[trigger] r.to_un().has(n),
    {
        let r = ExecUnum { base: W::zero(), walls: W::zero(), extent: W::max() };
        proof {
            assert forall|n: nat| n < W::modulus() implies #[trigger] r.to_un().has(n) by {
                Self::lemma_top_has(r, n);
            };
            assert forall|n: W| #![auto] r.has(n) by {
                n.lemma_view_bounded();
            };
        }
        r
    }

    /// Sound fixed-width addition. Uses the precise field formula when
    /// represented bounds do not wrap; otherwise widens to top.
    /// cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))
    /// walls = (w1 & w2) & ~(cout << 1)
    #[verifier::rlimit(30)]
    #[verifier::spinoff_prover]
    pub fn add(&self, t: &Self) -> (r: Self)
        ensures forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int + c2.view() as int))
    {
        let (b1, sx, b2, tx) = (self.base, self.extent, t.base, t.extent);
        if !sum4_fits(b1, sx, b2, tx) {
            return Self::top();
        }
        let v = b1.wrapping_add(b2);
        let x12 = sx.wrapping_add(tx);
        let cout = sx.bit_and(tx).bit_or(sx.bit_or(tx).bit_and(x12.bit_not()));
        proof { W::lemma_modulus(); }
        let carry_in = cout.shl_wrap(1);
        let (sw, tw) = (self.walls, t.walls);
        let walls = sw.bit_and(tw).bit_and(carry_in.bit_not());
        let r = ExecUnum { base: v, walls, extent: x12 };
        proof {
            let width = W::bits();
            lemma_exp_bits::<W>();
            self.lemma_cu(); t.lemma_cu();
            lemma_no_wrap::<W>(b1.view() + b2.view() as int);
            lemma_no_wrap::<W>(sx.view() + tx.view() as int);
            nat_add_correct(b1.view(), b2.view());
            nat_add_correct(sx.view(), tx.view());
            lemma_fits(v);
            lemma_fits(x12);

            W::lemma_and(sx, tx);
            W::lemma_or(sx, tx);
            lemma_and_not(sx.or(tx), x12);
            W::lemma_or(sx.and(tx), sx.or(tx).and(x12.not()));
            Unum::carry_out_formula(sx.view(), tx.view());
            assert(cout.view() == Unum::carry_out(sx.view(), tx.view()));

            assert(lshi(cout.view(), 1) == lsh(cout.view())) by { assert(lshi(cout.view(), 0) == cout.view()); };
            W::lemma_and(sw, tw);
            lemma_and_not(sw.and(tw), carry_in);
            chop_bw_and_not(bw_and(sw.view(), tw.view()), lsh(Unum::carry_out(sx.view(), tx.view())), width);
            lemma_fits(sw.and(tw));
            assert(r.to_un() == self.to_un().add(t.to_un()).truncate(width));

            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int + c2.view() as int)) by {
                self.has_upper_bound(c1);
                t.has_upper_bound(c2);
                nat_add_correct(c1.view(), c2.view());
                lemma_no_wrap::<W>(c1.view() + c2.view() as int);
                self.to_un().add_bounded_sound(t.to_un(), c1.view(), c2.view(), width);
            };
        }
        r
    }

    /// Convert to an Anum: widen the extent to ones_mask. Unum fields are
    /// contiguous ranges `[0, max]`; Anum needs per-bit independence, so the
    /// whole extent is rounded up to 2^k - 1, as one field. This is sound, but
    /// may be less precise than per-field widening for multi-field Unums.
    pub fn to_ean(&self) -> (r: ExecAnum<W>)
        ensures
            forall|c: W| #![auto] self.has(c) ==> r.has(c),
            r.to_an() == self.to_un().to_anum(),
    {
        let r = ExecAnum { base: self.base, span: ExecAnum::<W>::ones_mask(self.extent) };
        proof { self.to_un().to_anum_sound(); }
        r
    }

    /// Convert to a Tnum through the Anum: `ExecAnum::to_etn` leaves unknown
    /// the bits that differ between the Anum's bounds, and its span.
    pub fn to_etn(&self) -> (r: ExecTnum<W>)
        ensures
            r.wf(),
            forall|c: W| #![auto] self.has(c) ==> r.has(c),
    {
        self.to_ean().to_etn()
    }

    /// Build from an Anum: each uncertain bit becomes its own 1-wide bitfield,
    /// so walls is all ones and extent is the span.
    pub fn from_ean(a: &ExecAnum<W>) -> (r: Self)
        ensures forall|c: W| #![auto] a.has(c) ==> r.has(c)
    {
        let r = ExecUnum { base: a.base, walls: W::max(), extent: a.span };
        proof {
            assert forall|c: W| #![auto] a.has(c) implies r.has(c) by {
                let d = nat_sub(c.view(), a.base.view());
                a.to_an().mask_tnum().has_equiv(d);
                Unum::submask_admitted(r.walls.view(), a.span.view(), d, true);
            };
        }
        r
    }

    /// Build from an Interval: a single bitfield covering the range.
    pub fn from_interval(iv: &Interval<W>) -> (r: Self)
        requires iv.wf()
        ensures forall|c: W| #![auto] iv.gamma(c) ==> r.has(c)
    {
        let (lo, hi) = iv.bounds();
        let range = sub_le(hi, lo);
        let r = ExecUnum { base: lo, walls: W::zero(), extent: range };
        proof {
            assert forall|c: W| #![auto] iv.gamma(c) implies r.has(c) by {
                Unum::offset_from_bound(range.view(), (c.view() - lo.view()) as nat);
            };
        }
        r
    }

    /// Negation: -(v + d) = (-v - x) + (x - d), and x - d is admitted with the
    /// same fields (`Unum::complement_admitted`), so the result's base is
    /// -v - x with the same walls and extent. The negated range wraps when the
    /// input range does, or when it holds 0 and something else:
    /// -[0, e] = {0} u [-e, MAX]; both give top.
    pub fn neg(&self) -> (r: Self)
        ensures forall|c: W| #![auto] self.has(c) ==> r.has(W::from_int(0 - c.view() as int))
    {
        let (b, x) = (self.base, self.extent);
        let max = match b.checked_add(x) {
            None => return Self::top(),
            Some(max) => max,
        };
        if max.eq(W::zero()) {
            proof {
                W::lemma_modulus();
                assert forall|c: W| #![auto] self.has(c) implies self.has(W::from_int(0 - c.view() as int)) by {
                    Unum::offset_bounded(self.walls.view(), x.view(), nat_sub(c.view(), b.view()));
                    assert(c.view() == 0);
                    W::lemma_from_int(0);
                    vstd::arithmetic::div_mod::lemma_small_mod(0, W::modulus());
                    W::lemma_view_injective(W::from_int(0), c);
                    assert(0 - c.view() as int == 0);
                };
            }
            return *self;
        }
        if b.eq(W::zero()) {
            return Self::top();
        }
        let r = ExecUnum { base: max.neg_nonzero(), walls: self.walls, extent: x };
        proof {
            W::lemma_modulus();
            let m = W::modulus() as int;
            assert forall|c: W| #![auto] self.has(c) implies r.has(W::from_int(0 - c.view() as int)) by {
                let (xv, cv) = (x.view(), c.view());
                let d = nat_sub(cv, b.view());
                let n = W::from_int(0 - cv as int);
                Unum::offset_bounded(self.walls.view(), xv, d);
                assert(cv >= b.view() && d == cv - b.view() && d <= xv);
                assert(r.base.view() == m - (b.view() + xv));
                c.lemma_view_bounded();
                W::lemma_from_int(0 - cv as int);
                vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(0 - cv as int, m);
                vstd::arithmetic::div_mod::lemma_small_mod((m - cv) as nat, m as nat);
                assert(n.view() == m - cv) by {
                    assert(m + (0 - cv as int) == (m - cv) as nat as int);
                };
                Unum::complement_admitted(self.walls.view(), xv, d, Bit::f(), true);
                assert(nat_sub(n.view(), r.base.view()) == (xv - d - Bit::f().n()) as nat);
            };
        }
        r
    }

    /// Subtraction: add the negation.
    pub fn sub(&self, t: &Self) -> (r: Self)
        ensures forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.has(W::from_int(c1.view() as int - c2.view() as int))
    {
        let nt = t.neg();
        let r = self.add(&nt);
        proof {
            W::lemma_modulus();
            assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.has(W::from_int(c1.view() as int - c2.view() as int)) by {
                let (v1, v2) = (c1.view() as int, c2.view() as int);
                let n2 = W::from_int(0 - v2);
                assert(nt.has(n2));
                let s = W::from_int(v1 + n2.view() as int);
                assert(r.has(s));
                W::lemma_from_int(0 - v2);
                W::lemma_from_int(v1 + n2.view() as int);
                W::lemma_from_int(v1 - v2);
                vstd::arithmetic::div_mod::lemma_add_mod_noop_right(v1, 0 - v2, W::modulus() as int);
                W::lemma_view_injective(s, W::from_int(v1 - v2));
            };
        }
        r
    }

    /// Multiplication: bilinear expansion.
    /// (v1+d1)*(v2+d2) = v1*v2 + v1*d2 + v2*d1 + d1*d2
    /// Uncertainty bounded by v1*x2 + v2*x1 + x1*x2.
    pub fn mul(&self, t: &Self) -> (r: Self)
        ensures forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) ==> r.to_un().has(chop(prod(c1.view(), c2.view()), W::bits()))
    {
        let (v1, x1, v2, x2) = (self.base, self.extent, t.base, t.extent);
        match mul_parts(v1, x1, v2, x2) {
            Some((base, unc)) => {
                let r = ExecUnum { base, walls: W::zero(), extent: unc };
                proof {
                    let width = W::bits();
                    lemma_exp_bits::<W>();
                    self.lemma_cu(); t.lemma_cu();
                    base.lemma_view_bounded();
                    unc.lemma_view_bounded();
                    chop_id(base.view(), width);
                    chop_id(unc.view(), width);
                    chop_id(0, width);
                    assert(r.to_un() == self.to_un().mul(t.to_un()).truncate(width));
                    assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.to_un().has(chop(prod(c1.view(), c2.view()), width)) by {
                        self.has_upper_bound(c1);
                        t.has_upper_bound(c2);
                        vstd::arithmetic::mul::lemma_mul_upper_bound(
                            c1.view() as int,
                            (v1.view() + x1.view()) as int,
                            c2.view() as int,
                            (v2.view() + x2.view()) as int,
                        );
                        chop_id(prod(c1.view(), c2.view()), width);
                        self.to_un().mul_bounded_sound(t.to_un(), c1.view(), c2.view(), width);
                    };
                }
                r
            },
            None => {
                let r = Self::top();
                proof {
                    lemma_exp_bits::<W>();
                    assert forall|c1: W, c2: W| #![auto] self.has(c1) && t.has(c2) implies r.to_un().has(chop(prod(c1.view(), c2.view()), W::bits())) by {
                        chop_lt(prod(c1.view(), c2.view()), W::bits());
                    };
                }
                r
            },
        }
    }

    pub fn min_val(&self) -> (r: W)
        ensures r == self.base
    {
        self.base
    }

    pub fn max_val(&self) -> (r: W)
        ensures r == W::from_int(self.base.view() as int + self.extent.view() as int)
    {
        self.base.wrapping_add(self.extent)
    }

    pub fn is_const(&self) -> (b: bool)
        ensures b == (self.extent.view() == 0)
    {
        self.extent.eq(W::zero())
    }
}

} // verus!
