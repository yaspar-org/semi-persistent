// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tristate bits: the single-bit abstract domain.
//!
//! A tristate bit (v, m) represents a set of booleans:
//!   {0} = (F,F), {1} = (T,F), {0,1} = (F,T), {} = (T,T)
//! Invariant: !(v && m).

use crate::bools::Bit;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TBit {
    pub val: Bit,
    pub mask: Bit,
}

impl TBit {
    // --- invariant and derived fields ---

    pub open spec fn inv(self) -> bool { self.val.and(self.mask).not().b() }
    pub open spec fn u(self) -> Bit { self.val.xor(self.mask) }

    // --- constructors ---

    /// Construct from (value, uncertainty)
    pub open spec fn mk(v: Bit, m: Bit) -> TBit { TBit { val: v, mask: m } }
    pub open spec fn ctor(v: Bit, u: Bit) -> TBit { TBit { val: v, mask: v.xor(u) } }

    /// Singleton containing only b
    pub open spec fn unit(b: Bit) -> TBit { TBit { val: b, mask: Bit::f() } }

    pub open spec fn zero() -> TBit { TBit::unit(Bit::f()) }
    pub open spec fn top() -> TBit { TBit { val: Bit::f(), mask: Bit::t() } }
    pub open spec fn bot() -> TBit { TBit { val: Bit::t(), mask: Bit::t() } }
    pub open spec fn is_bot(self) -> bool { self == TBit::bot() }

    // --- membership ---

    pub open spec fn has(self, b: Bit) -> bool { b.and(self.mask.not()) == self.val }

    // --- soundness of top/bot ---

    pub proof fn top_has(b: Bit)
        ensures TBit::top().has(b)
    {}

    pub proof fn bot_empty(b: Bit)
        ensures !TBit::bot().has(b)
    {}

    // --- join (union) ---

    pub open spec fn join(self, t: TBit) -> TBit {
        TBit::ctor(self.val.and(t.val), self.u().or(t.u()))
    }

    pub proof fn join_sound(self, t: TBit)
        ensures forall|b: Bit| #![auto] self.join(t).has(b) <==> (self.has(b) || t.has(b))
    {}

    // --- meet (intersection) ---

    pub open spec fn meet_ok(self, t: TBit) -> bool {
        self.val.or(t.val).and(self.u().and_not(t.u())) == Bit::f()
    }

    pub open spec fn meet1(self, t: TBit) -> TBit {
        TBit::ctor(self.val.or(t.val), self.u().and(t.u()))
    }

    pub proof fn meet_ok_sound(self, t: TBit)
        ensures forall|b: Bit| #![auto] self.has(b) && t.has(b) ==> self.meet_ok(t)
    {}

    pub proof fn meet1_sound(self, t: TBit)
        ensures forall|b: Bit| #![auto] self.meet1(t).has(b) <==> (self.has(b) && t.has(b))
    {}

    // --- pointwise or ---

    pub open spec fn bw_or(self, t: TBit) -> TBit {
        let v = self.val.or(t.val);
        TBit::ctor(v, v.or(self.u()).or(t.u()))
    }

    pub proof fn or_sound(self, t: TBit)
        ensures forall|b0: Bit, b1: Bit| #![auto] self.has(b0) && t.has(b1) ==> self.bw_or(t).has(b0.or(b1))
    {}

    // --- pointwise not ---

    pub open spec fn bw_not(self) -> TBit {
        TBit::ctor(self.u().not(), self.val.not())
    }

    pub proof fn not_sound(self)
        requires self.inv()
        ensures forall|b0: Bit| #![auto] self.has(b0) ==> self.bw_not().has(b0.not())
    {}

    // --- pointwise and ---

    pub open spec fn bw_and(self, t: TBit) -> TBit {
        TBit { val: self.val.and(t.val), mask: self.mask.or(t.mask) }
    }

    pub proof fn and_sound(self, t: TBit)
        requires self.inv()
        ensures forall|b0: Bit, b1: Bit| #![auto] self.has(b0) && t.has(b1) ==> self.bw_and(t).has(b0.and(b1))
    {}

    // --- pointwise and-not ---

    pub open spec fn bw_and_not(self, t: TBit) -> TBit {
        self.bw_and(t.bw_not())
    }

    pub proof fn and_not_sound(self, t: TBit)
        requires self.inv()
        ensures forall|b0: Bit, b1: Bit| #![auto] self.has(b0) && t.has(b1) ==> self.bw_and_not(t).has(b0.and_not(b1))
    {}

    // --- pointwise xor ---

    pub open spec fn bw_xor(self, t: TBit) -> TBit {
        let v = self.val.xor(t.val);
        let m = self.mask.or(t.mask);
        TBit { val: v.and(m.not()), mask: m }
    }

    pub proof fn xor_sound(self, t: TBit)
        requires self.inv()
        ensures forall|b0: Bit, b1: Bit| #![auto] self.has(b0) && t.has(b1) ==> self.bw_xor(t).has(b0.xor(b1))
    {}

    // --- pointwise addition with carry ---
    //           var rc := b0.full_add(b1,c0); r.0.has(rc.0) && r.1.has(rc.1)`

    pub open spec fn add_carry(self, t: TBit, c: TBit) -> (TBit, TBit) {
        let (lbvv, lbvc) = self.val.full_add(t.val, c.val);
        let (lbmv, lbmc) = self.mask.full_add(t.mask, c.mask);
        let (ubv, ubc1) = lbvv.full_add(lbmv, Bit::ctor_n(0));
        let (ubc, _) = lbvc.full_add(lbmc, ubc1);
        let diffv = ubv.xor(lbvv);
        let diffc = ubc.xor(lbvc);
        let maskv = diffv.or(self.mask).or(t.mask);
        let maskc = diffc;
        let rv = TBit { val: lbvv.and(maskv.not()), mask: maskv };
        let rc = TBit { val: lbvc.and(maskc.not()), mask: maskc };
        (rv, rc)
    }

    pub proof fn add_carry_sound(self, t: TBit, c: TBit)
        ensures forall|b0: Bit, b1: Bit, c0: Bit| #![auto] self.has(b0) && t.has(b1) && c.has(c0) ==> ({
            let rc = b0.full_add(b1, c0);
            let (r, carry) = self.add_carry(t, c);
            r.has(rc.0) && carry.has(rc.1)
        })
    {}

    /// The result and carry of Tb.plus_c always have inv.
    pub proof fn add_carry_inv(self, t: TBit, c: TBit)
        ensures ({
            let (r, carry) = self.add_carry(t, c);
            r.inv() && carry.inv()
        })
    {}

    /// Key carry properties for the plus_bv_eq proof.
    /// Carry decomposition for Tb.plus_c.
    ///
    /// The non-recursive Tnum addition formula (plus_bv) computes carries globally:
    ///   lbv = self.val + t.val,  lbm = self.mask + t.mask,  ub = lbv + lbm
    /// The recursive formula (plus_c) propagates carries bit-by-bit through Tb.plus_c.
    ///
    /// This lemma relates the two carry structures at each bit position.
    /// Given inputs self, t, c (all with inv), let:
    ///   (b1, c1) = Tb.add_carry(self, t, c)     — recursive carry-out
    ///   cv1 = carry(sv + tv + cv)             — nat-level v-carry
    ///   cm1 = carry(sm + tm + cm)             — nat-level m-carry
    ///   rv0 = (sv + tv + cv) mod 2            — v-result bit
    ///   rm0 = (sm + tm + cm) mod 2            — m-result bit
    ///   ub_carry = rv0 AND rm0                — carry from ub = lbv + lbm at bit 0
    ///
    /// The ensures clauses are:
    ///
    /// (1) c1.val == cv1: the v-carry from Tb.plus_c equals the nat-level v-carry.
    ///
    /// (2) !c1.mask ==> !cm1: when the carry-out is known, the m-carry is zero.
    ///
    /// (3) !c1.mask ==> !ub_carry: when the carry-out is known, the ub carry is zero.
    ///     Together with (2), this means tl(lbm) and tl(ub) decompose cleanly.
    ///
    /// (4) c1.mask ==> (cm1 != ub_carry): THE KEY LEMMA. When the carry-out is
    ///     uncertain, exactly one of cm1 and ub_carry is 1. This is the carry
    ///     compensation property: the non-recursive formula routes the extra carry
    ///     through ub (rv0 & rm0), while the recursive formula routes it through
    ///     cm (the m-carry). The two paths compute the same sum:
    ///       tl(lbm) + ub_carry == tail_lbm + 0
    ///     because cm1 + ub_carry == 1 == c1.mask, so swapping which carry is used
    ///     doesn't change the total.
    ///
    ///     Proof: c1.mask = maskc = ubc XOR cv1. When c1.mask == T, cv1 must be F
    ///     (otherwise cv1==T ==> cm1==ubc1 ==> maskc==F, contradiction).
    ///     So c1.mask = ubc = cm1 XOR ubc1 = cm1 XOR (rv0 & rm0) = T,
    ///     meaning cm1 != (rv0 & rm0). QED.
    ///
    /// (5,6) b1.val and b1.mask match the non-recursive head formula.
    pub proof fn add_carry_carry_decomp(self, t: TBit, c: TBit)
        requires self.inv(), t.inv(), c.inv()
        ensures ({
            let (b1, c1) = self.add_carry(t, c);
            let cv1 = self.val.full_add(t.val, c.val).1;
            let cm1 = self.mask.full_add(t.mask, c.mask).1;
            let rv0 = self.val.full_add(t.val, c.val).0;
            let rm0 = self.mask.full_add(t.mask, c.mask).0;
            let ub0 = rv0.full_add(rm0, Bit::f()).0;
            let maskv = ub0.xor(rv0).or(self.mask).or(t.mask);
            &&& c1.val == cv1
            &&& (!c1.mask.b() ==> !cm1.b())
            &&& (!c1.mask.b() ==> !(rv0.b() && rm0.b()))
            &&& (c1.mask.b() ==> (cm1.b() != (rv0.b() && rm0.b())))
            &&& b1.val == rv0.and(maskv.not())
            &&& b1.mask == maskv
        })
    {
        let cv1 = self.val.full_add(t.val, c.val).1;
        let cm1 = self.mask.full_add(t.mask, c.mask).1;
        let rv0 = self.val.full_add(t.val, c.val).0;
        let rm0 = self.mask.full_add(t.mask, c.mask).0;
        let ubc1 = rv0.and(rm0);
        assert(cv1.b() ==> (cm1 == ubc1));
    }

    // --- isBelow (refinement check) ---

    pub open spec fn is_below(self, t: TBit) -> bool {
        self.join(t) == t
    }

    pub proof fn is_below_sound(self, t: TBit)
        requires self.inv()
        ensures self.is_below(t) <==> forall|b: Bit| #![auto] self.has(b) ==> t.has(b)
    {
        self.join_sound(t);
        // Forward: is_below ==> forall b. has(b) ==> t.has(b)
        // follows from join_sound: join(t).has(b) <==> has(b) || t.has(b)
        // if join(t) == t, then t.has(b) <==> has(b) || t.has(b), so has(b) ==> t.has(b)

        // Reverse: need join(t) == t when forall b. has(b) ==> t.has(b)
        // join(t).has(b) <==> has(b) || t.has(b) <==> t.has(b) (since has(b) ==> t.has(b))
        // So join(t) and t have the same membership. For TBit, same membership ==> equal.
        // This is the eqL lemma: exhaustive over {true, false}.
        if forall|b: Bit| #![auto] self.has(b) ==> t.has(b) {
            // join(t).has(true) == t.has(true) and join(t).has(false) == t.has(false)
            // implies join(t) == t (by exhaustion over the 4 possible TBit values)
            assert(self.join(t).has(Bit::t()) == t.has(Bit::t()));
            assert(self.join(t).has(Bit::f()) == t.has(Bit::f()));
        }
    }
}

} // verus!
