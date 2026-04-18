// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Tristate numbers (Tnums): sets of naturals via per-bit 0/1/u.
//!
//! All bitwise soundness proofs follow from this characterization
//! plus mapd's per-bit correctness.

use crate::bools::Bit;
use crate::nats::*;
use crate::tbit::TBit;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Tnum { pub val: nat, pub mask: nat }

impl Tnum {
    pub open spec fn inv(self) -> bool { disj(self.val, self.mask) }
    pub open spec fn u(self) -> nat { bw_xor(self.val, self.mask) }
    pub open spec fn min(self) -> nat { self.val }
    pub open spec fn max(self) -> nat { bw_or(self.val, self.mask) }
    pub open spec fn size(self) -> nat { self.val + self.mask }
    pub open spec fn is_zero(self) -> bool { self.val == 0 && self.mask == 0 }
    pub open spec fn head(self) -> TBit { TBit { val: hd(self.val), mask: hd(self.mask) } }
    pub open spec fn tail(self) -> Tnum { Tnum { val: tl(self.val), mask: tl(self.mask) } }

    pub open spec fn ctor(v: nat, m: nat) -> Tnum { Tnum { val: v, mask: m } }
    pub open spec fn uctor(v: nat, u: nat) -> Tnum { Tnum { val: v, mask: bw_xor(v, u) } }
    pub open spec fn unit(n: nat) -> Tnum { Tnum { val: n, mask: 0 } }
    pub open spec fn zero() -> Tnum { Tnum { val: 0, mask: 0 } }

    /// Recursive membership
    pub open spec fn has(self, n: nat) -> bool
        decreases self.size()
    {
        if self.is_zero() { n == 0 }
        else { self.head().has(hd(n)) && self.tail().has(tl(n)) }
    }

    /// Non-recursive membership: n & !m == v
    pub open spec fn has_bw(self, n: nat) -> bool {
        bw_and_not(n, self.mask) == self.val
    }

    // ================================================================
    // THE KEY LEMMA: has(n) <==> has_bw(n)
    // Once we have this, all bitwise soundness proofs are trivial.
    // ================================================================

    pub proof fn has_equiv(self, n: nat)
        ensures self.has(n) <==> self.has_bw(n)
        decreases self.size()
    {
        if self.is_zero() {
            // has(n) <==> n == 0
            // has_bw(n) <==> andnot(n, 0) == 0 <==> n == 0
            // Need: andnot(n, 0) == n
            assert forall|i: nat| #![auto] bit(bw_and_not(n, 0 as nat), i) == bit(n, i) by {
                and_not_bit(n, 0, i);
                bit_zero(i);
            };
            eq_from_bits(bw_and_not(n, 0), n);
        } else {
            // Inductive step: decompose through hd/tl
            // has(n) <==> head.has(hd(n)) && tail.has(tl(n))
            // head.has(hd(n)) <==> hd(n).and(hd(m).not()) == hd(v)
            //                 <==> hd(andnot(n, m)) == hd(v)  [by mapd_hd_tl]
            // tail.has(tl(n)) <==> tail.has_bw(tl(n))  [by IH]
            //                 <==> andnot(tl(n), tl(m)) == tl(v)
            //                 <==> tl(andnot(n, m)) == tl(v)  [by mapd_hd_tl]
            // So: has(n) <==> hd(andnot(n,m)) == hd(v) && tl(andnot(n,m)) == tl(v)
            //            <==> andnot(n,m) == v  [by hd_tl reconstruction]
            self.tail().has_equiv(tl(n));
            mapd_hd_tl(n, self.mask, |x: Bit, y: Bit| x.and_not(y));
            // Now: tl(andnot(n, m)) == andnot(tl(n), tl(m))
            // And: hd(andnot(n, m)) == hd(n).and_not(hd(m))

            if self.has(n) {
                // Forward: has ==> has_bw
                // head.has(hd(n)) means hd(n).and(hd(m).not()) == hd(v)
                // which is hd(andnot(n,m)) == hd(v)
                // tail.has(tl(n)) ==> tail.has_bw(tl(n)) by IH
                // which is andnot(tl(n), tl(m)) == tl(v)
                // which is tl(andnot(n,m)) == tl(v)
                // So hd and tl of andnot(n,m) match v, hence andnot(n,m) == v
                hd_tl(bw_and_not(n, self.mask));
                hd_tl(self.val);
            }
            if self.has_bw(n) {
                // Reverse: has_bw ==> has
                // andnot(n, m) == v
                // hd(andnot(n,m)) == hd(v), i.e. head.has(hd(n))
                // tl(andnot(n,m)) == tl(v), i.e. andnot(tl(n),tl(m)) == tl(v)
                // By IH reverse: tail.has_bw(tl(n)) ==> tail.has(tl(n))
            }
        }
    }


    // ================================================================
    // Bitwise operations — soundness via has_equiv
    // ================================================================

    pub open spec fn bw_or(self, t: Tnum) -> Tnum {
        let v = bw_or(self.val, t.val);
        Tnum { val: v, mask: bw_and_not(bw_or(self.mask, t.mask), v) }
    }

    /// All bitwise Tn ops (or, and, xor, andnot) preserve inv.
    /// The result always has v = andnot(mapd(sv, tv, f), or(sm, tm)) and m = or(sm, tm),
    /// so disj(v, m) holds trivially (andnot(x, m) & m == 0).
    pub proof fn bitwise_inv(self, t: Tnum, f: spec_fn(Bit, Bit) -> Bit)
        ensures ({
            let v = bw_and_not(mapd(self.val, t.val, f), bw_or(self.mask, t.mask));
            let m = bw_or(self.mask, t.mask);
            disj(v, m)
        })
    {
        let v = bw_and_not(mapd(self.val, t.val, f), bw_or(self.mask, t.mask));
        let m = bw_or(self.mask, t.mask);
        assert forall|i: nat| #![auto] !(bit(v, i).b() && bit(m, i).b()) by {
            and_not_bit(mapd(self.val, t.val, f), bw_or(self.mask, t.mask), i);
        };
        disj_bits(v, m);
    }

    pub proof fn or_sound(self, t: Tnum)
        ensures
            self.bw_or(t).inv(),
            forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc) ==> self.bw_or(t).has(bw_or(c, tc))
    {
        // inv: disj(andnot(or(sv,tv), or(sm,tm)), or(sm,tm))
        let r = self.bw_or(t);
        let rv = bw_or(self.val, t.val);
        let rm = bw_and_not(bw_or(self.mask, t.mask), rv);
        assert forall|i: nat| #![auto] !(bit(rv, i).b() && bit(rm, i).b()) by {
            and_not_bit(bw_or(self.mask, t.mask), rv, i);
        };
        disj_bits(rv, rm);
        // soundness
        assert forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc)
            implies self.bw_or(t).has(bw_or(c, tc)) by {
            self.has_equiv(c);
            t.has_equiv(tc);
            self.bw_or(t).has_equiv(bw_or(c, tc));
            // Now: andnot(c, sm) == sv, andnot(tc, tm) == tv
            // Need: andnot(or(c,tc), r.mask) == r.val
            // r.val = or(sv, tv), r.mask = andnot(or(sm, tm), or(sv, tv))
            // andnot(or(c,tc), andnot(or(sm,tm), or(sv,tv))) == or(sv,tv)
            // This is a pure bitwise identity given the premises.
            // Prove it bit by bit.
            let rv = bw_or(self.val, t.val);
            let rm = bw_and_not(bw_or(self.mask, t.mask), rv);
            assert forall|i: nat| #![auto] bit(bw_and_not(bw_or(c, tc), rm), i) == bit(rv, i) by {
                and_not_bit(c, self.mask, i);
                and_not_bit(tc, t.mask, i);
                or_bit(c, tc, i);
                or_bit(self.val, t.val, i);
                or_bit(self.mask, t.mask, i);
                and_not_bit(bw_or(self.mask, t.mask), rv, i);
                and_not_bit(bw_or(c, tc), rm, i);
            };
            eq_from_bits(bw_and_not(bw_or(c, tc), rm), rv);
        };
    }

    pub open spec fn bw_and(self, t: Tnum) -> Tnum {
        Tnum { val: bw_and(self.val, t.val), mask: bw_or(self.mask, t.mask) }
    }

    pub proof fn and_sound(self, t: Tnum)
        requires self.inv(), t.inv()
        ensures
            self.bw_and(t).inv(),
            forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc) ==> self.bw_and(t).has(bw_and(c, tc))
    {
        let rv = bw_and(self.val, t.val);
        let rm = bw_or(self.mask, t.mask);
        assert forall|i: nat| #![auto] !(bit(rv, i).b() && bit(rm, i).b()) by {
            and_bit(self.val, t.val, i);
            or_bit(self.mask, t.mask, i);
            // sv[i]=1 && tv[i]=1 ==> sm[i]=0 && tm[i]=0 (from inv)
            assert(!(bit(self.val, i).b() && bit(self.mask, i).b())) by { disj_bits(self.val, self.mask); };
            assert(!(bit(t.val, i).b() && bit(t.mask, i).b())) by { disj_bits(t.val, t.mask); };
        };
        disj_bits(rv, rm);
        assert forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc)
            implies self.bw_and(t).has(bw_and(c, tc)) by {
            self.has_equiv(c);
            t.has_equiv(tc);
            self.bw_and(t).has_equiv(bw_and(c, tc));
            let rv = bw_and(self.val, t.val);
            let rm = bw_or(self.mask, t.mask);
            assert forall|i: nat| #![auto] bit(bw_and_not(bw_and(c, tc), rm), i) == bit(rv, i) by {
                and_not_bit(c, self.mask, i);
                and_not_bit(tc, t.mask, i);
                and_bit(c, tc, i);
                and_bit(self.val, t.val, i);
                or_bit(self.mask, t.mask, i);
                and_not_bit(bw_and(c, tc), rm, i);
            };
            eq_from_bits(bw_and_not(bw_and(c, tc), rm), rv);
        };
    }

    pub open spec fn bw_and_not(self, t: Tnum) -> Tnum {
        Tnum { val: bw_and_not(bw_and_not(self.val, t.val), t.mask), mask: bw_or(self.mask, t.mask) }
    }

    pub proof fn and_not_sound(self, t: Tnum)
        ensures forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc) ==> self.bw_and_not(t).has(bw_and_not(c, tc))
    {
        assert forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc)
            implies self.bw_and_not(t).has(bw_and_not(c, tc)) by {
            self.has_equiv(c);
            t.has_equiv(tc);
            self.bw_and_not(t).has_equiv(bw_and_not(c, tc));
            let rv = bw_and_not(bw_and_not(self.val, t.val), t.mask);
            let rm = bw_or(self.mask, t.mask);
            assert forall|i: nat| #![auto] bit(bw_and_not(bw_and_not(c, tc), rm), i) == bit(rv, i) by {
                and_not_bit(c, self.mask, i);
                and_not_bit(tc, t.mask, i);
                and_not_bit(c, tc, i);
                and_not_bit(self.val, t.val, i);
                and_not_bit(bw_and_not(self.val, t.val), t.mask, i);
                or_bit(self.mask, t.mask, i);
                and_not_bit(bw_and_not(c, tc), rm, i);
            };
            eq_from_bits(bw_and_not(bw_and_not(c, tc), rm), rv);
        };
    }

    pub open spec fn bw_xor(self, t: Tnum) -> Tnum {
        let v = bw_xor(self.val, t.val);
        let m = bw_or(self.mask, t.mask);
        Tnum { val: bw_and_not(v, m), mask: m }
    }

    pub proof fn xor_sound(self, t: Tnum)
        ensures forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc) ==> self.bw_xor(t).has(bw_xor(c, tc))
    {
        assert forall|c: nat, tc: nat| #![auto] self.has(c) && t.has(tc)
            implies self.bw_xor(t).has(bw_xor(c, tc)) by {
            self.has_equiv(c);
            t.has_equiv(tc);
            self.bw_xor(t).has_equiv(bw_xor(c, tc));
            let rm = bw_or(self.mask, t.mask);
            let rv = bw_and_not(bw_xor(self.val, t.val), rm);
            assert forall|i: nat| #![auto] bit(bw_and_not(bw_xor(c, tc), rm), i) == bit(rv, i) by {
                and_not_bit(c, self.mask, i);
                and_not_bit(tc, t.mask, i);
                xor_bit(c, tc, i);
                xor_bit(self.val, t.val, i);
                or_bit(self.mask, t.mask, i);
                and_not_bit(bw_xor(self.val, t.val), rm, i);
                and_not_bit(bw_xor(c, tc), rm, i);
            };
            eq_from_bits(bw_and_not(bw_xor(c, tc), rm), rv);
        };
    }

    // ================================================================
    // Shifts
    // ================================================================

    pub open spec fn rsh(self) -> Tnum { Tnum { val: rsh(self.val), mask: rsh(self.mask) } }

    pub proof fn rsh_sound(self)
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rsh().has(rsh(n))
    {
        assert forall|n: nat| #![auto] self.has(n) implies self.rsh().has(rsh(n)) by {
            if !self.is_zero() {}
        };
    }

    pub open spec fn lsh(self) -> Tnum { Tnum { val: lsh(self.val), mask: lsh(self.mask) } }

    pub proof fn lsh_sound(self)
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lsh().has(lsh(n))
    {
        assert forall|n: nat| #![auto] self.has(n) implies self.lsh().has(lsh(n)) by {
            if self.is_zero() { assert(n == 0); }
            else {
                hd_cons(self.val, Bit::f());
                hd_cons(self.mask, Bit::f());
                hd_cons(n, Bit::f());
            }
        };
    }

    // ================================================================
    // Join
    // ================================================================

    pub open spec fn join(self, t: Tnum) -> Tnum {
        Tnum::uctor(bw_and(self.val, t.val), bw_or(self.u(), t.u()))
    }

    pub proof fn join_sound(self, t: Tnum)
        ensures
            forall|n: nat| #![auto] self.has(n) ==> self.join(t).has(n),
            forall|n: nat| #![auto] t.has(n) ==> self.join(t).has(n),
    {
        assert forall|n: nat| #![auto] self.has(n) implies self.join(t).has(n) by {
            self.has_equiv(n);
            self.join(t).has_equiv(n);
            // join.val = and(sv, tv), join.mask = xor(and(sv,tv), or(xor(sv,sm), xor(tv,tm)))
            // Need: andnot(n, join.mask) == join.val given andnot(n, sm) == sv
            let jv = bw_and(self.val, t.val);
            let ju = bw_or(self.u(), t.u());
            let jm = bw_xor(jv, ju);
            assert forall|i: nat| #![auto] bit(bw_and_not(n, jm), i) == bit(jv, i) by {
                and_not_bit(n, self.mask, i);
                and_bit(self.val, t.val, i);
                xor_bit(self.val, self.mask, i);
                xor_bit(t.val, t.mask, i);
                or_bit(bw_xor(self.val, self.mask), bw_xor(t.val, t.mask), i);
                xor_bit(jv, ju, i);
                and_not_bit(n, jm, i);
            };
            eq_from_bits(bw_and_not(n, jm), jv);
        };
        assert forall|n: nat| #![auto] t.has(n) implies self.join(t).has(n) by {
            t.has_equiv(n);
            self.join(t).has_equiv(n);
            let jv = bw_and(self.val, t.val);
            let ju = bw_or(self.u(), t.u());
            let jm = bw_xor(jv, ju);
            assert forall|i: nat| #![auto] bit(bw_and_not(n, jm), i) == bit(jv, i) by {
                and_not_bit(n, t.mask, i);
                and_bit(self.val, t.val, i);
                xor_bit(self.val, self.mask, i);
                xor_bit(t.val, t.mask, i);
                or_bit(bw_xor(self.val, self.mask), bw_xor(t.val, t.mask), i);
                xor_bit(jv, ju, i);
                and_not_bit(n, jm, i);
            };
            eq_from_bits(bw_and_not(n, jm), jv);
        };
    }


    // ================================================================
    // Addition
    // ================================================================

    pub open spec fn cons_tbit(self, b: TBit) -> Tnum {
        Tnum { val: cons(self.val, b.val), mask: cons(self.mask, b.mask) }
    }

    pub open spec fn add_carry(self, t: Tnum, carry: TBit) -> Tnum
        decreases self.size() + t.size()
    {
        if self.is_zero() && t.is_zero() {
            Tnum::zero().cons_tbit(carry)
        } else {
            let (b1, c1) = self.head().add_carry(t.head(), carry);
            self.tail().add_carry(t.tail(), c1).cons_tbit(b1)
        }
    }

    pub proof fn add_carry_sound(self, t: Tnum, carry: TBit)
        ensures forall|xc: nat, tc: nat, bc: Bit| #![auto]
            self.has(xc) && t.has(tc) && carry.has(bc) ==>
            self.add_carry(t, carry).has(nat_add_carry(xc, tc, bc))
        decreases self.size() + t.size()
    {
        assert forall|xc: nat, tc: nat, bc: Bit| #![auto]
            self.has(xc) && t.has(tc) && carry.has(bc)
            implies self.add_carry(t, carry).has(nat_add_carry(xc, tc, bc)) by {
            self.add_carry_sound1(t, carry, xc, tc, bc);
        };
    }

    #[verifier::rlimit(200)]
    proof fn add_carry_sound1(self, t: Tnum, carry: TBit, xc: nat, tc: nat, bc: Bit)
        requires self.has(xc), t.has(tc), carry.has(bc)
        ensures self.add_carry(t, carry).has(nat_add_carry(xc, tc, bc))
        decreases self.size() + t.size()
    {
        if self.is_zero() && t.is_zero() {
            hd_cons(0, carry.val);
            hd_cons(0, carry.mask);
        } else {
            if self.is_zero() { assert(xc == 0); }
            else { assert(self.head().has(hd(xc))); assert(self.tail().has(tl(xc))); }
            if t.is_zero() { assert(tc == 0); }
            else { assert(t.head().has(hd(tc))); assert(t.tail().has(tl(tc))); }

            let (b1, c1) = self.head().add_carry(t.head(), carry);
            let (rb, rc) = hd(xc).full_add(hd(tc), bc);

            // Tb.plus_c soundness — just the one instance we need
            assert(b1.has(rb) && c1.has(rc)) by {
                self.head().add_carry_sound(t.head(), carry);
            };

            // IH on tails
            self.tail().add_carry_sound1(t.tail(), c1, tl(xc), tl(tc), rc);

            // Connect head/tail of result and concrete value
            let r = self.tail().add_carry(t.tail(), c1);
            hd_cons(r.val, b1.val);
            hd_cons(r.mask, b1.mask);
            hd_cons(nat_add_carry(tl(xc), tl(tc), rc), rb);
        }
    }

    pub open spec fn add(self, t: Tnum) -> Tnum {
        self.add_carry(t, TBit { val: Bit::f(), mask: Bit::f() })
    }

    /// plusCZ: add(zero) == self
    pub proof fn add_carry_zero(self)
        requires self.inv()
        ensures self.add(Tnum::zero()) == self
        decreases self.size()
    {
        if self.is_zero() {
        } else {
            self.tail().add_carry_zero();
            Self::add_carry_zero_tb(self.head());
        }
    }

    /// Helper: adding Tb(F,F) with carry Tb(F,F) is identity
    proof fn add_carry_zero_tb(h: TBit)
        requires h.inv()
        ensures h.add_carry(TBit { val: Bit::f(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() })
            == (h, TBit { val: Bit::f(), mask: Bit::f() })
    {
        assert(TBit { val: Bit::f(), mask: Bit::f() }.add_carry(TBit { val: Bit::f(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() })
            == (TBit { val: Bit::f(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() }));
        assert(TBit { val: Bit::t(), mask: Bit::f() }.add_carry(TBit { val: Bit::f(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() })
            == (TBit { val: Bit::t(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() }));
        assert(TBit { val: Bit::f(), mask: Bit::t() }.add_carry(TBit { val: Bit::f(), mask: Bit::f() }, TBit { val: Bit::f(), mask: Bit::f() })
            == (TBit { val: Bit::f(), mask: Bit::t() }, TBit { val: Bit::f(), mask: Bit::f() }));
        assert(h.val == Bit::f() || h.val == Bit::t());
        assert(h.mask == Bit::f() || h.mask == Bit::t());
    }

    /// When both v's are 0 and carry.val is F, result.val is 0.
    pub proof fn add_carry_val_zero(self, t: Tnum, carry: TBit)
        requires self.val == 0, t.val == 0, !carry.val.b()
        ensures self.add_carry(t, carry).val == 0
        decreases self.size() + t.size()
    {
        if self.is_zero() && t.is_zero() {
            // result = zero().cons_tbit(carry) = Tn(cons(0, carry.val), cons(0, carry.mask))
            // carry.val == F, so cons(0, F) == 0
        } else {
            // head = Tb(F, hd(self.mask)), t.head = Tb(F, hd(t.mask)), carry = Tb(F, carry.mask)
            // Tb.plus_c: with all v's being F, result bit v is F and carry v is F
            // (exhaustive check on the boolean cases)
            let (b1, c1) = self.head().add_carry(t.head(), carry);
            // b1.val == F and c1.val == F (since all input v's are F)
            assert(!b1.val.b());
            assert(!c1.val.b());
            // IH: self.tail().add_carry(t.tail(), c1).val == 0
            self.tail().add_carry_val_zero(t.tail(), c1);
            // result = tail_result.cons_tbit(b1)
            // result.val = cons(tail_result.val, b1.val) = cons(0, F) = 0
        }
    }

    pub proof fn add_sound(self, t: Tnum)
        ensures forall|c: nat, tc: nat| #![auto]
            self.has(c) && t.has(tc) ==> self.add(t).has(nat_add(c, tc))
    {
        self.add_carry_sound(t, TBit { val: Bit::f(), mask: Bit::f() });
    }

    pub open spec fn add_bitwise(self, t: Tnum) -> Tnum {
        let lbv = nat_add(self.val, t.val);
        let lbm = nat_add(self.mask, t.mask);
        let ub = nat_add(lbv, lbm);
        let diff = bw_xor(ub, lbv);
        let mask = bw_or(bw_or(diff, self.mask), t.mask);
        Tnum::ctor(bw_and_not(lbv, mask), mask)
    }

    /// Linking lemma: plusBv computes the same result as plus (recursive).
    /// We prove it via membership extensionality: two inv Tnums with the
    /// same has set are structurally equal.
    pub proof fn add_bitwise_eq(self, t: Tnum)
        requires self.inv(), t.inv()
        ensures self.add_bitwise(t) == self.add(t)
    {
        let a = self.add_bitwise(t);
        let b = self.add(t);
        Self::add_bitwise_inv(self, t);
        Self::add_inv(self, t);
        Self::add_bitwise_sound(self, t);
        Self::tn_ext(a, b);
    }

    /// add preserves inv
    pub proof fn add_inv(self, t: Tnum)
        requires self.inv(), t.inv()
        ensures self.add(t).inv()
        decreases self.size() + t.size()
    {
        if self.is_zero() && t.is_zero() {
        } else {
            let (b1, c1) = self.head().add_carry(t.head(), TBit { val: Bit::f(), mask: Bit::f() });
            self.tail().add_inv_carry(t.tail(), c1);
        }
    }

    /// Generalized: plus_c preserves inv (with any inv carry)
    pub proof fn add_inv_carry(self, t: Tnum, carry: TBit)
        requires carry.inv()
        ensures self.add_carry(t, carry).inv()
        decreases self.size() + t.size()
    {
        if self.is_zero() && t.is_zero() {
            assert(!carry.val.b() || !carry.mask.b());
            disj_zero(0);
            disj_cons(0, carry.val, 0, carry.mask);
        } else {
            let (b1, c1) = self.head().add_carry(t.head(), carry);
            self.head().add_carry_inv(t.head(), carry);
            self.tail().add_inv_carry(t.tail(), c1);
            let r = self.tail().add_carry(t.tail(), c1);
            assert(!b1.val.b() || !b1.mask.b());
            disj_cons(r.val, b1.val, r.mask, b1.mask);
        }
    }

    pub proof fn add_bitwise_inv(self, t: Tnum)
        requires self.inv(), t.inv()
        ensures self.add_bitwise(t).inv()
    {
        let mask = bw_or(bw_or(bw_xor(nat_add(nat_add(self.val, t.val), nat_add(self.mask, t.mask)), nat_add(self.val, t.val)), self.mask), t.mask);
        assert forall|i: nat| #![auto] !(bit(bw_and_not(nat_add(self.val, t.val), mask), i).b() && bit(mask, i).b()) by {
            and_not_bit(nat_add(self.val, t.val), mask, i);
        };
        disj_bits(bw_and_not(nat_add(self.val, t.val), mask), mask);
    }

    /// add_bitwise has the same members as add.
    /// add_bitwise has the same members as add.
    /// Proof: for chopped (finite) inputs, both formulas produce the same result.
    /// Generalized non-recursive formula with two carries (v and m).
    /// The ub always uses carry F, matching Tb.plus_c's internal structure.
    pub open spec fn add_carry_bitwise(self, t: Tnum, cv: Bit, cm: Bit) -> Tnum {
        let lbv = nat_add_carry(self.val, t.val, cv);
        let lbm = nat_add_carry(self.mask, t.mask, cm);
        let ub = nat_add(lbv, lbm);  // always carry F, matching Tb.plus_c
        let diff = bw_xor(ub, lbv);
        let mask = bw_or(bw_or(diff, self.mask), t.mask);
        Tnum::ctor(bw_and_not(lbv, mask), mask)
    }

    /// add_bitwise == add_carry_bitwise with cv=F, cm=F
    /// add == plus_c with carry=Tb(F,F)
    /// We prove add_carry_bitwise(cv, cm) == nat_add_carry(Tb(cv, cm)) by induction.
    // ================================================================
    // add_bitwise_eq: the non-recursive addition formula equals the recursive one.
    //
    // This is the hardest theorem in the entire development.
    //
    // The non-recursive formula (add_bitwise / add_carry_bitwise):
    //   lbv = self.val + t.val + cv       (lower bound of value sum)
    //   lbm = self.mask + t.mask + cm       (lower bound of mask sum)
    //   ub  = lbv + lbm               (upper bound)
    //   mask = (ub XOR lbv) | self.mask | t.mask
    //   result = Tn(lbv AND NOT mask, mask)
    //
    // The recursive formula (plus_c):
    //   Process one bit at a time via Tb.plus_c, propagating a TBit carry.
    //
    // Proof architecture:
    //   add_bitwise_eq
    //     = add_bitwise_inv + add_inv + add_bitwise_sound + tn_ext
    //   add_bitwise_sound
    //     -> add_carry_bitwise_eq (generalized with carry)
    //       = add_carry_bitwise_inv + add_carry_bitwise_has_eq + tn_ext
    //   add_carry_bitwise_has_eq (inductive: has equivalence at every bit)
    //     = add_carry_bitwise_tl + has_equiv + mapd_hd_tl + IH
    //   add_carry_bitwise_tl (tail decomposition of non-recursive formula)
    //     = add_carry_carry_decomp + hd_cons + mapd_hd_tl + add_carry_correct
    //
    // The crux is add_carry_carry_decomp (in tbit.rs), specifically clause (4):
    //   c1.mask ==> (cm1 != ub_carry)
    // This carry compensation property ensures that when the recursive carry
    // is uncertain, the non-recursive formula's ub carry and m-carry sum to
    // the same total as the recursive formula's carry, so the tails match.
    // ================================================================

    proof fn add_bitwise_sound(self, t: Tnum)
        requires self.inv(), t.inv(), self.add_bitwise(t).inv()
        ensures forall|n: nat| #![auto] self.add_bitwise(t).has(n) <==> self.add(t).has(n)
    {
        Self::add_carry_bitwise_eq(self, t, Bit::f(), Bit::f());
        assert(self.add_bitwise(t) == self.add(t));
        assert forall|n: nat| #![auto] self.add_bitwise(t).has(n) <==> self.add(t).has(n) by {};
    }

    /// Structural equality: add_carry_bitwise(cv, cm) == nat_add_carry(Tb(cv, cm)).
    ///
    /// Proved via extensionality: both sides have inv (add_carry_bitwise_inv, add_inv_carry),
    /// both have the same `has` set (add_carry_bitwise_has_eq), therefore they are equal (tn_ext).
    proof fn add_carry_bitwise_eq(self, t: Tnum, cv: Bit, cm: Bit)
        requires self.inv(), t.inv(), !(cv.b() && cm.b())
        ensures self.add_carry_bitwise(t, cv, cm) == self.add_carry(t, TBit::mk(cv, cm))
        decreases self.size() + t.size()
    {
        let carry = TBit::mk(cv, cm);
        Self::add_carry_bitwise_inv(self, t, cv, cm);
        self.add_inv_carry(t, carry);
        Self::add_carry_bitwise_has_eq(self, t, cv, cm);
        Self::tn_ext(self.add_carry_bitwise(t, cv, cm), self.add_carry(t, carry));
    }

    proof fn add_carry_bitwise_inv(self, t: Tnum, cv: Bit, cm: Bit)
        requires self.inv(), t.inv()
        ensures self.add_carry_bitwise(t, cv, cm).inv()
    {
        let lbv = nat_add_carry(self.val, t.val, cv);
        let mask = bw_or(bw_or(bw_xor(nat_add(lbv, nat_add_carry(self.mask, t.mask, cm)), lbv), self.mask), t.mask);
        assert forall|i: nat| #![auto] !(bit(bw_and_not(lbv, mask), i).b() && bit(mask, i).b()) by {
            and_not_bit(lbv, mask, i);
        };
        disj_bits(bw_and_not(lbv, mask), mask);
    }

    /// Tail decomposition of the non-recursive addition formula.
    ///
    /// Shows that hd/tl of add_carry_bitwise(self, t, cv, cm) equal the Tb.plus_c head
    /// and add_carry_bitwise applied to the tails with the recursive carry c1.
    ///
    /// The proof splits on c1.mask (the carry-out uncertainty):
    ///
    /// Case c1.mask == F (carry is known):
    ///   From add_carry_carry_decomp: cm1 == F and ub_carry == F.
    ///   So tl(lbv) uses cv1 == c1.val, tl(lbm) uses cm1 == c1.mask == F,
    ///   and tl(ub) = nat_add_carry(tl(lbv), tl(lbm), F) = nat_add(tl(lbv), tl(lbm)).
    ///   Everything decomposes cleanly.
    ///
    /// Case c1.mask == T (carry is uncertain):
    ///   The non-recursive tail has tl(lbm) = nat_add_carry(tl(sm), tl(tm), cm1)
    ///   with ub carry = rv0 & rm0. The recursive tail has
    ///   tail_lbm = nat_add_carry(tl(sm), tl(tm), c1.mask=T) with ub carry = F.
    ///   These differ! But from add_carry_carry_decomp clause (4):
    ///     cm1 XOR ub_carry == T  (exactly one is 1)
    ///   So tl(lbm) + ub_carry == tail_lbm + 0 (carry compensation).
    ///   The ub tails are equal, so the masks and results match.
    proof fn add_carry_bitwise_tl(self, t: Tnum, cv: Bit, cm: Bit)
        requires self.inv(), t.inv(), !(cv.b() && cm.b()),
                 !(self.is_zero() && t.is_zero())
        ensures ({
            let (b1, c1) = self.head().add_carry(t.head(), TBit::mk(cv, cm));
            let tail_cbv = self.tail().add_carry_bitwise(t.tail(), c1.val, c1.mask);
            let full_cbv = self.add_carry_bitwise(t, cv, cm);
            &&& hd(full_cbv.val) == b1.val
            &&& hd(full_cbv.mask) == b1.mask
            &&& tl(full_cbv.val) == tail_cbv.val
            &&& tl(full_cbv.mask) == tail_cbv.mask
        })
    {
        let carry = TBit::mk(cv, cm);
        let (b1, c1) = self.head().add_carry(t.head(), carry);
        self.head().add_carry_carry_decomp(t.head(), carry);
        let cv1 = hd(self.val).full_add(hd(t.val), cv).1;
        let rv0 = hd(self.val).full_add(hd(t.val), cv).0;
        let cm1 = hd(self.mask).full_add(hd(t.mask), cm).1;
        let rm0 = hd(self.mask).full_add(hd(t.mask), cm).0;
        let lbv = nat_add_carry(self.val, t.val, cv);
        let lbm = nat_add_carry(self.mask, t.mask, cm);
        let ub = nat_add(lbv, lbm);
        let ub_carry = rv0.full_add(rm0, Bit::f()).1;
        let ub0 = rv0.full_add(rm0, Bit::f()).0;
        hd_cons(nat_add_carry(tl(self.val), tl(t.val), cv1), rv0);
        hd_cons(nat_add_carry(tl(self.mask), tl(t.mask), cm1), rm0);
        hd_cons(nat_add_carry(tl(lbv), tl(lbm), ub_carry), ub0);
        let diff = bw_xor(ub, lbv);
        let mask = bw_or(bw_or(diff, self.mask), t.mask);
        mapd_hd_tl(ub, lbv, |x: Bit, y: Bit| x.xor(y));
        mapd_hd_tl(diff, self.mask, |x: Bit, y: Bit| x.or(y));
        mapd_hd_tl(bw_or(diff, self.mask), t.mask, |x: Bit, y: Bit| x.or(y));
        mapd_hd_tl(lbv, mask, |x: Bit, y: Bit| x.and_not(y));
        assert(tl(lbv) == nat_add_carry(tl(self.val), tl(t.val), c1.val));
        if !c1.mask.b() {
            assert(tl(lbm) == nat_add_carry(tl(self.mask), tl(t.mask), c1.mask));
            assert(tl(ub) == nat_add(tl(lbv), tl(lbm)));
            let tail_lbv = nat_add_carry(tl(self.val), tl(t.val), c1.val);
            let tail_lbm = nat_add_carry(tl(self.mask), tl(t.mask), c1.mask);
            let tail_mask = bw_or(bw_or(bw_xor(nat_add(tail_lbv, tail_lbm), tail_lbv), tl(self.mask)), tl(t.mask));
            assert(tl(mask) == tail_mask);
            assert(tl(bw_and_not(lbv, mask)) == bw_and_not(tail_lbv, tail_mask));
        } else {
            let tail_lbv = nat_add_carry(tl(self.val), tl(t.val), c1.val);
            let tail_lbm = nat_add_carry(tl(self.mask), tl(t.mask), c1.mask);
            assert(nat_add_carry(tl(lbv), tl(lbm), ub_carry) == nat_add(tail_lbv, tail_lbm)) by {
                nat_add_carry_correct(tl(lbv), tl(lbm), ub_carry);
                nat_add_carry_correct(tail_lbv, tail_lbm, Bit::f());
                nat_add_carry_correct(tl(self.mask), tl(t.mask), cm1);
                nat_add_carry_correct(tl(self.mask), tl(t.mask), c1.mask);
            };
            let tail_ub = nat_add(tail_lbv, tail_lbm);
            assert(tl(ub) == tail_ub);
            let tail_mask = bw_or(bw_or(bw_xor(tail_ub, tail_lbv), tl(self.mask)), tl(t.mask));
            assert(tl(mask) == tail_mask);
            assert(tl(bw_and_not(lbv, mask)) == bw_and_not(tail_lbv, tail_mask));
        }
    }

    /// Has-set equivalence: add_carry_bitwise and plus_c contain the same values.
    ///
    /// Inductive proof. At each level:
    ///   add_carry_bitwise.has(n)
    ///     <==> andnot(n, mask) == v_bv                    [by has_equiv]
    ///     <==> hd matches AND tl matches                  [by mapd_hd_tl on andnot]
    ///     <==> b1.has(hd(n)) AND tail_cbv.has(tl(n))      [by add_carry_bitwise_tl]
    ///     <==> b1.has(hd(n)) AND tail_rec.has(tl(n))       [by IH]
    ///     <==> plus_c.has(n)                               [by definition of has]
    ///
    /// The key step is add_carry_bitwise_tl, which shows that the head and tail of
    /// add_carry_bitwise match the Tb.plus_c head and add_carry_bitwise on tails.
    #[verifier::rlimit(20000)]
    proof fn add_carry_bitwise_has_eq(self, t: Tnum, cv: Bit, cm: Bit)
        requires self.inv(), t.inv(), !(cv.b() && cm.b())
        ensures forall|n: nat| #![auto] self.add_carry_bitwise(t, cv, cm).has(n) <==> self.add_carry(t, TBit::mk(cv, cm)).has(n)
        decreases self.size() + t.size()
    {
        let carry = TBit::mk(cv, cm);
        if self.is_zero() && t.is_zero() {
        } else {
            let (b1, c1) = self.head().add_carry(t.head(), carry);
            self.head().add_carry_inv(t.head(), carry);
            self.tail().add_carry_bitwise_has_eq(t.tail(), c1.val, c1.mask);
            let full = self.add_carry_bitwise(t, cv, cm);
            let tail_cbv = self.tail().add_carry_bitwise(t.tail(), c1.val, c1.mask);
            Self::add_carry_bitwise_tl(self, t, cv, cm);
            assert forall|n: nat| #![auto] full.has(n) <==> self.add_carry(t, carry).has(n) by {
                full.has_equiv(n);
                tail_cbv.has_equiv(tl(n));
                mapd_hd_tl(n, full.mask, |x: Bit, y: Bit| x.and_not(y));
                // Pin the head/tail decomposition of full.has(n) via has_bw.
                assert(full.has_bw(n)
                    <==> b1.has(hd(n)) && tail_cbv.has_bw(tl(n)));
                // And pin the head/tail decomposition of add_carry(t, carry).has(n)
                // via the recursive definition of has.
                assert(self.add_carry(t, carry).has(n)
                    <==> b1.has(hd(n))
                      && self.tail().add_carry(t.tail(), c1).has(tl(n)));
            };
        }
    }

    /// Tnum extensionality: two inv Tnums with the same has set are equal.
    pub proof fn tn_ext(a: Tnum, b: Tnum)
        requires a.inv(), b.inv(),
            forall|n: nat| #![auto] a.has(n) <==> b.has(n)
        ensures a == b
        decreases a.size() + b.size()
    {
        if a.is_zero() && b.is_zero() {
        } else if a.is_zero() {
            // a.has(n) <==> n == 0. b is not zero.
            // b.has(0) is true (since a.has(0)).
            // b.has_equiv(0): andnot(0, b.mask) == b.val, so b.val == 0.
            // b.mask > 0 since b is not zero. So b.has(b.mask): andnot(b.mask, b.mask) == 0 == b.val. True.
            // But a.has(b.mask) requires b.mask == 0. Contradiction.
            a.has_equiv(0);
            b.has_equiv(0);
            assert(b.val == 0) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(0 as nat, b.mask), i) == bit(0 as nat, i) by {
                    and_not_bit(0, b.mask, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(0, b.mask), 0);
            };
            // b.mask > 0, so b.has(b.mask)
            b.has_equiv(b.mask);
            assert(bw_and_not(b.mask, b.mask) == 0) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(b.mask, b.mask), i) == bit(0 as nat, i) by {
                    and_not_bit(b.mask, b.mask, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(b.mask, b.mask), 0);
            };
            // So b.has(b.mask) is true. But a.has(b.mask) requires b.mask == 0.
            a.has_equiv(b.mask);
            assert(bw_and_not(b.mask, 0) == b.mask) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(b.mask, 0 as nat), i) == bit(b.mask, i) by {
                    and_not_bit(b.mask, 0, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(b.mask, 0), b.mask);
            };
            // a.has(b.mask) <==> b.mask == 0. But b.mask > 0. Contradiction with a.has <==> b.has.
        } else if b.is_zero() {
            // Symmetric to above
            a.has_equiv(0);
            b.has_equiv(0);
            assert(a.val == 0) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(0 as nat, a.mask), i) == bit(0 as nat, i) by {
                    and_not_bit(0, a.mask, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(0, a.mask), 0);
            };
            a.has_equiv(a.mask);
            assert(bw_and_not(a.mask, a.mask) == 0) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(a.mask, a.mask), i) == bit(0 as nat, i) by {
                    and_not_bit(a.mask, a.mask, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(a.mask, a.mask), 0);
            };
            b.has_equiv(a.mask);
            assert(bw_and_not(a.mask, 0) == a.mask) by {
                assert forall|i: nat| #![auto] bit(bw_and_not(a.mask, 0 as nat), i) == bit(a.mask, i) by {
                    and_not_bit(a.mask, 0, i);
                    bit_zero(i);
                };
                eq_from_bits(bw_and_not(a.mask, 0), a.mask);
            };
        } else {
            // Both non-zero. Prove heads equal, then tails by IH.
            // a.head().has(b) for b in {F, T} matches b.head().has(b).
            // Use n = cons(0, F) and n = cons(0, T) as witnesses.
            assert(a.head() == b.head()) by {
                // a.has(a.val) is always true (by has_equiv + inv)
                a.has_equiv(a.val);
                b.has_equiv(a.val);
                b.has_equiv(b.val);
                // So a.head().has(hd(a.val)) && a.tail().has(tl(a.val)) is true.
                // And b.has(a.val) is true, so b.head().has(hd(a.val)) && b.tail().has(tl(a.val)).
                // Use n = cons(tl(a.val), F) and n = cons(tl(a.val), T) to test both head values.
                let m0 = tl(a.val);
                // a.tail().has(m0) is true (from a.has(a.val))
                // b.tail().has(m0) is true (from b.has(a.val))

                // Test F: n = cons(m0, F)
                let nf = cons(m0, Bit::f());
                hd_cons(m0, Bit::f());
                // a.has(nf) <==> a.head().has(F) && a.tail().has(m0) <==> a.head().has(F)
                // b.has(nf) <==> b.head().has(F) && b.tail().has(m0) <==> b.head().has(F)
                // So a.head().has(F) <==> b.head().has(F)

                // Test T: n = cons(m0, T)
                let nt = cons(m0, Bit::t());
                hd_cons(m0, Bit::t());
                // a.has(nt) <==> a.head().has(T) && a.tail().has(m0) <==> a.head().has(T)
                // b.has(nt) <==> b.head().has(T) && b.tail().has(m0) <==> b.head().has(T)
                // So a.head().has(T) <==> b.head().has(T)

                // TBit is determined by has(F) and has(T):
                // (F,F): has(F)=T, has(T)=F
                // (T,F): has(F)=F, has(T)=T
                // (F,T): has(F)=T, has(T)=T
                // So if has(F) and has(T) match, the Tb's are equal.
                // Force the solver to case-split on the head components:
                // a.has(a.val) is true, and since a is not zero, it decomposes
                a.has_equiv(a.val);
                assert(a.has_bw(a.val)) by {
                    assert forall|i: nat| #![auto] bit(bw_and_not(a.val, a.mask), i) == bit(a.val, i) by {
                        and_not_bit(a.val, a.mask, i);
                        disj_bits(a.val, a.mask);
                    };
                    eq_from_bits(bw_and_not(a.val, a.mask), a.val);
                };
                assert(a.has(a.val));
                // Since a is not zero, has unfolds: a.head().has(hd(a.val)) && a.tail().has(tl(a.val))
                assert(a.head().has(hd(a.val)) && a.tail().has(m0));
                // b.has(a.val) is also true
                b.has_equiv(a.val);
                assert(b.has(a.val));
                assert(b.head().has(hd(a.val)) && b.tail().has(m0));
                assert(a.has(nf) == (a.head().has(Bit::f()) && a.tail().has(m0)));
                assert(b.has(nf) == (b.head().has(Bit::f()) && b.tail().has(m0)));
                assert(a.has(nf) == b.has(nf));
                assert(a.head().has(Bit::f()) <==> b.head().has(Bit::f()));
                assert(a.has(nt) == (a.head().has(Bit::t()) && a.tail().has(m0)));
                assert(b.has(nt) == (b.head().has(Bit::t()) && b.tail().has(m0)));
                assert(a.has(nt) == b.has(nt));
                assert(a.head().has(Bit::t()) <==> b.head().has(Bit::t()));
                // Now case split on a.head() to determine b.head()
                if a.head().val.b() {
                    // a.head() = Tb(T, F): has(F)=F, has(T)=T
                    // b.head().has(F)=F, b.head().has(T)=T => b.head() = Tb(T, F)
                } else if a.head().mask.b() {
                    // a.head() = Tb(F, T): has(F)=T, has(T)=T
                    // b.head().has(F)=T, b.head().has(T)=T => b.head() = Tb(F, T)
                } else {
                    // a.head() = Tb(F, F): has(F)=T, has(T)=F
                    // b.head().has(F)=T, b.head().has(T)=F => b.head() = Tb(F, F)
                }
                if b.head().val.b() {} else if b.head().mask.b() {} else {}
            };
            assert forall|m: nat| #![auto] a.tail().has(m) <==> b.tail().has(m) by {
                // Since a.head() == b.head(), pick b0 with a.head().has(b0).
                // n = cons(m, b0): a.has(n) <==> a.head().has(b0) && a.tail().has(m)
                //                  b.has(n) <==> b.head().has(b0) && b.tail().has(m)
                // Since a.head().has(b0) == b.head().has(b0) == true:
                //   a.tail().has(m) <==> b.tail().has(m)
                if !a.head().val.b() {
                    let n = cons(m, Bit::f());
                    hd_cons(m, Bit::f());
                    assert(a.has(n) <==> a.tail().has(m));
                    assert(b.has(n) <==> b.tail().has(m));
                } else {
                    let n = cons(m, Bit::t());
                    hd_cons(m, Bit::t());
                    assert(a.has(n) <==> a.tail().has(m));
                    assert(b.has(n) <==> b.tail().has(m));
                }
            };
            Self::tn_ext(a.tail(), b.tail());
        }
    }

    // ================================================================
    // ================================================================
    // Meet (intersection)
    // ================================================================

    /// Precondition for meet: the two Tnums are compatible.
    pub open spec fn meet_ok(self, t: Tnum) -> bool {
        bw_and(bw_or(self.val, t.val), bw_and_not(self.u(), t.u())) == 0
    }

    /// Meet (intersection) of two Tnums.
    pub open spec fn meet(self, t: Tnum) -> Tnum {
        Tnum::uctor(bw_or(self.val, t.val), bw_and(self.u(), t.u()))
    }

    /// Soundness of meet: intersection contains all common members.
    pub proof fn meet_sound(self, t: Tnum)
        ensures forall|n: nat| #![auto] self.has(n) && t.has(n) ==> self.meet(t).has(n)
    {
        assert forall|n: nat| #![auto] self.has(n) && t.has(n)
            implies self.meet(t).has(n) by {
            self.has_equiv(n);
            t.has_equiv(n);
            self.meet(t).has_equiv(n);
            // self.has(n): andnot(n, self.mask) == self.val
            // t.has(n): andnot(n, t.mask) == t.val
            // meet(t) = uctor(or(self.val, t.val), and(self.u(), t.u()))
            //         = Tn(v=or(self.val,t.val), m=xor(or(self.val,t.val), and(self.u(),t.u())))
            // meet(t).has(n): andnot(n, meet.mask) == meet.val
            // Need: andnot(n, xor(or(sv,tv), and(xor(sv,sm), xor(tv,tm)))) == or(sv,tv)
            // This is a bitwise property that follows from the membership conditions.
            assert forall|i: nat| #![auto]
                bit(bw_and_not(n, self.meet(t).mask), i) == bit(self.meet(t).val, i) by {
                and_not_bit(n, self.mask, i);
                and_not_bit(n, t.mask, i);
                and_not_bit(n, self.meet(t).mask, i);
                or_bit(self.val, t.val, i);
                xor_bit(self.val, self.mask, i);
                xor_bit(t.val, t.mask, i);
                and_bit(bw_xor(self.val, self.mask), bw_xor(t.val, t.mask), i);
                xor_bit(bw_or(self.val, t.val), bw_and(bw_xor(self.val, self.mask), bw_xor(t.val, t.mask)), i);
            };
            eq_from_bits(bw_and_not(n, self.meet(t).mask), self.meet(t).val);
        };
    }

    // ================================================================
    // Multi-bit shifts: lshi, rshi
    // ================================================================

    /// Left shift by i bits.
    pub open spec fn lshi(self, i: nat) -> Tnum {
        Tnum { val: lshi(self.val, i), mask: lshi(self.mask, i) }
    }

    /// Soundness of lshi: left shift by i bits.
    pub proof fn lshi_sound(self, i: nat)
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lshi(i).has(lshi(n, i))
        decreases i
    {
        if i > 0 {
            self.lshi_sound((i - 1) as nat);
            assert forall|n: nat| #![auto] self.has(n)
                implies self.lshi(i).has(lshi(n, i)) by {
                // lshi(n, i) = lsh(lshi(n, i-1))
                // By IH: lshi(i-1).has(lshi(n, i-1))
                // By lsh_sound: lshi(i-1).lsh().has(lsh(lshi(n, i-1)))
                self.lshi((i - 1) as nat).lsh_sound();
                // lshi(i) == lshi(i-1).lsh()
                // This follows from lshi(v, i) = lsh(lshi(v, i-1))
            };
        }
    }

    /// Right shift by i bits.
    pub open spec fn rshi(self, i: nat) -> Tnum {
        Tnum { val: rshi(self.val, i), mask: rshi(self.mask, i) }
    }

    /// Soundness of rshi: right shift by i bits.
    pub proof fn rshi_sound(self, i: nat)
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rshi(i).has(rshi(n, i))
        decreases i
    {
        if i > 0 {
            self.rsh_sound();
            self.rsh().rshi_sound((i - 1) as nat);
            assert forall|n: nat| #![auto] self.has(n)
                implies self.rshi(i).has(rshi(n, i)) by {
                // rshi(n, i) = rshi(rsh(n), i-1)
                // By rsh_sound: rsh().has(rsh(n))
                // By IH: rsh().rshi(i-1).has(rshi(rsh(n), i-1))
                // rshi(i) == rsh().rshi(i-1)
                // This follows from rshi(v, i) = rshi(rsh(v), i-1)
            };
        }
    }

    // ================================================================
    // Negation (two's complement, bounded)
    // ================================================================

    /// Two's complement negation of a Tnum (w-bit).
    /// We prove this via xor_sound + add_sound + chop_sound.
    /// Note: neg_tn is also defined in div.rs with full soundness proof.
    pub open spec fn neg(self, w: nat) -> Tnum {
        self.bw_xor(Tnum::unit(all_ones(w))).add_bitwise(Tnum::unit(1)).chop_tn(w)
    }

    // ================================================================
    // timesB, addZ, ne, chop
    // ================================================================

    pub open spec fn add_zero(self) -> Tnum { Tnum::ctor(0, self.max()) }

    pub open spec fn mul_bit(self, b: TBit) -> Tnum {
        if b.val.b() { self }
        else if b.mask.b() { self.add_zero() }
        else { Tnum::zero() }
    }


    pub proof fn times_b_inv(self, b: TBit)
        requires self.inv()
        ensures self.mul_bit(b).inv()
    {
        if b.val.b() {
        } else if b.mask.b() {
            disj_bits(0, bw_or(self.val, self.mask));
            assert forall|i: nat| #![auto] !(bit(0 as nat, i).b() && bit(bw_or(self.val, self.mask), i).b()) by {
                bit_zero(i);
            };
            disj_bits(0, bw_or(self.val, self.mask));
        } else {
        }
    }
    pub proof fn mul_bit_sound(self, b: TBit)
        requires self.inv()
        ensures forall|x: nat, y: Bit| #![auto] self.has(x) && b.has(y) ==> self.mul_bit(b).has(nat_mul_bit(x, y))
    {
        assert forall|x: nat, y: Bit| #![auto] self.has(x) && b.has(y)
            implies self.mul_bit(b).has(nat_mul_bit(x, y)) by {
            self.has_equiv(x);
            if b.val.b() {
                // b.has(y) && b.val == T ==> y == T
                // nat_mul_bit(x, T) == x, self.mul_bit(Tb(T,_)) == self
            } else if b.mask.b() {
                // b = Tb(F, T) = top, y is T or F
                // nat_mul_bit(x, y) is x or 0
                // result = add_zero() = Tn(0, max) = Tn(0, or(v, m))
                self.mul_bit(b).has_equiv(nat_mul_bit(x, y));
                if y.b() {
                    // nat_mul_bit(x, T) == x
                    // Need: andnot(x, or(v,m)) == 0
                    assert forall|i: nat| #![auto] bit(bw_and_not(x, bw_or(self.val, self.mask)), i) == bit(0 as nat, i) by {
                        and_not_bit(x, self.mask, i);
                        or_bit(self.val, self.mask, i);
                        and_not_bit(x, bw_or(self.val, self.mask), i);
                        bit_zero(i);
                    };
                    eq_from_bits(bw_and_not(x, bw_or(self.val, self.mask)), 0);
                } else {
                    // nat_mul_bit(x, F) == 0
                    // Need: andnot(0, or(v,m)) == 0
                    assert forall|i: nat| #![auto] bit(bw_and_not(0 as nat, bw_or(self.val, self.mask)), i) == bit(0 as nat, i) by {
                        and_not_bit(0, bw_or(self.val, self.mask), i);
                        bit_zero(i);
                    };
                    eq_from_bits(bw_and_not(0, bw_or(self.val, self.mask)), 0);
                }
            } else {
                // b = Tb(F, F), y must be F
                // nat_mul_bit(x, F) == 0, result = zero, zero.has(0) ✓
            }
        };
    }

    pub open spec fn ne(self, t: Tnum) -> bool {
        self.bw_xor(t).min() != 0
    }

    pub open spec fn chop_tn(self, i: nat) -> Tnum {
        Tnum { val: chop(self.val, i), mask: chop(self.mask, i) }
    }

    pub proof fn chop_sound(self, i: nat)
        requires self.inv()
        ensures
            self.chop_tn(i).inv(),
            forall|n: nat| #![auto] self.has(n) ==> self.chop_tn(i).has(chop(n, i)),
    {
        chop_disj(self.val, self.mask, i);
        assert forall|n: nat| #![auto] self.has(n) implies self.chop_tn(i).has(chop(n, i)) by {
            self.has_equiv(n);
            self.chop_tn(i).has_equiv(chop(n, i));
            // Need: andnot(chop(n,i), chop(m,i)) == chop(v,i)
            // given: andnot(n, m) == v
            // This is: chop(andnot(n,m), i) == chop(v, i)
            // which follows from chop_mapd
            chop_mapd(n, self.mask, |x: Bit, y: Bit| x.and_not(y), i);
        };
    }

    // ================================================================
}

/// Helper: bw_or(a, b) == 0 implies a == 0 and b == 0
pub proof fn or_zero(a: nat, b: nat)
    requires bw_or(a, b) == 0
    ensures a == 0, b == 0
{
    assert forall|i: nat| #![auto] bit(a, i) == Bit::f() by { or_bit(a, b, i); bit_zero(i); };
    assert forall|i: nat| #![auto] bit(b, i) == Bit::f() by { or_bit(a, b, i); bit_zero(i); };
    assert forall|i: nat| #![auto] bit(a, i) == bit(0 as nat, i) by { bit_zero(i); };
    assert forall|i: nat| #![auto] bit(b, i) == bit(0 as nat, i) by { bit_zero(i); };
    eq_from_bits(a, 0);
    eq_from_bits(b, 0);
}

} // verus!
