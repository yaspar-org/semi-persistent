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

    /// Multiplication: t0 * t using Anum accumulator.
    pub open spec fn mul_step(t0: Tnum, t: Tnum, a: Anum) -> Tnum
        decreases t0.size()
    {
        if t0.is_zero() { a.to_tnum() }
        else {
            Anum::mul_step(
                t0.rsh(),
                t.lsh(),
                a.add(Anum::from_tnum(t.mul_bit(t0.head()))),
            )
        }
    }

    pub proof fn mul_step_sound(t0: Tnum, t: Tnum, a: Anum)
        requires t0.inv(), t.inv()
        ensures forall|x: nat, y: nat, z: nat| #![auto]
            t0.has(x) && t.has(y) && a.has(z) ==>
            Anum::mul_step(t0, t, a).has(nat_mul_acc(x, y, z))
        decreases t0.size()
    {
        assert forall|x: nat, y: nat, z: nat| #![auto]
            t0.has(x) && t.has(y) && a.has(z)
            implies Anum::mul_step(t0, t, a).has(nat_mul_acc(x, y, z)) by {
            Anum::mul_step_sound1(t0, t, a, x, y, z);
        };
    }

    proof fn mul_step_sound1(t0: Tnum, t: Tnum, a: Anum, x: nat, y: nat, z: nat)
        requires t0.inv(), t.inv(), t0.has(x), t.has(y), a.has(z)
        ensures Anum::mul_step(t0, t, a).has(nat_mul_acc(x, y, z))
        decreases t0.size()
    {
        if t0.is_zero() {
            assert(x == 0);
            Anum::tnum_has_from_anum(a, z);
        } else {
            // Step: chain the component lemmas
            let tb = t.mul_bit(t0.head());

            // 1. rsh/lsh preserve inv
            Anum::rsh_inv(t0);
            Anum::lsh_inv(t);

            // 2. times_b is sound and preserves inv
            t.times_b_inv(t0.head());

            // 3. Build new accumulator
            let a1 = a.add(Anum::from_tnum(tb));

            // 4. New accumulator has the right concrete value
            assert(t0.head().has(hd(x))) by {
                if t0.is_zero() {} // contradiction
            };
            Anum::mul_step_acc(t, t0.head(), a, x, y, z);

            // 5. Unfold times1
            Anum::times1_unfold(x, y, z);

            // 6. IH
            Anum::mul_step_sound1(t0.rsh(), t.lsh(), a1, tl(x), lsh(y), nat_add(z, nat_mul_bit(y, hd(x))));
        }
    }

    /// Base case: a.has(z) ==> a.to_tnum().has(z)
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
    proof fn rsh_inv(t: Tnum)
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
    proof fn lsh_inv(t: Tnum)
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

    pub open spec fn tnum_mul(t0: Tnum, t1: Tnum) -> Tnum {
        Anum::mul_step(t0, t1, Anum::zero())
    }

    pub proof fn tnum_mul_sound(t0: Tnum, t1: Tnum)
        requires t0.inv(), t1.inv()
        ensures
            Anum::tnum_mul(t0, t1).inv(),
            forall|x: nat, y: nat| #![auto]
                t0.has(x) && t1.has(y) ==> Anum::tnum_mul(t0, t1).has(nat_mul_acc(x, y, 0))
    {
        Anum::mul_step_sound(t0, t1, Anum::zero());
        Anum::times2_inv(t0, t1, Anum::zero());
    }

    proof fn times2_inv(t0: Tnum, t: Tnum, a: Anum)
        requires t0.inv(), t.inv()
        ensures Anum::mul_step(t0, t, a).inv()
        decreases t0.size()
    {
        if t0.is_zero() {
            disj_zero(a.span);
            assert forall|j: nat| #![auto] !(bit(a.base, j).b() && bit(0 as nat, j).b()) by { bit_zero(j); };
            disj_bits(a.base, 0);
            Tnum::ctor(0, a.span).add_inv(Tnum::ctor(a.base, 0));
        } else {
            Anum::rsh_inv(t0);
            Anum::lsh_inv(t);
            t.times_b_inv(t0.head());
            Anum::times2_inv(t0.rsh(), t.lsh(), a.add(Anum::from_tnum(t.mul_bit(t0.head()))));
        }
    }

    // ================================================================
    // mul_step_rc / times2R: tail-recursive multiplication for bounded simulation
    //
    // ================================================================

    /// Raw tail-recursive multiplication loop.
    /// Uses add (not add_bitwise) so no linking lemma is needed at Layer 2.
    /// The bounded Layer 4 version will use add_bitwise and prove simulation.
    pub open spec fn mul_step_rc(t0: Tnum, t: Tnum, p: Tnum, q: Tnum, acc_v: Tnum, acc_m: Tnum, a: Anum) -> Tnum
        decreases p.size()
    {
        if p.is_zero() {
            acc_m.add(acc_v)
        } else {
            let a1 = a.add(Anum::from_tnum(q.mul_bit(p.head())));
            let p1 = p.rsh();
            let q1 = q.lsh();
            if p.head().val.b() {
                Anum::mul_step_rc(t0, t, p1, q1, acc_v, acc_m.add(Tnum::ctor(0, q.mask)), a1)
            } else if p.head().mask.b() {
                Anum::mul_step_rc(t0, t, p1, q1, acc_v, acc_m.add(Tnum::ctor(0, q.max())), a1)
            } else {
                Anum::mul_step_rc(t0, t, p1, q1, acc_v, acc_m, a1)
            }
        }
    }

    /// Simulation proof: mul_step_rc equals mul_step(t0, t, Anum::zero()).
    pub proof fn mul_step_r(t0: Tnum, t: Tnum, p: Tnum, q: Tnum, acc_v: Tnum, acc_m: Tnum, a: Anum)
        requires
            Anum::mul_step(t0, t, Anum::zero()) == Anum::mul_step(p, q, a),
            acc_v == Tnum::ctor(mul(t0.val, t.val), 0),
            acc_m == a.mask_tnum(),
            mul(t0.val, t.val) == nat_mul_acc(p.val, q.val, a.base),
        ensures
            Anum::mul_step_rc(t0, t, p, q, acc_v, acc_m, a) == Anum::mul_step(t0, t, Anum::zero()),
        decreases p.size()
    {
        a.add_zero();
        if p.is_zero() {
            // p.val == 0, so nat_mul_acc(0, q.val, a.base) == a.base
            // Therefore mul(t0.val, t.val) == a.base
            // acc_v == Tnum::ctor(a.base, 0) == a.val_tnum()
            // acc_m == a.mask_tnum()
            // acc_m.add(acc_v) == a.mask_tnum().add(a.val_tnum()) == a.to_tnum()
            // mul_step(p, q, a) == a.to_tnum() (since p.is_zero())
        } else {
            let a1 = a.add(Anum::from_tnum(q.mul_bit(p.head())));
            let p1 = p.rsh();
            let q1 = q.lsh();

            // times1 invariant maintenance:
            // nat_mul_acc(p.val, q.val, a.base) unfolds when p.val != 0
            Anum::times1_unfold(p.val, q.val, a.base);

            if p.head().val.b() {
                // q.mul_bit(Tb(T,F)) == q, from_tnum(q).mask_tnum() == Tn(0, q.mask)
                // a1.mask == a.mask_tnum().add(Tn(0, q.mask)).m
                // acc_m' == a.mask_tnum().add(Tn(0, q.mask))
                // acc_m'.v == 0 by add_carry_val_zero
                let acc_m1 = acc_m.add(Tnum::ctor(0, q.mask));
                assert(acc_m1.val == 0) by {
                    a.mask_tnum().add_carry_val_zero(Tnum::ctor(0, q.mask), TBit { val: Bit::f(), mask: Bit::f() });
                };
                // So acc_m' == Tn(0, acc_m'.m) == a1.mask_tnum()
                Anum::mul_step_r(t0, t, p1, q1, acc_v, acc_m1, a1);
            } else if p.head().mask.b() {
                // q.mul_bit(Tb(F,T)) == q.add_zero() == Tn(0, q.val|q.mask) = Tn(0, q.max())
                // from_tnum(Tn(0, q.max())).mask_tnum() == Tn(0, q.max())
                let acc_m1 = acc_m.add(Tnum::ctor(0, q.max()));
                assert(acc_m1.val == 0) by {
                    a.mask_tnum().add_carry_val_zero(Tnum::ctor(0, q.max()), TBit { val: Bit::f(), mask: Bit::f() });
                };
                Anum::mul_step_r(t0, t, p1, q1, acc_v, acc_m1, a1);
            } else {
                // p.head() == Tb(F,F): q.mul_bit(Tb(F,F)) == zero
                // a1 == a.add(from_tnum(zero)) == a.add(Anum::zero()) == a
                // acc_m unchanged
                Anum::mul_step_r(t0, t, p1, q1, acc_v, acc_m, a1);
            }
        }
    }
    // ================================================================
    // Anum-level multiplication: Anum × An → An (preserves additive structure)
    // ================================================================

    /// Anum multiplication loop — same as times2 but returns Anum, not Tn.
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

    /// Soundness of mul_step_anum — same as mul_step_sound.
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
}

} // verus!
