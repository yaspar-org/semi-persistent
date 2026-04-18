// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Unums: horizontally composable additive tristate numbers.
//! Layer 2 proofs on infinite bitstrings (nat).

use crate::anum::Anum;
use crate::bools::Bit;
use crate::nats::*;
use crate::tbit::TBit;
use crate::tnum::Tnum;
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn field_admits(w: nat, x: nat, d: nat, borrow: Bit, first: bool) -> bool
    decreases w + x + d
{
    if w == 0 && x == 0 && d == 0 { !borrow.b() }
    else if w == 0 && x == 0 { false }
    else {
        if hd(w).b() && !first && borrow.b() { false }
        else {
            let diff: int = hd(x).n() as int - hd(d).n() as int - borrow.n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            field_admits(tl(w), tl(x), tl(d), nb, false)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Unum { pub base: nat, pub walls: nat, pub extent: nat }

impl Unum {
    pub open spec fn has(self, n: nat) -> bool {
        n >= self.base && field_admits(self.walls, self.extent, nat_sub(n, self.base), Bit::f(), true)
    }

    pub open spec fn carry_out_c(a: nat, b: nat, c: Bit) -> nat
        decreases a + b
    {
        if a == 0 && b == 0 { 0 }
        else { let (_, c1) = hd(a).full_add(hd(b), c); cons(Self::carry_out_c(tl(a), tl(b), c1), c1) }
    }

    pub open spec fn carry_out(a: nat, b: nat) -> nat { Self::carry_out_c(a, b, Bit::f()) }

    pub open spec fn add(self, other: Unum) -> Unum {
        let x12 = nat_add(self.extent, other.extent);
        let w = bw_and_not(bw_and(self.walls, other.walls), lsh(Self::carry_out(self.extent, other.extent)));
        Unum { base: nat_add(self.base, other.base), walls: w, extent: x12 }
    }

    /// THE soundness theorem.
    pub proof fn add_sound(self, other: Unum)
        ensures forall|c1: nat, c2: nat| #![auto]
            self.has(c1) && other.has(c2) ==> self.add(other).has(nat_add(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto]
            self.has(c1) && other.has(c2) implies self.add(other).has(nat_add(c1, c2)) by {
            if self.has(c1) && other.has(c2) {
                let d1 = nat_sub(c1, self.base); let d2 = nat_sub(c2, other.base);
                nat_add_correct(c1, c2); nat_add_correct(self.base, other.base); nat_add_correct(d1, d2);
                Self::field_admits_add(self.walls, self.extent, d1, other.walls, other.extent, d2);
            }
        };
    }

    proof fn field_admits_add(w1: nat, x1: nat, d1: nat, w2: nat, x2: nat, d2: nat)
        requires field_admits(w1, x1, d1, Bit::f(), true), field_admits(w2, x2, d2, Bit::f(), true)
        ensures field_admits(
            bw_and_not(bw_and(w1, w2), lsh(Self::carry_out(x1, x2))),
            nat_add(x1, x2), nat_add(d1, d2), Bit::f(), true)
    {
        Self::field_admits_add_carry(w1, x1, d1, Bit::f(), true, w2, x2, d2, Bit::f(), true,
                               Bit::f(), Bit::f(), Bit::f());
    }

    /// Core inductive lemma. Invariant: cd + br <= cx + b1 + b2.
    /// Ensures first=TRUE always (leader check at bit 0 skipped).
    #[verifier::rlimit(10000)]
    proof fn field_admits_add_carry(
        w1: nat, x1: nat, d1: nat, b1: Bit, first1: bool,
        w2: nat, x2: nat, d2: nat, b2: Bit, first2: bool,
        cd: Bit, cx: Bit, br: Bit,
    )
        requires
            field_admits(w1, x1, d1, b1, first1),
            field_admits(w2, x2, d2, b2, first2),
            cd.n() + br.n() <= cx.n() + b1.n() + b2.n(),
        ensures field_admits(
            bw_and_not(bw_and(w1, w2), lsh(Self::carry_out_c(x1, x2, cx))),
            nat_add_carry(x1, x2, cx), nat_add_carry(d1, d2, cd), br, true)
        decreases w1 + x1 + d1 + w2 + x2 + d2
    {
        reveal_with_fuel(field_admits, 1);
        if w1 == 0 && x1 == 0 && d1 == 0 && w2 == 0 && x2 == 0 && d2 == 0 {
            nat_add_carry_correct(0, 0, cx);
            nat_add_carry_correct(0, 0, cd);
            Self::field_admits_leq(cx.n(), cd.n(), br, true);
        } else {
            assert(!(w1 == 0 && x1 == 0) || d1 == 0);
            assert(!(w2 == 0 && x2 == 0) || d2 == 0);
            let (d12h, ncd) = hd(d1).full_add(hd(d2), cd);
            let (x12h, ncx) = hd(x1).full_add(hd(x2), cx);
            let diff_r: int = x12h.n() as int - d12h.n() as int - br.n() as int;
            let nbr = if diff_r < 0 { Bit::t() } else { Bit::f() };
            let diff1: int = hd(x1).n() as int - hd(d1).n() as int - b1.n() as int;
            let nb1 = if diff1 < 0 { Bit::t() } else { Bit::f() };
            let diff2: int = hd(x2).n() as int - hd(d2).n() as int - b2.n() as int;
            let nb2 = if diff2 < 0 { Bit::t() } else { Bit::f() };

            assert(hd(x1).n() <= 1 && hd(d1).n() <= 1 && hd(x2).n() <= 1 && hd(d2).n() <= 1) by {
                assert(hd(x1) == Bit::t() || hd(x1) == Bit::f());
                assert(hd(d1) == Bit::t() || hd(d1) == Bit::f());
                assert(hd(x2) == Bit::t() || hd(x2) == Bit::f());
                assert(hd(d2) == Bit::t() || hd(d2) == Bit::f());
            };
            Self::inv_step(hd(x1).n(), hd(d1).n(), hd(x2).n(), hd(d2).n(), b1, b2, cd, cx, br);

            Self::field_admits_add_carry(
                tl(w1), tl(x1), tl(d1), nb1, false,
                tl(w2), tl(x2), tl(d2), nb2, false,
                ncd, ncx, nbr,
            );

            // Connect IH to full result
            Self::connect_induction(w1, x1, d1, w2, x2, d2, cx, cd, br,
                             nb1, nb2, ncd, ncx, nbr, d12h, x12h);
        }
    }

    /// Connection step: given IH on tails, derive field_admits on the full result.
    #[verifier::rlimit(500)]
    proof fn connect_induction(
        w1: nat, x1: nat, d1: nat, w2: nat, x2: nat, d2: nat,
        cx: Bit, cd: Bit, br: Bit,
        nb1: Bit, nb2: Bit, ncd: Bit, ncx: Bit, nbr: Bit,
        d12h: Bit, x12h: Bit,
    )
        requires
            !(w1 == 0 && x1 == 0 && d1 == 0 && w2 == 0 && x2 == 0 && d2 == 0),
            field_admits(tl(w1), tl(x1), tl(d1), nb1, false),
            field_admits(tl(w2), tl(x2), tl(d2), nb2, false),
            ncd.n() + nbr.n() <= ncx.n() + nb1.n() + nb2.n(),
            // IH result:
            field_admits(
                bw_and_not(bw_and(tl(w1), tl(w2)), lsh(Self::carry_out_c(tl(x1), tl(x2), ncx))),
                nat_add_carry(tl(x1), tl(x2), ncx),
                nat_add_carry(tl(d1), tl(d2), ncd),
                nbr, true),
            // Bit decomposition:
            hd(d1).full_add(hd(d2), cd) == (d12h, ncd),
            hd(x1).full_add(hd(x2), cx) == (x12h, ncx),
            ({let diff_r: int = x12h.n() as int - d12h.n() as int - br.n() as int;
              nbr == if diff_r < 0 { Bit::t() } else { Bit::f() }}),
        ensures
            field_admits(
                bw_and_not(bw_and(w1, w2), lsh(Self::carry_out_c(x1, x2, cx))),
                nat_add_carry(x1, x2, cx),
                nat_add_carry(d1, d2, cd),
                br, true)
    { reveal_with_fuel(field_admits, 1);
        let co = Self::carry_out_c(x1, x2, cx);
        let w = bw_and_not(bw_and(w1, w2), lsh(co));
        let w_tail = bw_and_not(bw_and(tl(w1), tl(w2)), lsh(Self::carry_out_c(tl(x1), tl(x2), ncx)));

        // tl(w) <= w_tail bitwise
        Self::tw_leq_wtail(w1, w2, x1, x2, cx, ncx, co, w, w_tail);

        // tl(w) = (tl(w1)&tl(w2)) & ~co
        Self::tw_eq(w1, w2, co, w);

        // Monotonicity: field_admits(w_tail,...,nbr,true) => field_admits(tl(w),...,nbr,true)
        Self::field_admits_mono(w_tail, tl(w),
            nat_add_carry(tl(x1), tl(x2), ncx), nat_add_carry(tl(d1), tl(d2), ncd), nbr, true);

        // nbr=T => tl(w)[0]=0
        assert(hd(co) == ncx) by {
            if !(x1 == 0 && x2 == 0) { hd_cons(Self::carry_out_c(tl(x1), tl(x2), ncx), ncx); }
        };
        Self::nbr_implies_no_leader(
            tl(w1), tl(x1), tl(d1), nb1,
            tl(w2), tl(x2), tl(d2), nb2,
            ncd, ncx, nbr, co, tl(w));

        // Convert first=true to first=false
        Self::field_admits_first_equiv(tl(w),
            nat_add_carry(tl(x1), tl(x2), ncx), nat_add_carry(tl(d1), tl(d2), ncd), nbr);

        // Now field_admits(w, nat_add_carry(x1,x2,cx), nat_add_carry(d1,d2,cd), br, true) unfolds:
        // first=true => leader check skipped
        // new borrow = nbr
        // tail = field_admits(tl(w), tl(nat_add_carry(x1,x2,cx)), tl(nat_add_carry(d1,d2,cd)), nbr, false) ✓
    }

    /// tl(w) <= w_tail bitwise
    proof fn tw_leq_wtail(
        w1: nat, w2: nat, x1: nat, x2: nat, cx: Bit, ncx: Bit,
        co: nat, w: nat, w_tail: nat,
    )
        requires
            co == Self::carry_out_c(x1, x2, cx),
            w == bw_and_not(bw_and(w1, w2), lsh(co)),
            w_tail == bw_and_not(bw_and(tl(w1), tl(w2)), lsh(Self::carry_out_c(tl(x1), tl(x2), ncx))),
            !(x1 == 0 && x2 == 0) ==> hd(x1).full_add(hd(x2), cx).1 == ncx,
        ensures forall|i: nat| #![auto] bit(tl(w), i).b() ==> bit(w_tail, i).b()
    {
        // tl(w) = (tl(w1)&tl(w2)) & ~co  (from tw_eq)
        // w_tail = (tl(w1)&tl(w2)) & ~lsh(carry_out_c(tl(x1),tl(x2),ncx))
        // co = carry_out_c(x1,x2,cx) = cons(carry_out_c(tl(x1),tl(x2),ncx), ncx)  [when x1,x2 not both 0]
        // tl(w)[i] = tl(w1)[i] & tl(w2)[i] & ~co[i]
        // w_tail[i] = tl(w1)[i] & tl(w2)[i] & ~lsh(carry_out_c(tl(x1),tl(x2),ncx))[i]
        // For i=0: co[0]=ncx, lsh(...)[0]=F. ~ncx <= ~F=T. ✓
        // For i>0: co[i]=carry_out_c(tl(x1),tl(x2),ncx)[i-1]=lsh(carry_out_c(tl(x1),tl(x2),ncx))[i]. Equal. ✓
        Self::tw_eq(w1, w2, co, w);
        let tw12 = bw_and(tl(w1), tl(w2));
        let co_tail = Self::carry_out_c(tl(x1), tl(x2), ncx);
        assert forall|i: nat| #![auto] bit(tl(w), i).b() ==> bit(w_tail, i).b() by {
            and_not_bit(tw12, co, i);
            and_not_bit(tw12, lsh(co_tail), i);
            and_bit(tl(w1), tl(w2), i);
            if i == 0 {
                hd_cons(co_tail, Bit::f());  // lsh(co_tail)[0] = F
                if !(x1 == 0 && x2 == 0) {
                    hd_cons(co_tail, ncx);  // co[0] = ncx
                }
                // ~ncx <= T = ~F. If tl(w)[0]=1: tw12[0]=1 and ~co[0]=1, so ~ncx=1, so ncx=F.
                // w_tail[0] = tw12[0] & ~F = tw12[0] = 1. ✓
            } else {
                bit_cons(co_tail, Bit::f(), i);  // lsh(co_tail)[i] = co_tail[i-1]
                if !(x1 == 0 && x2 == 0) {
                    bit_cons(co_tail, ncx, i);  // co[i] = co_tail[i-1]
                }
                // co[i] = co_tail[i-1] = lsh(co_tail)[i]. Equal.
            }
        };
    }

    /// tl(w) = (tl(w1)&tl(w2)) & ~co
    proof fn tw_eq(w1: nat, w2: nat, co: nat, w: nat)
        requires w == bw_and_not(bw_and(w1, w2), lsh(co))
        ensures tl(w) == bw_and_not(bw_and(tl(w1), tl(w2)), co)
    {
        assert forall|i: nat| #![auto]
            bit(tl(w), i) == bit(bw_and_not(bw_and(tl(w1), tl(w2)), co), i) by {
            bit_tl(w, i);
            mapd_hd_tl(w1, w2, |a: Bit, b: Bit| a.and(b));
            mapd_hd_tl(bw_and(w1, w2), lsh(co), |a: Bit, b: Bit| a.and_not(b));
            bit_cons(co, Bit::f(), i + 1);
            and_bit(tl(w1), tl(w2), i);
            and_not_bit(bw_and(tl(w1), tl(w2)), co, i);
            and_bit(w1, w2, i + 1);
            and_not_bit(bw_and(w1, w2), lsh(co), i + 1);
        };
        eq_from_bits(tl(w), bw_and_not(bw_and(tl(w1), tl(w2)), co));
    }

    /// If nbr=T, then tl(w)[0]=0.
    proof fn nbr_implies_no_leader(
        tw1: nat, tx1: nat, td1: nat, nb1: Bit,
        tw2: nat, tx2: nat, td2: nat, nb2: Bit,
        ncd: Bit, ncx: Bit, nbr: Bit, co: nat, tw: nat,
    )
        requires
            field_admits(tw1, tx1, td1, nb1, false),
            field_admits(tw2, tx2, td2, nb2, false),
            ncd.n() + nbr.n() <= ncx.n() + nb1.n() + nb2.n(),
            tw == bw_and_not(bw_and(tw1, tw2), co),
            hd(co) == ncx,
        ensures nbr.b() ==> !hd(tw).b()
    { reveal_with_fuel(field_admits, 1);
        if nbr.b() {
            and_not_bit(bw_and(tw1, tw2), co, 0);
            and_bit(tw1, tw2, 0);
            if ncx.b() {
                // co[0]=T => ~co[0]=F => tw[0]=0
            } else {
                assert(nb1.b() || nb2.b()) by { assert(ncd.n() + 1 <= nb1.n() + nb2.n()); };
                if nb1.b() {
                    if hd(tw1).b() { assert(field_admits(tw1, tx1, td1, nb1, false) == false); }
                } else {
                    if hd(tw2).b() { assert(field_admits(tw2, tx2, td2, nb2, false) == false); }
                }
            }
        }
    }

    /// field_admits(w,x,d,br,true) => field_admits(w,x,d,br,false) when br=F or hd(w)=F.
    proof fn field_admits_first_equiv(w: nat, x: nat, d: nat, br: Bit)
        requires field_admits(w, x, d, br, true), br.b() ==> !hd(w).b()
        ensures field_admits(w, x, d, br, false)
    { reveal_with_fuel(field_admits, 1); }

    /// Monotonicity: fewer boundaries => easier to satisfy.
    proof fn field_admits_mono(w: nat, wp: nat, x: nat, d: nat, br: Bit, first: bool)
        requires
            field_admits(w, x, d, br, first),
            forall|i: nat| #![auto] bit(wp, i).b() ==> bit(w, i).b(),
        ensures field_admits(wp, x, d, br, first)
        decreases w + x + d
    { reveal_with_fuel(field_admits, 1);
        if w == 0 && x == 0 && d == 0 {
            assert forall|i: nat| #![auto] bit(wp, i) == bit(0 as nat, i) by {
                bit_zero(i);
            };
            eq_from_bits(wp, 0);
        } else if w == 0 && x == 0 {
        } else {
            assert(hd(wp).b() ==> hd(w).b()) by { assert(bit(wp, 0).b() ==> bit(w, 0).b()); };
            assert(!(hd(wp).b() && !first && br.b())) by {
                if hd(wp).b() && !first && br.b() { assert(hd(w).b()); }
            };
            assert forall|i: nat| #![auto] bit(tl(wp), i).b() ==> bit(tl(w), i).b() by {
                bit_tl(wp, i); bit_tl(w, i);
            };
            let diff: int = hd(x).n() as int - hd(d).n() as int - br.n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            Self::field_admits_mono(tl(w), tl(wp), tl(x), tl(d), nb, false);
        }
    }

    proof fn inv_step(
        x1h: nat, d1h: nat, x2h: nat, d2h: nat,
        b1: Bit, b2: Bit, cd: Bit, cx: Bit, br: Bit,
    )
        requires x1h <= 1, d1h <= 1, x2h <= 1, d2h <= 1,
                 cd.n() + br.n() <= cx.n() + b1.n() + b2.n(),
        ensures ({
            let nb1 = if (x1h as int - d1h as int - b1.n() as int) < 0 { Bit::t() } else { Bit::f() };
            let nb2 = if (x2h as int - d2h as int - b2.n() as int) < 0 { Bit::t() } else { Bit::f() };
            let d12 = d1h + d2h + cd.n(); let ncd = if d12 >= 2 { Bit::t() } else { Bit::f() };
            let x12 = x1h + x2h + cx.n(); let ncx = if x12 >= 2 { Bit::t() } else { Bit::f() };
            let x12b = if x12 % 2 == 1 { Bit::t() } else { Bit::f() };
            let d12b = if d12 % 2 == 1 { Bit::t() } else { Bit::f() };
            let nbr = if (x12b.n() as int - d12b.n() as int - br.n() as int) < 0 { Bit::t() } else { Bit::f() };
            ncd.n() + nbr.n() <= ncx.n() + nb1.n() + nb2.n()
        })
    {
        assert(b1 == Bit::t() || b1 == Bit::f()); assert(b2 == Bit::t() || b2 == Bit::f());
        assert(cd == Bit::t() || cd == Bit::f()); assert(cx == Bit::t() || cx == Bit::f());
        assert(br == Bit::t() || br == Bit::f());
    }

    proof fn field_admits_leq(x: nat, d: nat, borrow: Bit, first: bool)
        requires field_admits(0, x, d, borrow, first)
        ensures d + borrow.n() <= x
        decreases x + d
    { reveal_with_fuel(field_admits, 1);
        if x == 0 && d == 0 {} else {
            let diff: int = hd(x).n() as int - hd(d).n() as int - borrow.n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            Self::field_admits_leq(tl(x), tl(d), nb, false);
            hd_tl(x); hd_tl(d);
        }
    }

    /// field_admits(w, x, d, F, true) implies d <= x, for any w.
    /// Proof: at each bit, the borrow-tracking subtraction x - d never underflows
    /// across field boundaries, so d <= x as naturals.
    pub proof fn offset_bounded(w: nat, x: nat, d: nat)
        requires field_admits(w, x, d, Bit::f(), true)
        ensures d <= x
        decreases w + x + d
    { reveal_with_fuel(field_admits, 1);
        if w == 0 && x == 0 && d == 0 {
        } else {
            // hd(w) is a leader (first=true so no borrow check at bit 0)
            let diff: int = hd(x).n() as int - hd(d).n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            // Recurse on tails with first=false
            // We need: d <= x, i.e. hd(d) + 2*tl(d) <= hd(x) + 2*tl(x)
            // Case hd(d) <= hd(x): nb = F, recurse gives tl(d) <= tl(x)
            // Case hd(d) > hd(x): nb = T (borrow), but then at next leader bit
            //   field_admits checks borrow=T => false. So this can only happen in
            //   a follower region. But field_admits_leq handles w=0 case.
            // For general w: use field_admits_leq on the whole thing via w=0 monotonicity.
            // Since field_admits(w,x,d,F,true) and w has fewer boundaries than all-ones,
            // we can't directly use field_admits_leq. Instead prove by induction.
            //
            // Key: field_admits(w,x,d,F,true) => field_admits(0,x,d,F,true) by field_admits_mono
            // (fewer boundaries = easier to satisfy, so w=0 is harder... wait, w=0 means
            // NO leader bits, so the borrow check never fires. That's EASIER, not harder.)
            // Actually field_admits_mono says: fewer boundaries in wp => easier.
            // w=0 has NO boundaries, so it's the easiest. field_admits(w,...) with more
            // boundaries is HARDER. So field_admits(w,x,d,F,true) does NOT imply field_admits(0,...).
            //
            // Correct approach: induction mirroring field_admits_leq but for general w.
            if w == 0 && x == 0 {
                // d > 0 but w=0,x=0 => field_admits = false, contradicts requires
            } else {
                // first=true: skip leader check at bit 0
                // nb = borrow after processing bit 0
                Self::offset_bounded_carry(tl(w), tl(x), tl(d), nb);
                hd_tl(x); hd_tl(d);
                // hd(x).n() + 2*tl(x) = x, hd(d).n() + 2*tl(d) = d
                // nb=F: hd(d) <= hd(x), tl(d) <= tl(x) => d <= x ✓
                // nb=T: hd(d) > hd(x) (i.e. hd(d)=1, hd(x)=0), tl(d) + 1 <= tl(x)
                //   => d = 1 + 2*tl(d) <= 1 + 2*(tl(x)-1) = 2*tl(x)-1 < 2*tl(x) <= x ✓
                //   (since hd(x)=0 => x = 2*tl(x))
                assert(hd(x).n() <= 1 && hd(d).n() <= 1);
            }
        }
    }

    /// Generalized: field_admits with arbitrary borrow, first=false.
    proof fn offset_bounded_carry(w: nat, x: nat, d: nat, borrow: Bit)
        requires field_admits(w, x, d, borrow, false)
        ensures d + borrow.n() <= x
        decreases w + x + d
    { reveal_with_fuel(field_admits, 1);
        if w == 0 && x == 0 && d == 0 {
        } else if w == 0 && x == 0 {
            // field_admits = false, contradiction
        } else {
            // If hd(w)=1 (leader) and borrow=T: field_admits = false, contradiction
            if hd(w).b() && borrow.b() { return; }
            let diff: int = hd(x).n() as int - hd(d).n() as int - borrow.n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            Self::offset_bounded_carry(tl(w), tl(x), tl(d), nb);
            hd_tl(x); hd_tl(d);
            assert(hd(x).n() <= 1 && hd(d).n() <= 1 && borrow.n() <= 1);
        }
    }

    /// Multiplication: bilinear expansion.
    /// result = (v1*v2, w=0, x = v1*x2 + v2*x1 + x1*x2)
    /// (w=0 means single field spanning all bits)
    pub open spec fn mul(self, other: Unum) -> Unum {
        Unum {
            base: prod(self.base, other.base),
            walls: 0,
            extent: prod(self.base, other.extent) + prod(other.base, self.extent) + prod(self.extent, other.extent),
        }
    }

    /// Soundness of Unum multiplication.
    pub proof fn mul_sound(self, other: Unum)
        ensures forall|c1: nat, c2: nat| #![auto]
            self.has(c1) && other.has(c2) ==> self.mul(other).has(prod(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto]
            self.has(c1) && other.has(c2) implies self.mul(other).has(prod(c1, c2)) by {
            if self.has(c1) && other.has(c2) {
                let d1 = nat_sub(c1, self.base);
                let d2 = nat_sub(c2, other.base);
                // d1 <= x1, d2 <= x2
                Self::offset_bounded(self.walls, self.extent, d1);
                Self::offset_bounded(other.walls, other.extent, d2);
                // c1*c2 = (v1+d1)*(v2+d2) = v1*v2 + v1*d2 + v2*d1 + d1*d2
                let v1 = self.base; let x1 = self.extent;
                let v2 = other.base; let x2 = other.extent;
                assert(c1 == v1 + d1 && c2 == v2 + d2);
                assert(prod(c1, c2) == v1*v2 + v1*d2 + v2*d1 + d1*d2) by {
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(c1 as int, v2 as int, d2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(v2 as int, v1 as int, d1 as int);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(d2 as int, v1 as int, d1 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(c1 as int, v2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(c1 as int, d2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(v1 as int, v2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(v1 as int, d2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(d1 as int, v2 as int);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(d1 as int, d2 as int);
                };
                // uncertainty = prod(c1,c2) - v1*v2 = v1*d2 + v2*d1 + d1*d2
                let unc = v1*d2 + v2*d1 + d1*d2;
                // unc <= v1*x2 + v2*x1 + x1*x2 since d1<=x1, d2<=x2
                assert(unc <= v1*x2 + v2*x1 + x1*x2) by {
                    vstd::arithmetic::mul::lemma_mul_upper_bound(d2 as int, x2 as int, v1 as int, v1 as int);
                    vstd::arithmetic::mul::lemma_mul_upper_bound(d1 as int, x1 as int, v2 as int, v2 as int);
                    vstd::arithmetic::mul::lemma_mul_upper_bound(d1 as int, x1 as int, d2 as int, x2 as int);
                };
                // result.has(c1*c2): c1*c2 >= v1*v2 and field_admits(0, x_total, unc, F, true)
                let x_total = v1*x2 + v2*x1 + x1*x2;
                assert(prod(c1, c2) >= prod(v1, v2));
                assert(nat_sub(prod(c1, c2), prod(v1, v2)) == unc);
                // field_admits(0, x_total, unc, F, true) iff unc <= x_total (by field_admits_leq)
                Self::offset_from_bound(x_total, unc);
            }
        }
    }

    /// field_admits(0, x, d, F, true) iff d <= x.
    proof fn field_admits_no_walls_iff(x: nat, d: nat)
        ensures field_admits(0, x, d, Bit::f(), true) <==> d <= x
    {
        if field_admits(0, x, d, Bit::f(), true) {
            Self::field_admits_leq(x, d, Bit::f(), true);
        }
        if d <= x {
            Self::offset_from_bound(x, d);
        }
    }

    /// Converse of field_admits_leq: d <= x implies field_admits(0, x, d, F, true).
    pub proof fn offset_from_bound(x: nat, d: nat)
        requires d <= x
        ensures field_admits(0, x, d, Bit::f(), true)
        decreases x + d
    { reveal_with_fuel(field_admits, 1);
        if x == 0 && d == 0 {
        } else {
            let diff: int = hd(x).n() as int - hd(d).n() as int;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            hd_tl(x); hd_tl(d);
            assert(x == hd(x).n() + 2*tl(x) && d == hd(d).n() + 2*tl(d));
            assert(hd(x).n() <= 1 && hd(d).n() <= 1);
            assert(hd(x) == Bit::t() || hd(x) == Bit::f());
            assert(hd(d) == Bit::t() || hd(d) == Bit::f());
            if nb.b() {
                assert(hd(d) == Bit::t() && hd(x) == Bit::f());
                assert(tl(d) + 1 <= tl(x));
                Self::offset_from_bound_borrow(tl(x), tl(d));
                // Now: field_admits(0, tl(x), tl(d), T, false)
                // Need: field_admits(0, x, d, F, true)
                // Unfold: w=0, x>0 or d>0, hd(w)=F so no leader check,
                //   diff = hd(x).n() - hd(d).n() - 0 < 0 (since hd(d)=1, hd(x)=0)
                //   nb = T, recurse field_admits(tl(0)=0, tl(x), tl(d), T, false) ✓
                assert(field_admits(0 as nat, x, d, Bit::f(), true)) by {
                    assert(tl(0 as nat) == 0 as nat);
                };
            } else {
                assert(tl(d) <= tl(x));
                Self::offset_from_bound(tl(x), tl(d));
                // field_admits(0, tl(x), tl(d), F, true) is in context.
                // field_admits(0, x, d, F, true) unfolds to field_admits(0, tl(x), tl(d), F, false).
                // Since br=F, first=true and first=false are equivalent (no leader check fires).
                assert(field_admits(0 as nat, tl(x), tl(d), Bit::f(), false)) by {
                    // field_admits(0,tl(x),tl(d),F,true): leader check is hd(w)&&!first&&br.b()
                    // = F && !true && F = false, so it's skipped. Same for first=false.
                };
                assert(field_admits(0 as nat, x, d, Bit::f(), true)) by {
                    assert(tl(0 as nat) == 0 as nat);
                };
            }
        }
    }

    /// With borrow=T: d + 1 <= x implies field_admits(0, x, d, T, false).
    proof fn offset_from_bound_borrow(x: nat, d: nat)
        requires d + 1 <= x
        ensures field_admits(0, x, d, Bit::t(), false)
        decreases x + d
    { reveal_with_fuel(field_admits, 1);
        if x == 0 && d == 0 {
            assert(false); // unreachable: d+1<=x => 1<=0
        } else {
            let diff: int = hd(x).n() as int - hd(d).n() as int - 1;
            let nb = if diff < 0 { Bit::t() } else { Bit::f() };
            hd_tl(x); hd_tl(d);
            assert(x == hd(x).n() + 2*tl(x) && d == hd(d).n() + 2*tl(d));
            assert(hd(x).n() <= 1 && hd(d).n() <= 1);
            assert(hd(x) == Bit::t() || hd(x) == Bit::f());
            assert(hd(d) == Bit::t() || hd(d) == Bit::f());
            if nb.b() {
                assert(tl(d) + 1 <= tl(x));
                Self::offset_from_bound_borrow(tl(x), tl(d));
                assert(field_admits(0 as nat, x, d, Bit::t(), false)) by {
                    assert(tl(0 as nat) == 0 as nat);
                };
            } else {
                assert(hd(x) == Bit::t() && hd(d) == Bit::f());
                assert(tl(d) <= tl(x));
                Self::offset_from_bound(tl(x), tl(d));
                // field_admits(0, tl(x), tl(d), F, true) is in context.
                // field_admits(0, x, d, T, false) unfolds to field_admits(0, tl(x), tl(d), F, false).
                // Since br=F, first=true and first=false are equivalent.
                assert(field_admits(0 as nat, tl(x), tl(d), Bit::f(), false));
                assert(field_admits(0 as nat, x, d, Bit::t(), false)) by {
                    assert(tl(0 as nat) == 0 as nat);
                };
            }
        }
    }

    pub open spec fn to_anum(self) -> Anum { Anum { base: self.base, span: all_ones(len(self.extent)) } }

    /// Chop a Unum to w bits: chop all three fields.
    pub open spec fn truncate(self, w: nat) -> Unum {
        Unum { base: chop(self.base, w), walls: chop(self.walls, w), extent: chop(self.extent, w) }
    }

    /// If Un.has(n) and n, v, x all fit in w bits, then truncate.has(n).
    /// (chop is identity on fitted values, so truncate == self and chop(n,w) == n)
    pub proof fn chop_sound(self, n: nat, w: nat)
        requires self.has(n), fits(n, w), fits(self.base, w), fits(self.extent, w)
        ensures self.truncate(w).has(n)
    {
        // self.has(n): n >= v && field_admits(w_field, x, n-v, F, true)
        let d = nat_sub(n, self.base);
        Self::offset_bounded(self.walls, self.extent, d);
        // d <= x, x fits in w bits, so d fits in w bits
        chop_idem(d, w); chop_idem(n, w); chop_idem(self.base, w); chop_idem(self.extent, w);
        // truncate(w).has(n) requires:
        //   n >= chop(v, w) = v  ✓
        //   field_admits(chop(w_field,w), chop(x,w), nat_sub(n, chop(v,w)), F, true)
        //   = field_admits(chop(w_field,w), x, d, F, true)
        // Since chop(w_field,w) has fewer or equal bits set than w_field
        // (chop zeros out bits >= w), field_admits_mono gives:
        //   field_admits(w_field, x, d, F, true) ==> field_admits(chop(w_field,w), x, d, F, true)
        // because fewer boundaries = easier to satisfy.
        assert forall|i: nat| #![auto] bit(chop(self.walls, w), i).b() ==> bit(self.walls, i).b() by {
            chop_bit(self.walls, w, i);
        };
        Self::field_admits_mono(self.walls, chop(self.walls, w), self.extent, d, Bit::f(), true);
        assert(nat_sub(n, chop(self.base, w)) == d);
    }

    /// Bounded plus soundness: when the concrete sum doesn't overflow w bits,
    /// the chopped result contains the sum.
    ///
    /// Precondition: nat_add(c1,c2) < exp(w)  (no overflow on concrete sum)
    /// This is the same limitation as Anum: the base+offset representation
    /// cannot track values that wrap below the base.
    pub proof fn add_bounded_sound(self, other: Unum, c1: nat, c2: nat, w: nat)
        requires
            self.has(c1), other.has(c2),
            fits(self.base, w), fits(self.extent, w),
            fits(other.base, w), fits(other.extent, w),
            fits(nat_add(self.extent, other.extent), w),
            nat_add(c1, c2) < exp(w),
            fits(nat_add(self.base, other.base), w),  // v1+v2 fits (no base overflow)
        ensures self.add(other).truncate(w).has(nat_add(c1, c2))
    {
        // Direct call to field_admits_add which is the core of add_sound
        assert(c1 >= self.base && c2 >= other.base);  // from has(c1), has(c2)
        let d1 = nat_sub(c1, self.base); let d2 = nat_sub(c2, other.base);
        Self::field_admits_add(self.walls, self.extent, d1, other.walls, other.extent, d2);
        nat_add_correct(c1, c2); nat_add_correct(self.base, other.base); nat_add_correct(d1, d2);
        let result = self.add(other);
        assert(result.has(nat_add(c1, c2)));
        // nat_add(c1,c2) fits in w bits
        chop_idem(nat_add(c1, c2), w);
        // result.extent = nat_add(x1,x2) fits; result.walls fits (bitwise op on fitted values)
        chop_idem(result.extent, w); chop_idem(result.walls, w);
        // d = nat_add(c1,c2) - nat_add(v1,v2) fits in w bits (d <= result.extent which fits)
        let d1 = nat_sub(c1, self.base); let d2 = nat_sub(c2, other.base);
        Self::offset_bounded(self.walls, self.extent, d1);
        Self::offset_bounded(other.walls, other.extent, d2);
        nat_add_correct(d1, d2); nat_add_correct(c1, c2); nat_add_correct(self.base, other.base);
        assert(nat_add(c1, c2) >= nat_add(self.base, other.base));
        let d = nat_sub(nat_add(c1, c2), nat_add(self.base, other.base));
        assert(d == nat_add(d1, d2));
        assert(d <= nat_add(self.extent, other.extent)) by { nat_add_correct(d1, d2); nat_add_correct(self.extent, other.extent); };
        chop_idem(d, w);
        // Both nat_add(c1,c2) and nat_add(v1,v2) fit => chop is identity => minus is valid
        assert(nat_add(c1, c2) >= nat_add(self.base, other.base)) by { nat_add_correct(c1, c2); nat_add_correct(self.base, other.base); };
        assert(chop(nat_add(c1, c2), w) == nat_add(c1, c2)) by {
            chop_is_mod(nat_add(c1, c2), w); exp_pos(w);
            vstd::arithmetic::div_mod::lemma_small_mod(nat_add(c1, c2), exp(w));
        };
        assert(chop(nat_add(self.base, other.base), w) == nat_add(self.base, other.base)) by {
            chop_is_mod(nat_add(self.base, other.base), w); exp_pos(w);
            vstd::arithmetic::div_mod::lemma_small_mod(nat_add(self.base, other.base), exp(w));
        };
        assert(nat_sub(chop(nat_add(c1, c2), w), chop(nat_add(self.base, other.base), w)) == d) by {
            nat_add_correct(self.base, other.base); nat_add_correct(c1, c2);
        };
        // truncate(result) == Un{chop(result.base,w), chop(result.walls,w), chop(result.extent,w)}
        // result.has(nat_add(c1,c2)) and d fits => truncate(result).has(nat_add(c1,c2))
        // because field_admits(chop(result.walls,w), chop(result.extent,w), d, F, true)
        //       = field_admits(result.walls, result.extent, d, F, true)  [since result.walls and result.extent fit]
        // which holds from result.has(nat_add(c1,c2))
        assert(fits(result.base, w) || true);  // result.base may not fit, but chop handles it
        // The key: result.has(nat_add(c1,c2)) means field_admits(result.walls, result.extent, d, F, true)
        // truncate(result).has(nat_add(c1,c2)) means:
        //   nat_add(c1,c2) >= chop(result.base, w)  [need: chop(nat_add(c1,c2),w) >= chop(result.base,w)]
        //   field_admits(chop(result.walls,w), chop(result.extent,w), nat_sub(nat_add(c1,c2), chop(result.base,w)), F, true)
        // Since result.walls and result.extent fit: chop(result.walls,w)=result.walls, chop(result.extent,w)=result.extent
        // nat_sub(nat_add(c1,c2), chop(result.base,w)) = d  [proved above]
        // field_admits(result.walls, result.extent, d, F, true)  ✓ from result.has(nat_add(c1,c2))
        // nat_add(c1,c2) >= chop(result.base,w): chop(result.base,w) = chop(nat_add(v1,v2),w)
        //   nat_add(c1,c2) = nat_add(v1,v2) + d >= nat_add(v1,v2) >= chop(nat_add(v1,v2),w)  ✓
        assert(nat_add(c1, c2) >= chop(nat_add(self.base, other.base), w)) by {
            nat_add_correct(self.base, other.base); nat_add_correct(c1, c2);
        };
        // Final assembly: truncate(result).has(nat_add(c1,c2))
        // chop(result.walls, w) has fewer bits than result.walls (chop zeros high bits)
        // field_admits_mono: fewer boundaries => easier to satisfy
        assert forall|i: nat| #![auto] bit(chop(result.walls, w), i).b() ==> bit(result.walls, i).b() by {
            chop_bit(result.walls, w, i);
        };
        Self::field_admits_mono(result.walls, chop(result.walls, w), result.extent, d, Bit::f(), true);
        // Now: field_admits(chop(result.walls,w), result.extent, d, F, true)
        // And: chop(result.extent, w) = result.extent (fits)
        // And: nat_sub(nat_add(c1,c2), chop(result.base,w)) = d
        // So: truncate(result).has(nat_add(c1,c2)) ✓
        assert(result.truncate(w).has(nat_add(c1, c2)));
    }

    /// Bounded mul soundness: when the concrete product doesn't overflow w bits.
    pub proof fn mul_bounded_sound(self, other: Unum, c1: nat, c2: nat, w: nat)
        requires
            self.has(c1), other.has(c2),
            fits(self.base, w), fits(self.extent, w),
            fits(other.base, w), fits(other.extent, w),
            fits(prod(self.base, other.base), w),
            fits(prod(self.base, other.extent) + prod(other.base, self.extent) + prod(self.extent, other.extent), w),
            prod(c1, c2) < exp(w),
        ensures self.mul(other).truncate(w).has(prod(c1, c2))
    {
        self.mul_sound(other);
        let result = self.mul(other);
        assert(result.has(prod(c1, c2)));
        // prod(c1,c2) fits
        chop_idem(prod(c1, c2), w);
        // result.extent = v1*x2+v2*x1+x1*x2 fits; result.walls = 0 fits
        chop_idem(result.extent, w); chop_idem(result.walls, w);
        // d = prod(c1,c2) - prod(v1,v2)
        let d1 = nat_sub(c1, self.base); let d2 = nat_sub(c2, other.base);
        assert(c1 >= self.base && c2 >= other.base);
        Self::offset_bounded(self.walls, self.extent, d1);
        Self::offset_bounded(other.walls, other.extent, d2);
        assert(prod(c1, c2) >= prod(self.base, other.base)) by {
            vstd::arithmetic::mul::lemma_mul_inequality(self.base as int, c1 as int, c2 as int);
            vstd::arithmetic::mul::lemma_mul_inequality(other.base as int, c2 as int, self.base as int);
        };
        let d = nat_sub(prod(c1, c2), prod(self.base, other.base));
        assert(chop(prod(c1, c2), w) == prod(c1, c2)) by {
            chop_is_mod(prod(c1, c2), w); exp_pos(w);
            vstd::arithmetic::div_mod::lemma_small_mod(prod(c1, c2), exp(w));
        };
        assert(chop(prod(self.base, other.base), w) == prod(self.base, other.base)) by {
            chop_is_mod(prod(self.base, other.base), w); exp_pos(w);
            vstd::arithmetic::div_mod::lemma_small_mod(prod(self.base, other.base), exp(w));
        };
        assert(nat_sub(chop(prod(c1, c2), w), chop(prod(self.base, other.base), w)) == d);
        // field_admits_mono: chop(result.walls,w) has fewer bits than result.walls
        assert forall|i: nat| #![auto] bit(chop(result.walls, w), i).b() ==> bit(result.walls, i).b() by {
            chop_bit(result.walls, w, i);
        };
        Self::field_admits_mono(result.walls, chop(result.walls, w), result.extent, d, Bit::f(), true);
        assert(prod(c1, c2) >= chop(prod(self.base, other.base), w));
        assert(result.truncate(w).has(prod(c1, c2)));
    }

    pub proof fn to_anum_sound(self)
        requires self.walls == 0
        ensures forall|n: nat| #![auto] self.has(n) ==> self.to_anum().has(n)
    {
        assert forall|n: nat| #![auto] self.has(n) implies self.to_anum().has(n) by {
            if self.has(n) {
                Self::field_admits_leq(self.extent, nat_sub(n, self.base), Bit::f(), true);
                len_bound(self.extent);
                all_ones_has(nat_sub(n, self.base), len(self.extent));
                Tnum::ctor(0, all_ones(len(self.extent))).has_equiv(nat_sub(n, self.base));
            }
        };
    }
}

pub proof fn carry_out_c_overflow(a: nat, b: nat, i: nat)
    ensures bit(Unum::carry_out(a, b), i).b() <==> chop(a, i+1) + chop(b, i+1) >= exp(i+1)
{ carry_out_c_overflow_carry(a, b, Bit::f(), i); }

proof fn carry_out_c_overflow_carry(a: nat, b: nat, c: Bit, i: nat)
    ensures bit(Unum::carry_out_c(a, b, c), i).b() <==> chop(a, i+1) + chop(b, i+1) + c.n() >= exp(i+1)
    decreases i, a + b
{
    if a == 0 && b == 0 { bit_zero(i); chop_zero(i+1); exp_pos(i+1); }
    else {
        let (r0, c1) = hd(a).full_add(hd(b), c);
        hd(a).full_add_correct(hd(b), c);
        hd_cons(Unum::carry_out_c(tl(a), tl(b), c1), c1);
        if i == 0 {
            chop_is_mod(a, 1); chop_is_mod(b, 1); hd_tl(a); hd_tl(b);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, 2);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b as int, 2);
        } else {
            bit_cons(Unum::carry_out_c(tl(a), tl(b), c1), c1, i);
            carry_out_c_overflow_carry(tl(a), tl(b), c1, (i-1) as nat);
            chop_is_mod(a, i+1); chop_is_mod(b, i+1);
            chop_is_mod(tl(a), i); chop_is_mod(tl(b), i);
            hd_tl(a); hd_tl(b); exp_pos(i);
            assert(a % exp(i+1) == hd(a).n() + 2*(tl(a) % exp(i))) by { mod_decompose(a, i); };
            assert(b % exp(i+1) == hd(b).n() + 2*(tl(b) % exp(i))) by { mod_decompose(b, i); };
            assert(hd(a).n() + hd(b).n() + c.n() == 2*c1.n() + r0.n());
            assert((hd(a).n()+hd(b).n()+c.n()+2*(tl(a)%exp(i)+tl(b)%exp(i)) >= 2*exp(i))
                <==> (c1.n()+tl(a)%exp(i)+tl(b)%exp(i) >= exp(i))) by { assert(r0.n() <= 1); };
        }
    }
}

proof fn mod_decompose(a: nat, i: nat)
    ensures a % exp(i+1) == hd(a).n() + 2*(tl(a) % exp(i))
{ hd_cons(chop(tl(a), i), hd(a)); chop_is_mod(a, i+1); chop_is_mod(tl(a), i); }

proof fn chop_zero(k: nat) ensures chop(0, k) == 0 decreases k
{ if k > 0 { chop_zero((k-1) as nat); } }

proof fn exp_pos(k: nat) ensures exp(k) > 0 decreases k
{ if k > 0 { exp_pos((k-1) as nat); } }

} // verus!
