// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Unsigned intervals over machine words, generic over the width.
//!
//! This is the reference port of a machine domain onto the shared traits:
//! bottomless (`lo <= hi` always, empty results are `BotOr::Bot`), canonical
//! (the bounds are the least and greatest members), private fields so that only
//! well-formed values exist, and one instance per width serving both unsigned
//! and signed semantics.
// Proof-only bindings and lemma imports are erased outside Verus.
#![allow(unused_imports, unused_variables)]
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// `{x | lo <= x <= hi}` in the unsigned reading.
pub struct Interval<W> {
    lo: W,
    hi: W,
}

/// `from_int` is the identity on in-range integers.
proof fn lemma_from_small<W: Word>(i: int)
    requires
        0 <= i < W::modulus(),
    ensures
        W::from_int(i).view() == i,
{
    W::lemma_from_int(i);
    lemma_small_mod(i as nat, W::modulus());
}

/// `from_int` subtracts the modulus once on `[M, 2M)`.
proof fn lemma_from_over<W: Word>(i: int)
    requires
        W::modulus() <= i < 2 * W::modulus(),
    ensures
        W::from_int(i).view() == i - W::modulus(),
{
    W::lemma_from_int(i);
    lemma_mod_sub_multiples_vanish(i, W::modulus() as int);
    lemma_small_mod((i - W::modulus()) as nat, W::modulus());
}

/// `from_int` adds the modulus once on `[-M, 0)`.
proof fn lemma_from_under<W: Word>(i: int)
    requires
        -(W::modulus() as int) <= i < 0,
    ensures
        W::from_int(i).view() == i + W::modulus(),
{
    W::lemma_from_int(i);
    lemma_mod_add_multiples_vanish(i, W::modulus() as int);
    lemma_small_mod((i + W::modulus()) as nat, W::modulus());
}

/// 2^a <= 2^b for a <= b.
proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        0 < pow2(a) <= pow2(b),
{
    lemma_pow2_pos(a);
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// Right shift is monotone in the operand and antitone in the amount.
proof fn lemma_shr_bounds(lo: nat, x: nat, hi: nat, a: nat, s: nat, b: nat)
    requires
        lo <= x <= hi,
        a <= s <= b,
    ensures
        lo / pow2(b) <= x / pow2(s) <= hi / pow2(a),
        x / pow2(s) <= x,
{
    lemma_pow2_le(a, s);
    lemma_pow2_le(s, b);
    lemma_pow2_le(0, a);
    lemma2_to64();
    lemma_div_is_ordered(lo as int, x as int, pow2(b) as int);
    lemma_div_is_ordered_by_denominator(x as int, pow2(s) as int, pow2(b) as int);
    lemma_div_is_ordered_by_denominator(x as int, pow2(a) as int, pow2(s) as int);
    lemma_div_is_ordered(x as int, hi as int, pow2(a) as int);
    lemma_div_is_ordered_by_denominator(x as int, 1, pow2(s) as int);
}

/// Left shift is monotone in the operand and in the amount.
proof fn lemma_shl_bounds(lo: nat, x: nat, hi: nat, a: nat, s: nat, b: nat)
    requires
        lo <= x <= hi,
        a <= s <= b,
    ensures
        lo * pow2(a) <= x * pow2(s) <= hi * pow2(b),
{
    lemma_pow2_le(a, s);
    lemma_pow2_le(s, b);
    lemma_mul_upper_bound(lo as int, x as int, pow2(a) as int, pow2(s) as int);
    lemma_mul_upper_bound(x as int, hi as int, pow2(s) as int, pow2(b) as int);
}

proof fn lemma_from_zero<W: Word>()
    ensures
        W::from_int(0).view() == 0,
{
    W::lemma_modulus();
    lemma_from_small::<W>(0);
}

impl<W: Word> Interval<W> {
    pub closed spec fn lo(&self) -> W {
        self.lo
    }

    pub closed spec fn hi(&self) -> W {
        self.hi
    }

    pub fn new(lo: W, hi: W) -> (r: Option<Self>)
        ensures
            match r {
                Some(i) => i.wf() && i.lo() == lo && i.hi() == hi,
                None => lo.view() > hi.view(),
            },
    {
        if lo.le(hi) {
            Some(Interval { lo, hi })
        } else {
            None
        }
    }

    pub fn constant(c: W) -> (r: Self)
        ensures
            r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> x == c,
    {
        proof {
            assert forall|x: W| #[trigger] (Interval { lo: c, hi: c }).gamma(x) <==> x == c by {
                W::lemma_view_injective(x, c);
            }
        }
        Interval { lo: c, hi: c }
    }

    /// The intersection, exactly: an interval meet loses nothing.
    pub fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: W| #[trigger] r.gamma(c) == (self.gamma(c) && o.gamma(c)),
    {
        let lo = if self.lo.le(o.lo) {
            o.lo
        } else {
            self.lo
        };
        let hi = if self.hi.le(o.hi) {
            self.hi
        } else {
            o.hi
        };
        if lo.le(hi) {
            BotOr::Val(Interval { lo, hi })
        } else {
            BotOr::Bot
        }
    }

    /// The in-range shift amounts of `k` lie in `[r.0, r.1]`, or there are none.
    fn shift_range(k: &Self) -> (r: Option<(u32, u32)>)
        requires
            k.wf(),
        ensures
            match r {
                Some((a, b)) => a <= b && (b as nat) < W::bits() && forall|s: W|
                    #[trigger] k.gamma(s) && s.view() < W::bits() ==> a as nat <= s.view() <= b as nat,
                None => forall|s: W| #[trigger] k.gamma(s) ==> s.view() >= W::bits(),
            },
    {
        let a = k.lo.to_shift()?;
        proof {
            W::lemma_modulus();
        }
        let b = match k.hi.to_shift() {
            Some(b) => b,
            None => W::bit_width() - 1,
        };
        Some((a, b))
    }

    pub fn bounds(&self) -> (r: (W, W))
        ensures
            r.0 == self.lo(),
            r.1 == self.hi(),
    {
        (self.lo, self.hi)
    }
}

impl<W: Word> Domain for Interval<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        self.lo().view() <= self.hi().view()
    }

    open spec fn gamma(&self, c: W) -> bool {
        self.lo().view() <= c.view() <= self.hi().view()
    }

    fn dup(&self) -> (r: Self) {
        Interval { lo: self.lo, hi: self.hi }
    }

    fn top() -> (r: Self) {
        let r = Interval { lo: W::zero(), hi: W::max() };
        proof {
            assert forall|c: W| #[trigger] r.gamma(c) by {
                c.lemma_view_bounded();
            }
        }
        r
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        o.lo.le(self.lo) && self.hi.le(o.hi)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        let lo = if self.lo.le(o.lo) {
            self.lo
        } else {
            o.lo
        };
        let hi = if self.hi.le(o.hi) {
            o.hi
        } else {
            self.hi
        };
        Interval { lo, hi }
    }

    // Duplicates `meet_exact`: calling it from here would make the impl
    // depend on a function whose contract mentions the impl (a Verus cycle).
    fn meet(&self, o: &Self) -> (r: BotOr<Self>)
    {
        let lo = if self.lo.le(o.lo) {
            o.lo
        } else {
            self.lo
        };
        let hi = if self.hi.le(o.hi) {
            self.hi
        } else {
            o.hi
        };
        if lo.le(hi) {
            BotOr::Val(Interval { lo, hi })
        } else {
            BotOr::Bot
        }
    }

    /// Cousot-Cousot widening: an unstable bound jumps to the end of the range.
    fn widen(&self, o: &Self) -> (r: Self) {
        let lo = if self.lo.le(o.lo) {
            self.lo
        } else {
            W::zero()
        };
        let hi = if o.hi.le(self.hi) {
            self.hi
        } else {
            W::max()
        };
        let r = Interval { lo, hi };
        proof {
            self.lo.lemma_view_bounded();
            assert forall|c: W| self.gamma(c) || o.gamma(c) implies #[trigger] r.gamma(c) by {
                c.lemma_view_bounded();
            }
        }
        r
    }
}

impl<W: Word> Canonical for Interval<W> {
    proof fn lemma_nonempty(&self) {
        assert(self.gamma(self.lo));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert(a.gamma(a.lo) && a.gamma(a.hi) && a.gamma(b.lo) && a.gamma(b.hi));
        W::lemma_view_injective(a.lo, b.lo);
        W::lemma_view_injective(a.hi, b.hi);
    }
}

impl<W: Word> Arith<Unsigned<W>> for Interval<W> {
    /// Exact when no sum wraps or every sum wraps once; top otherwise.
    fn add(&self, o: &Self) -> (r: Self) {
        match self.hi.checked_add(o.hi) {
            Some(hi) => {
                let lo = match self.lo.checked_add(o.lo) {
                    Some(lo) => lo,
                    None => { return Self::top(); },  // unreachable: lo <= hi
                };
                let r = Interval { lo, hi };
                proof {
                    hi.lemma_view_bounded();
                    assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                        Unsigned::<W>::add(x, y),
                    ) by {
                        lemma_from_small::<W>(x.view() as int + y.view() as int);
                    }
                }
                r
            },
            None => {
                if self.lo.checked_add(o.lo).is_none() {
                    // every sum lies in [M, 2M): subtract M from both bounds
                    let r = Interval { lo: self.lo.wrapping_add(o.lo), hi: self.hi.wrapping_add(o.hi) };
                    proof {
                        self.hi.lemma_view_bounded();
                        o.hi.lemma_view_bounded();
                        lemma_from_over::<W>(self.lo.view() as int + o.lo.view() as int);
                        lemma_from_over::<W>(self.hi.view() as int + o.hi.view() as int);
                        assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                            Unsigned::<W>::add(x, y),
                        ) by {
                            lemma_from_over::<W>(x.view() as int + y.view() as int);
                        }
                    }
                    r
                } else {
                    Self::top()
                }
            },
        }
    }

    /// Exact when no difference wraps or every difference wraps once; top otherwise.
    fn sub(&self, o: &Self) -> (r: Self) {
        if o.hi.le(self.lo) {
            let lo = match self.lo.checked_sub(o.hi) {
                Some(v) => v,
                None => { return Self::top(); },  // unreachable
            };
            let hi = match self.hi.checked_sub(o.lo) {
                Some(v) => v,
                None => { return Self::top(); },  // unreachable
            };
            let r = Interval { lo, hi };
            proof {
                self.hi.lemma_view_bounded();
                assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                    Unsigned::<W>::sub(x, y),
                ) by {
                    x.lemma_view_bounded();
                    lemma_from_small::<W>(x.view() as int - y.view() as int);
                }
            }
            r
        } else if self.hi.lt(o.lo) {
            // every difference lies in [-M, 0): add M to both bounds
            let r = Interval { lo: self.lo.wrapping_sub(o.hi), hi: self.hi.wrapping_sub(o.lo) };
            proof {
                o.hi.lemma_view_bounded();
                lemma_from_under::<W>(self.lo.view() as int - o.hi.view() as int);
                lemma_from_under::<W>(self.hi.view() as int - o.lo.view() as int);
                assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                    Unsigned::<W>::sub(x, y),
                ) by {
                    y.lemma_view_bounded();
                    lemma_from_under::<W>(x.view() as int - y.view() as int);
                }
            }
            r
        } else {
            Self::top()
        }
    }

    /// `{0}` and intervals excluding 0 negate exactly; otherwise top.
    fn neg(&self) -> (r: Self) {
        let z = W::zero();
        if self.hi.eq(z) {
            proof {
                assert forall|x: W| self.gamma(x) implies #[trigger] self.gamma(Unsigned::<W>::neg(x)) by {
                    lemma_from_zero::<W>();
                }
            }
            self.dup()
        } else if self.lo.eq(z) {
            Self::top()
        } else {
            let r = Interval { lo: self.hi.neg_nonzero(), hi: self.lo.neg_nonzero() };
            proof {
                assert forall|x: W| self.gamma(x) implies #[trigger] r.gamma(Unsigned::<W>::neg(x)) by {
                    let m = W::modulus() as int;
                    x.lemma_view_bounded();
                    W::lemma_from_int(-(x.view() as int));
                    lemma_mod_add_multiples_vanish(-(x.view() as int), m);
                    lemma_small_mod((m - x.view()) as nat, m as nat);
                }
            }
            r
        }
    }
}

impl<W: Word> DivRem<Unsigned<W>> for Interval<W> {
    fn contains_zero(&self) -> (b: bool) {
        proof {
            lemma_from_zero::<W>();
        }
        self.lo.eq(W::zero())
    }

    /// `[lo / d.hi, hi / d.lo']` where `d.lo'` is the least nonzero divisor.
    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let z = W::zero();
        proof {
            lemma_from_zero::<W>();
        }
        if d.hi.eq(z) {
            (BotOr::Bot, DivZero::Always)
        } else {
            let dlo_pos = !d.lo.eq(z);
            let q_lo = self.lo.udiv(d.hi);
            let q_hi = if dlo_pos {
                self.hi.udiv(d.lo)
            } else {
                self.hi
            };
            proof {
                lemma_div_is_ordered(self.lo.view() as int, self.hi.view() as int, d.hi.view() as int);
                if dlo_pos {
                    lemma_div_is_ordered_by_denominator(
                        self.hi.view() as int,
                        d.lo.view() as int,
                        d.hi.view() as int,
                    );
                } else {
                    lemma_div_is_ordered_by_denominator(self.hi.view() as int, 1, d.hi.view() as int);
                }
                assert forall|x: W, y: W|
                    self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y) implies #[trigger] (Interval {
                    lo: q_lo,
                    hi: q_hi,
                }).gamma(Unsigned::<W>::div(x, y)) by {
                    x.lemma_view_bounded();
                    lemma_div_pos_is_pos(x.view() as int, y.view() as int);
                    lemma_div_is_ordered_by_denominator(x.view() as int, 1, y.view() as int);
                    lemma_from_small::<W>(x.view() as int / y.view() as int);
                    lemma_div_is_ordered(self.lo.view() as int, x.view() as int, y.view() as int);
                    lemma_div_is_ordered_by_denominator(
                        self.lo.view() as int,
                        y.view() as int,
                        d.hi.view() as int,
                    );
                    lemma_div_is_ordered(x.view() as int, self.hi.view() as int, y.view() as int);
                    if dlo_pos {
                        lemma_div_is_ordered_by_denominator(
                            self.hi.view() as int,
                            d.lo.view() as int,
                            y.view() as int,
                        );
                    } else {
                        lemma_div_is_ordered_by_denominator(self.hi.view() as int, 1, y.view() as int);
                    }
                }
            }
            let r = BotOr::Val(Interval { lo: q_lo, hi: q_hi });
            if dlo_pos {
                (r, DivZero::Never)
            } else {
                (r, DivZero::Maybe)
            }
        }
    }

    /// When every quotient is the same `q`, `x % y = x - q * y` is
    /// `[lo - q * d.hi, hi - q * d.lo']` (`d.lo'` the least nonzero divisor),
    /// which includes the identity case `hi < d.lo` (q = 0). Otherwise
    /// `[0, min(hi, d.hi - 1)]`.
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let z = W::zero();
        proof {
            lemma_from_zero::<W>();
        }
        if d.hi.eq(z) {
            return (BotOr::Bot, DivZero::Always);
        }
        let dm1 = match d.hi.checked_sub(W::one()) {
            Some(v) => v,
            None => { return (BotOr::Bot, DivZero::Always); },  // unreachable
        };
        let dlo1 = if d.lo.eq(z) {
            W::one()
        } else {
            d.lo
        };
        let flag = if d.lo.eq(z) {
            DivZero::Maybe
        } else {
            DivZero::Never
        };
        let q = self.lo.udiv(d.hi);
        let same_q = q.eq(self.hi.udiv(dlo1));
        if same_q {
            {
                proof {
                    lemma_fundamental_div_mod(self.lo.view() as int, d.hi.view() as int);
                    lemma_mod_bound(self.lo.view() as int, d.hi.view() as int);
                    lemma_fundamental_div_mod(self.hi.view() as int, dlo1.view() as int);
                    lemma_mod_bound(self.hi.view() as int, dlo1.view() as int);
                    lemma_mul_inequality(dlo1.view() as int, d.hi.view() as int, q.view() as int);
                    lemma_mul_is_commutative(q.view() as int, d.hi.view() as int);
                    lemma_mul_is_commutative(q.view() as int, dlo1.view() as int);
                    self.lo.lemma_view_bounded();
                    self.hi.lemma_view_bounded();
                }
                // q * d.hi <= lo and q * d.lo' <= hi, so neither product wraps.
                let qh = match q.checked_mul(d.hi) {
                    Some(v) => v,
                    None => {
                        proof {
                            assert(false);
                        }
                        z
                    },
                };
                let ql = match q.checked_mul(dlo1) {
                    Some(v) => v,
                    None => {
                        proof {
                            assert(false);
                        }
                        z
                    },
                };
                let lo_r = match self.lo.checked_sub(qh) {
                    Some(v) => v,
                    None => { return (BotOr::Val(Self::top()), flag); },  // unreachable
                };
                let hi_q = match self.hi.checked_sub(ql) {
                    Some(v) => v,
                    None => { return (BotOr::Val(Self::top()), flag); },  // unreachable
                };
                let hi_r = if hi_q.le(dm1) {
                    hi_q
                } else {
                    dm1
                };
                let r = Interval { lo: lo_r, hi: hi_r };
                proof {
                    assert forall|x: W, y: W|
                        self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y) implies #[trigger] r.gamma(
                        Unsigned::<W>::rem(x, y),
                    ) by {
                        let (xv, yv, qv) = (x.view() as int, y.view() as int, q.view() as int);
                        x.lemma_view_bounded();
                        // x / y == q: lo/d.hi <= lo/y <= x/y <= hi/y <= hi/d.lo'
                        lemma_div_is_ordered(self.lo.view() as int, xv, yv);
                        lemma_div_is_ordered_by_denominator(self.lo.view() as int, yv, d.hi.view() as int);
                        lemma_div_is_ordered(xv, self.hi.view() as int, yv);
                        lemma_div_is_ordered_by_denominator(self.hi.view() as int, dlo1.view() as int, yv);
                        lemma_fundamental_div_mod(xv, yv);
                        lemma_mod_bound(xv, yv);
                        lemma_mul_inequality(yv, d.hi.view() as int, qv);
                        lemma_mul_inequality(dlo1.view() as int, yv, qv);
                        lemma_mul_is_commutative(qv, yv);
                        lemma_from_small::<W>(xv % yv);
                    }
                }
                return (BotOr::Val(r), flag);
            }
        }
        let hi = if self.hi.le(dm1) {
            self.hi
        } else {
            dm1
        };
        let r = Interval { lo: z, hi };
        proof {
            assert forall|x: W, y: W|
                self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y) implies #[trigger] r.gamma(
                Unsigned::<W>::rem(x, y),
            ) by {
                x.lemma_view_bounded();
                lemma_mod_bound(x.view() as int, y.view() as int);
                lemma_mod_decreases(x.view(), y.view());
                lemma_from_small::<W>(x.view() as int % y.view() as int);
            }
        }
        (BotOr::Val(r), flag)
    }
}

impl<W: Word> Mul<Unsigned<W>> for Interval<W> {
    /// `[lo * o.lo, hi * o.hi]` when no product wraps, top otherwise.
    fn mul(&self, o: &Self) -> (r: Self) {
        match (self.lo.checked_mul(o.lo), self.hi.checked_mul(o.hi)) {
            (Some(lo), Some(hi)) => {
                let r = Interval { lo, hi };
                proof {
                    hi.lemma_view_bounded();
                    lemma_mul_upper_bound(
                        self.lo.view() as int,
                        self.hi.view() as int,
                        o.lo.view() as int,
                        o.hi.view() as int,
                    );
                    assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                        Unsigned::<W>::mul(x, y),
                    ) by {
                        let (xv, yv) = (x.view() as int, y.view() as int);
                        lemma_mul_upper_bound(xv, self.hi.view() as int, yv, o.hi.view() as int);
                        lemma_mul_upper_bound(self.lo.view() as int, xv, o.lo.view() as int, yv);
                        lemma_from_small::<W>(xv * yv);
                    }
                }
                r
            },
            _ => Self::top(),
        }
    }
}

impl<W: Word> Interval<W> {
    /// Shared flag logic for the signed placeholder transfers.
    fn signed_div_flag(d: &Self) -> (r: (BotOr<Self>, DivZero))
        requires
            d.wf(),
        ensures
            r.0.wf(),
            forall|c: W| #[trigger] r.0.gamma(c) <== !(r.0 is Bot),
            r.1 is Never ==> !d.gamma(Signed::<W>::zero()),
            r.1 is Always ==> forall|y: W| #[trigger] d.gamma(y) ==> Signed::<W>::is_zero(y),
            (r.0 is Bot) <==> (r.1 is Always),
    {
        let z = W::zero();
        proof {
            lemma_from_zero::<W>();
        }
        if d.hi.eq(z) {
            (BotOr::Bot, DivZero::Always)
        } else if d.lo.eq(z) {
            (BotOr::Val(Self::top()), DivZero::Maybe)
        } else {
            (BotOr::Val(Self::top()), DivZero::Never)
        }
    }
}

/// Signed division is sound but coarse (top): an unsigned interval straddling
/// 2^(N-1) is two signed ranges. Precise signed transfers split at the sign
/// boundary (Verasco's normalization, Jourdan thesis ch. 5) and are future work.
impl<W: Word> DivRem<Signed<W>> for Interval<W> {
    fn contains_zero(&self) -> (b: bool) {
        proof {
            lemma_from_zero::<W>();
        }
        self.lo.eq(W::zero())
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::signed_div_flag(d)
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::signed_div_flag(d)
    }
}

/// Bounds that hold bit by bit: `x & y` is at most either operand, `x | y` at
/// least either one, and `x | y`, `x ^ y` have no bit above the higher top.
/// Warren's minOR/maxOR (Hacker's Delight 4-3) would make `and`/`or` exact.
impl<W: Word> Bitwise<W> for Interval<W> {
    fn and(&self, o: &Self) -> (r: Self) {
        let hi = if self.hi.le(o.hi) {
            self.hi
        } else {
            o.hi
        };
        let r = Interval { lo: W::zero(), hi };
        proof {
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                x.and(y),
            ) by {
                W::lemma_and_le(x, y);
            }
        }
        r
    }

    fn or(&self, o: &Self) -> (r: Self) {
        let lo = if self.lo.le(o.lo) {
            o.lo
        } else {
            self.lo
        };
        let m = if self.hi.le(o.hi) {
            o.hi
        } else {
            self.hi
        };
        let r = Interval { lo, hi: m.smear() };
        proof {
            W::lemma_below_ones_above(m, m, m);
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                x.or(y),
            ) by {
                W::lemma_or_ge(x, y);
                W::lemma_below_ones_above(x, y, m);
            }
        }
        r
    }

    fn xor(&self, o: &Self) -> (r: Self) {
        let m = if self.hi.le(o.hi) {
            o.hi
        } else {
            self.hi
        };
        let r = Interval { lo: W::zero(), hi: m.smear() };
        proof {
            W::lemma_below_ones_above(m, m, m);
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                x.xor(y),
            ) by {
                W::lemma_below_ones_above(x, y, m);
            }
        }
        r
    }

    /// Exact: `!x = MAX - x` reverses the order.
    fn not(&self) -> (r: Self) {
        let r = Interval { lo: self.hi.bit_not(), hi: self.lo.bit_not() };
        proof {
            W::lemma_not(self.lo);
            W::lemma_not(self.hi);
            assert forall|x: W| self.gamma(x) implies #[trigger] r.gamma(x.not()) by {
                W::lemma_not(x);
            }
        }
        r
    }
}

impl<W: Word> Shift<Unsigned<W>> for Interval<W> {
    /// `[lo << a, hi << b]` over the in-range amounts `[a, b]` when no result
    /// wraps; top otherwise.
    fn shl(&self, k: &Self) -> (r: BotOr<Self>) {
        let (a, b) = match Self::shift_range(k) {
            Some(ab) => ab,
            None => return BotOr::Bot,
        };
        proof {
            lemma_shl_bounds(self.lo.view(), self.lo.view(), self.hi.view(), a as nat, a as nat, b as nat);
        }
        match self.hi.checked_shl(b) {
            Some(hi) => {
                proof {
                    hi.lemma_view_bounded();
                }
                let lo = match self.lo.checked_shl(a) {
                    Some(lo) => lo,
                    None => {
                        proof {
                            assert(false);
                        }
                        W::zero()
                    },
                };
                let r = Interval { lo, hi };
                proof {
                    assert forall|x: W, s: W|
                        self.gamma(x) && k.gamma(s) && Unsigned::<W>::shift_ok(s) implies #[trigger] r.gamma(
                        Unsigned::<W>::shl(x, s),
                    ) by {
                        lemma_shl_bounds(self.lo.view(), x.view(), self.hi.view(), a as nat, s.view(), b as nat);
                        lemma_from_small::<W>((x.view() * pow2(s.view())) as int);
                    }
                }
                BotOr::Val(r)
            },
            None => BotOr::Val(Self::top()),
        }
    }

    /// `[lo >> b, hi >> a]` over the in-range amounts `[a, b]`.
    fn shr(&self, k: &Self) -> (r: BotOr<Self>) {
        let (a, b) = match Self::shift_range(k) {
            Some(ab) => ab,
            None => return BotOr::Bot,
        };
        let r = Interval { lo: self.lo.shr(b), hi: self.hi.shr(a) };
        proof {
            lemma_shr_bounds(self.lo.view(), self.lo.view(), self.hi.view(), a as nat, a as nat, b as nat);
            assert forall|x: W, s: W|
                self.gamma(x) && k.gamma(s) && Unsigned::<W>::shift_ok(s) implies #[trigger] r.gamma(
                Unsigned::<W>::shr(x, s),
            ) by {
                lemma_shr_bounds(self.lo.view(), x.view(), self.hi.view(), a as nat, s.view(), b as nat);
                x.lemma_view_bounded();
                lemma_from_small::<W>((x.view() / pow2(s.view())) as int);
            }
        }
        BotOr::Val(r)
    }
}

} // verus!
