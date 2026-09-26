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

    proof fn lemma_nonempty(&self) {
        assert(self.gamma(self.lo));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert(a.gamma(a.lo) && a.gamma(a.hi) && a.gamma(b.lo) && a.gamma(b.hi));
        W::lemma_view_injective(a.lo, b.lo);
        W::lemma_view_injective(a.hi, b.hi);
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

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
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

impl<W: Word> Arith<Unsigned<W>> for Interval<W> {
    /// Exact when no sum wraps, top otherwise.
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
            None => Self::top(),
        }
    }

    /// Exact when no difference wraps, top otherwise.
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

    /// `[0, min(hi, d.hi - 1)]`.
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let z = W::zero();
        proof {
            lemma_from_zero::<W>();
        }
        if d.hi.eq(z) {
            (BotOr::Bot, DivZero::Always)
        } else {
            let dm1 = match d.hi.checked_sub(W::one()) {
                Some(v) => v,
                None => { return (BotOr::Bot, DivZero::Always); },  // unreachable
            };
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
            if d.lo.eq(z) {
                (BotOr::Val(r), DivZero::Maybe)
            } else {
                (BotOr::Val(r), DivZero::Never)
            }
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

} // verus!
