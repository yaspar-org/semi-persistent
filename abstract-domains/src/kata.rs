// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Ramp-up kata 3 and 4: a u8 interval written without copying `domains.rs`.
//!
//! Kata 3: `has` and `add`, plus containment of wrapping sums.
//! Kata 4: meet commutative and idempotent; `add` monotone; then a bottom
//! value and the meet laws again. Disjoint meet without bottom returns
//! `top`, which is sound and breaks associativity — that is why §3.1
//! puts bottom first.
//!
//! Compared with `domains.rs` after writing this file: production `Interval`
//! is the same pair `{lo, hi}` with `wf = lo <= hi`, the same overflow-to-top
//! `add`, and the same disjoint-meet-returns-top. It has no bottom and does
//! not state the lattice laws this kata proves.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Kata 3 — interval over u8, no bottom
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Interval {
    pub lo: u8,
    pub hi: u8,
}

impl Interval {
    pub open spec fn wf(self) -> bool {
        self.lo <= self.hi
    }

    pub open spec fn has(self, x: u8) -> bool {
        self.lo <= x && x <= self.hi
    }

    pub open spec fn refines(self, other: Interval) -> bool {
        forall|x: u8| #![auto] self.has(x) ==> other.has(x)
    }

    pub open spec fn top_spec() -> Interval {
        Interval { lo: 0, hi: 255 }
    }

    pub fn top() -> (r: Interval)
        ensures
            r.wf(),
            r == Interval::top_spec(),
    {
        Interval { lo: 0, hi: 255 }
    }

    pub proof fn top_has(x: u8)
        ensures
            Interval::top_spec().has(x),
    {
    }

    pub fn constant(n: u8) -> (r: Interval)
        ensures
            r.wf(),
            r.has(n),
            r.lo == n && r.hi == n,
    {
        Interval { lo: n, hi: n }
    }

    pub fn contains(&self, x: u8) -> (r: bool)
        ensures
            r == self.has(x),
    {
        self.lo <= x && x <= self.hi
    }

    pub open spec fn add_spec(self, t: Interval) -> Interval {
        if self.lo as int + t.lo as int > 255 || self.hi as int + t.hi as int > 255 {
            Interval::top_spec()
        } else {
            Interval {
                lo: (self.lo as int + t.lo as int) as u8,
                hi: (self.hi as int + t.hi as int) as u8,
            }
        }
    }

    /// Soundness: every wrapping sum of contained inputs is in the result.
    /// Endpoint overflow returns top — the same policy `domains.rs` uses.
    /// `bit_vector` proofs may only mention local `u8`s, not `self.hi`.
    pub fn add(&self, t: &Interval) -> (r: Interval)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r == self.add_spec(*t),
            forall|x: u8, y: u8| #![auto] self.has(x) && t.has(y) ==> r.has(
                x.wrapping_add(y),
            ),
    {
        let slo = self.lo;
        let shi = self.hi;
        let tlo = t.lo;
        let thi = t.hi;
        let lo = slo.wrapping_add(tlo);
        let hi = shi.wrapping_add(thi);
        if lo < slo || hi < shi {
            proof {
                assert(slo as int + tlo as int > 255 || shi as int + thi as int > 255) by (
                bit_vector)
                    requires
                        lo == slo.wrapping_add(tlo),
                        hi == shi.wrapping_add(thi),
                        lo < slo || hi < shi;
                assert(self.add_spec(*t) == Interval::top_spec());
                assert forall|x: u8, y: u8| #![auto] self.has(x) && t.has(y) implies Interval::top_spec().has(
                    x.wrapping_add(y),
                ) by {
                    Interval::top_has(x.wrapping_add(y));
                };
            }
            Interval::top()
        } else {
            proof {
                assert(slo as int + tlo as int <= 255 && shi as int + thi as int <= 255) by (
                bit_vector)
                    requires
                        lo == slo.wrapping_add(tlo),
                        hi == shi.wrapping_add(thi),
                        lo >= slo,
                        hi >= shi;
                assert(self.add_spec(*t) == Interval { lo, hi });
                assert forall|x: u8, y: u8| #![auto] self.has(x) && t.has(y) implies (Interval {
                    lo,
                    hi,
                }).has(x.wrapping_add(y)) by {
                    assert(x.wrapping_add(y) >= x && x.wrapping_add(y) >= y) by (bit_vector)
                        requires
                            x <= shi,
                            y <= thi,
                            hi == shi.wrapping_add(thi),
                            hi >= shi;
                    assert(slo.wrapping_add(tlo) <= x.wrapping_add(y)) by (bit_vector)
                        requires
                            slo <= x,
                            tlo <= y,
                            x.wrapping_add(y) >= x,
                            lo == slo.wrapping_add(tlo),
                            lo >= slo;
                    assert(x.wrapping_add(y) <= shi.wrapping_add(thi)) by (bit_vector)
                        requires
                            x <= shi,
                            y <= thi,
                            x.wrapping_add(y) >= y,
                            hi == shi.wrapping_add(thi),
                            hi >= shi;
                };
            }
            Interval { lo, hi }
        }
    }

    pub open spec fn meet_spec(self, t: Interval) -> Interval {
        let lo = if self.lo > t.lo {
            self.lo
        } else {
            t.lo
        };
        let hi = if self.hi < t.hi {
            self.hi
        } else {
            t.hi
        };
        if hi < lo {
            Interval::top_spec()
        } else {
            Interval { lo, hi }
        }
    }

    pub fn meet(&self, t: &Interval) -> (r: Interval)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r == self.meet_spec(*t),
            forall|x: u8| #![auto] self.has(x) && t.has(x) ==> r.has(x),
    {
        let lo = if self.lo > t.lo {
            self.lo
        } else {
            t.lo
        };
        let hi = if self.hi < t.hi {
            self.hi
        } else {
            t.hi
        };
        if hi < lo {
            proof {
                assert forall|x: u8| #![auto] self.has(x) && t.has(x) implies Interval::top_spec().has(x)
                    by {
                    Interval::top_has(x);
                };
            }
            Interval::top()
        } else {
            Interval { lo, hi }
        }
    }
}

// ---------------------------------------------------------------------------
// Kata 4, first half — meet laws and add monotone (still no bottom)
// ---------------------------------------------------------------------------

pub proof fn meet_comm(a: Interval, b: Interval)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b) == b.meet_spec(a),
{
}

pub proof fn meet_idempotent(a: Interval)
    requires
        a.wf(),
    ensures
        a.meet_spec(a) == a,
{
}

/// The hard one: a tighter operand must not make the sum looser.
/// If `b + c` overflows to top, anything refines top. If it does not,
/// `a` is tighter so `a + c` cannot overflow either, and the summed
/// endpoints sit inside `b + c`.
pub proof fn add_monotone(a: Interval, b: Interval, c: Interval)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.lo >= b.lo,
        a.hi <= b.hi,
    ensures
        a.add_spec(c).refines(b.add_spec(c)),
{
    let ac = a.add_spec(c);
    let bc = b.add_spec(c);
    if b.lo as int + c.lo as int > 255 || b.hi as int + c.hi as int > 255 {
        assert(bc == Interval::top_spec());
        assert forall|z: u8| #![auto] ac.has(z) implies bc.has(z) by {
            Interval::top_has(z);
        };
    } else {
        assert(a.lo as int + c.lo as int <= 255);
        assert(a.hi as int + c.hi as int <= 255);
        assert(ac.lo as int == a.lo as int + c.lo as int);
        assert(bc.lo as int == b.lo as int + c.lo as int);
        assert(ac.hi as int == a.hi as int + c.hi as int);
        assert(bc.hi as int == b.hi as int + c.hi as int);
        assert forall|z: u8| #![auto] ac.has(z) implies bc.has(z) by {};
    }
}

// ---------------------------------------------------------------------------
// Kata 4, second half — explicit bottom, then the meet laws again
// ---------------------------------------------------------------------------

/// `empty` is bottom. All bottoms are identified by `eq_abs`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct IntervalBot {
    pub lo: u8,
    pub hi: u8,
    pub empty: bool,
}

impl IntervalBot {
    pub open spec fn wf(self) -> bool {
        self.empty || self.lo <= self.hi
    }

    pub open spec fn has(self, x: u8) -> bool {
        !self.empty && self.lo <= x && x <= self.hi
    }

    pub open spec fn eq_abs(self, other: IntervalBot) -> bool {
        (self.empty && other.empty) || (!self.empty && !other.empty && self.lo == other.lo
            && self.hi == other.hi)
    }

    pub open spec fn bottom_spec() -> IntervalBot {
        IntervalBot { lo: 0, hi: 0, empty: true }
    }

    pub open spec fn top_spec() -> IntervalBot {
        IntervalBot { lo: 0, hi: 255, empty: false }
    }

    pub fn bottom() -> (r: IntervalBot)
        ensures
            r.wf(),
            r == IntervalBot::bottom_spec(),
    {
        IntervalBot { lo: 0, hi: 0, empty: true }
    }

    pub fn top() -> (r: IntervalBot)
        ensures
            r.wf(),
            r == IntervalBot::top_spec(),
    {
        IntervalBot { lo: 0, hi: 255, empty: false }
    }

    pub fn range(lo: u8, hi: u8) -> (r: IntervalBot)
        requires
            lo <= hi,
        ensures
            r.wf(),
            !r.empty,
            r.lo == lo && r.hi == hi,
    {
        IntervalBot { lo, hi, empty: false }
    }

    pub fn contains(&self, x: u8) -> (r: bool)
        ensures
            r == self.has(x),
    {
        !self.empty && self.lo <= x && x <= self.hi
    }

    pub open spec fn meet_spec(self, t: IntervalBot) -> IntervalBot {
        if self.empty || t.empty {
            IntervalBot::bottom_spec()
        } else {
            let lo = if self.lo > t.lo {
                self.lo
            } else {
                t.lo
            };
            let hi = if self.hi < t.hi {
                self.hi
            } else {
                t.hi
            };
            if hi < lo {
                IntervalBot::bottom_spec()
            } else {
                IntervalBot { lo, hi, empty: false }
            }
        }
    }

    pub fn meet(&self, t: &IntervalBot) -> (r: IntervalBot)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.meet_spec(*t)),
            forall|x: u8| #![auto] r.has(x) ==> self.has(x) && t.has(x),
    {
        if self.empty || t.empty {
            IntervalBot::bottom()
        } else {
            let lo = if self.lo > t.lo {
                self.lo
            } else {
                t.lo
            };
            let hi = if self.hi < t.hi {
                self.hi
            } else {
                t.hi
            };
            if hi < lo {
                IntervalBot::bottom()
            } else {
                IntervalBot { lo, hi, empty: false }
            }
        }
    }
}

pub proof fn meet_bot_comm(a: IntervalBot, b: IntervalBot)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b).eq_abs(b.meet_spec(a)),
{
}

pub proof fn meet_bot_idempotent(a: IntervalBot)
    requires
        a.wf(),
    ensures
        a.meet_spec(a).eq_abs(a),
{
}

pub proof fn meet_bot_identity(a: IntervalBot)
    requires
        a.wf(),
    ensures
        a.meet_spec(IntervalBot::top_spec()).eq_abs(a),
        a.meet_spec(IntervalBot::bottom_spec()).eq_abs(IntervalBot::bottom_spec()),
{
}

pub proof fn meet_bot_assoc(a: IntervalBot, b: IntervalBot, c: IntervalBot)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        a.meet_spec(b).meet_spec(c).eq_abs(a.meet_spec(b.meet_spec(c))),
{
}

} // verus!
