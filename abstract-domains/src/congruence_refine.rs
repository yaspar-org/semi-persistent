// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Congruence participation in the unsigned-bounds fact channel.
//!
//! This exports the unsigned hull and consumes disjoint or singleton bounds.
//! General grid clipping belongs to Facts normalization. Once Facts has a
//! congruence field, export and meet that field as well.
#![allow(unused_variables)]
use crate::congruence::Congruence;
use crate::facts::Facts;
use crate::interval::Interval;
use crate::lattice::*;
use crate::reduce::Refine;
use crate::word::Word;
use vstd::prelude::*;

verus! {

impl<W: Word> Refine for Congruence<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        let (_, lo) = self.parts();
        let hi = self.max_member();
        proof {
            assert forall|x: W| #[trigger] self.has(x) implies lo.view() <= x.view() by {
                self.member_decomposition(x);
            }
        }
        let result = match Interval::new(lo, hi) {
            Some(u) => BotOr::Val(Facts::from_interval(u)),
            None => BotOr::Bot,
        };
        proof {
            assert forall|x: W| <Self as Domain>::gamma(self, x) implies #[trigger] result.gamma(x) by {
                assert(self.has(x));
            }
        }
        result
    }

    /// Bounds can reject the hull or identify a constant without grid clipping.
    /// Other intervals retain the congruence; the product retains their bounds.
    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        let u = f.interval();
        let hull = self.to_channel();
        let h = match hull {
            BotOr::Bot => {
                proof {
                    assert forall|x: W| #[trigger] <Self as Domain>::gamma(self, x) implies false by {
                        assert(hull.gamma(x));
                    }
                }
                return BotOr::Bot;
            },
            BotOr::Val(h) => h.interval(),
        };
        proof {
            assert forall|x: W| #[trigger] self.has(x) implies h.gamma(x) by {
                assert(<Self as Domain>::gamma(self, x));
                assert(hull.gamma(x));
            }
        }
        let overlap = h.meet_exact(&u);
        let result = match overlap {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(i) => {
                let (lo, hi) = i.bounds();
                if lo.eq(hi) {
                    proof {
                        assert forall|x: W| self.has(x) && f.gamma(x) implies x == lo by {
                            assert(hull.gamma(x));
                            assert(h.gamma(x) && u.gamma(x));
                            assert(overlap.gamma(x));
                            W::lemma_view_injective(x, lo);
                        }
                    }
                    let c = Congruence::constant(lo);
                    let r = self.meet(&c);
                    proof {
                        assert forall|x: W| self.has(x) && f.gamma(x) implies #[trigger] r.gamma(x) by {
                            assert(x == lo);
                            assert(c.has(x));
                            match r {
                                BotOr::Val(v) => { assert(v.has(x)); },
                                BotOr::Bot => {},
                            }
                        }
                    }
                    r
                } else {
                    BotOr::Val(self.dup())
                }
            },
        };
        proof {
            assert forall|x: W| <Self as Domain>::gamma(self, x) && f.gamma(x)
                implies #[trigger] result.gamma(x) by {
                assert(self.has(x));
                assert(h.gamma(x) && u.gamma(x));
                assert(overlap.gamma(x));
            }
            assert forall|x: W| #[trigger] result.gamma(x)
                implies <Self as Domain>::gamma(self, x) by {
                match result {
                    BotOr::Val(c) => { assert(c.has(x)); },
                    BotOr::Bot => {},
                }
            }
        }
        result
    }
}

} // verus!
