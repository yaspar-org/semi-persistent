// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Congruence participation in the interval/congruence fact channel.
//!
//! Exports the unsigned hull and congruence, and consumes both fields through
//! exact congruence meet and grid-aware Facts normalization.
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
                self.lemma_member_decomposition(x);
            }
        }
        let result = match Interval::new(lo, hi) {
            Some(u) => Facts::from_parts(u, self.dup()),
            None => BotOr::Bot,
        };
        proof {
            assert forall|x: W| <Self as Domain>::gamma(self, x) implies #[trigger] result.gamma(x) by {
                assert(self.has(x));
            }
        }
        result
    }

    /// Meet the incoming grid and normalize it against the incoming bounds.
    /// Singleton feedback strengthens the leaf; products retain snapped bounds.
    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        let u = f.interval();
        let incoming = f.congruence();
        let merged = self.meet(&incoming);
        let result = match merged {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(c) => {
                let normalized = Facts::from_parts(u, c.dup());
                match normalized {
                    BotOr::Bot => {
                        proof {
                            assert forall|x: W| self.has(x) && f.gamma(x) implies false by {
                                assert(incoming.has(x));
                                assert(c.has(x) && u.gamma(x));
                                assert(normalized.gamma(x));
                            }
                        }
                        BotOr::Bot
                    },
                    BotOr::Val(n) => {
                        let nc = n.congruence();
                        let r = c.meet(&nc);
                        proof {
                            assert forall|x: W| self.has(x) && f.gamma(x)
                                implies #[trigger] r.gamma(x) by {
                                assert(incoming.has(x));
                                assert(c.has(x) && u.gamma(x));
                                assert(normalized.gamma(x));
                                assert(n.gamma(x) && nc.has(x));
                                match r {
                                    BotOr::Val(v) => { assert(v.has(x)); },
                                    BotOr::Bot => {},
                                }
                            }
                            assert forall|x: W| #[trigger] r.gamma(x) implies self.has(x) by {
                                match r {
                                    BotOr::Val(v) => {
                                        assert(v.has(x));
                                        assert(c.has(x));
                                    },
                                    BotOr::Bot => {},
                                }
                            }
                        }
                        r
                    },
                }
            },
        };
        proof {
            assert forall|x: W| <Self as Domain>::gamma(self, x) && f.gamma(x)
                implies #[trigger] result.gamma(x) by {
                assert(self.has(x) && incoming.has(x));
            }
        }
        result
    }
}

} // verus!
