// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Facts<W>`: the channel of BitVec(W) e-classes.
//!
//! A record of fields, one per kind of fact, with `γ` the intersection of the
//! fields' concretizations. `normalize` propagates information between fields
//! (the reduction); `wf` adds to the field-wise invariant `pre_wf` the
//! condition that the fields are mutually reduced, which keeps `Facts`
//! canonical.
//!
//! **Adding a field** (doc/reduced-product.md, "Adding a field"): add it to the
//! struct, to `pre_wf`, `gamma`, `dup`, `top` (as top), `leq`, `join`, `widen`
//! and `meet_exact` (field-wise), extend `reduced` and `normalize`, and set it
//! to top in every constructor. A top field adds no constraint to `γ`, so every
//! existing `to_channel` stays sound and every existing `refine` stays valid.
//!
//! Planned fields (doc/reduced-product.md, planned work):
//! - `c`, a congruence `x ≡ r mod m` on the #117 `Word` primitives
//!   (src/congruence.rs);
//! - `s`, signed bounds (src/sbounds.rs);
//! - `bits`, known bits, a Tnum over `Word` (src/tnum_w.rs).
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::interval::*;
use crate::lattice::*;
use crate::reduce::*;
use crate::word::*;
use vstd::prelude::*;

verus! {

// TODO(abs-domain-registry): add the fields `s` (sbounds), `c` (congruence) and `bits` (known bits); the record keeps every field and a domain mask selects them, see abstract-domains/doc/future/registry-task.md §2
// TODO(abs-domain-registry): give Facts<W> a fixed-width Copy encoding into the registry entry (2 words per field, W bytes with all 4 fields) with a proved decode(encode(f)) == f, see abstract-domains/doc/future/registry-task.md §3
pub struct Facts<W> {
    /// Unsigned bounds.
    u: Interval<W>,
}

impl<W: Word> Facts<W> {
    pub closed spec fn u(&self) -> Interval<W> {
        self.u
    }

    // TODO(abs-domain-registry): parameterize `reduced` and `normalize` by the domain mask: a disabled field stays top and its reduction steps are skipped, see abstract-domains/doc/future/registry-task.md §6
    /// The fields agree: no field can be tightened from the others. Trivially
    /// true with one field; the planned normalize steps extend it.
    pub open spec fn reduced(&self) -> bool {
        true
    }

    /// The record that knows only `u`.
    pub fn from_interval(u: Interval<W>) -> (r: Self)
        requires
            u.wf(),
        ensures
            r.wf(),
            r.u() == u,
            forall|x: W| #[trigger] r.gamma(x) == u.gamma(x),
    {
        Facts { u }
    }

    // TODO(abs-domain-registry): add `as_constant` here: Some(v) exactly when gamma is {v}; the registry's is_singleton calls it, see abstract-domains/doc/future/registry-task.md §5
    pub fn interval(&self) -> (r: Interval<W>)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.u(),
            forall|x: W| self.gamma(x) ==> #[trigger] r.gamma(x),
    {
        self.u.dup()
    }
}

impl<W: Word> Domain for Facts<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        self.pre_wf() && self.reduced()
    }

    open spec fn gamma(&self, c: W) -> bool {
        self.u().gamma(c)
    }

    fn dup(&self) -> (r: Self) {
        Facts { u: self.u.dup() }
    }

    fn top() -> (r: Self) {
        Facts { u: Interval::top() }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        self.u.leq(&o.u)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        Facts { u: self.u.join(&o.u) }
    }

    /// `meet_exact` then `normalize`, inlined field by field: calling them from
    /// here would make this impl depend on functions whose contracts mention it.
    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        match self.u.meet(&o.u) {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(u) => BotOr::Val(Facts { u }),
        }
    }

    fn widen(&self, o: &Self) -> (r: Self) {
        Facts { u: self.u.widen(&o.u) }
    }
}

impl<W: Word> Canonical for Facts<W> {
    proof fn lemma_nonempty(&self) {
        assert(self.gamma(self.u.lo()));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert forall|c: W| #![trigger a.u.gamma(c)] a.u.gamma(c) == b.u.gamma(c) by {
            assert(a.gamma(c) == b.gamma(c));
        }
        Interval::lemma_canonical(&a.u, &b.u);
    }
}

impl<W: Word> Channel for Facts<W> {
    open spec fn pre_wf(&self) -> bool {
        self.u().wf()
    }

    proof fn lemma_wf_pre(&self) {
    }

    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>) {
        let m = self.u.meet_exact(&o.u);
        match m {
            BotOr::Bot => {
                proof {
                    assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {
                        assert(m.gamma(c) == (self.u.gamma(c) && o.u.gamma(c)));
                    }
                }
                BotOr::Bot
            },
            BotOr::Val(u) => {
                let r = Facts { u };
                proof {
                    assert forall|c: W| #[trigger] r.gamma(c) == (self.gamma(c) && o.gamma(c)) by {
                        assert(BotOr::<Interval<W>>::Val(u).gamma(c) == (self.u.gamma(c)
                            && o.u.gamma(c)));
                    }
                }
                BotOr::Val(r)
            },
        }
    }

    /// The identity: with one field there is nothing to propagate. The planned work adds
    /// the steps (doc/reduced-product.md): interval and congruence snap to each
    /// other's grid, unsigned and signed bounds tighten each other, and later
    /// known bits against bounds and congruence against low bits.
    fn normalize(&self) -> (r: BotOr<Self>) {
        BotOr::Val(self.dup())
    }
}

/// Every channel implements `Refine` for itself: `to_channel` is the identity,
/// `refine` is the reduced meet.
impl<W: Word> Refine for Facts<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        BotOr::Val(self.dup())
    }

    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        meet_normalize(self, f)
    }
}

/// An unsigned interval writes itself into the `u` field and refines by it.
impl<W: Word> Refine for Interval<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        BotOr::Val(Facts::from_interval(self.dup()))
    }

    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        let u = f.interval();
        let r = self.meet_exact(&u);
        proof {
            assert forall|x: W| self.gamma(x) && f.gamma(x) implies #[trigger] r.gamma(x) by {
                assert(u.gamma(x));
            }
        }
        r
    }
}

} // verus!
