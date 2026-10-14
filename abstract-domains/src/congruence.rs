// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, nonempty congruences over unsigned finite-width words.
//! This semantic core intentionally does not implement `Domain`: its lattice
//! operations belong to the subsequent Congruence core change.
#![allow(unused_imports, unused_variables)]
use crate::word::Word;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// `(0, r)` is a singleton; `(1, 0)` is top. Other canonical pairs
/// satisfy `r < m` and have a representable second member `r + m`.
/// Use `new` for raw pairs; fields cannot bypass normalization.
pub struct Congruence<W> {
    modulus: W,
    residue: W,
}

/// Raw descriptions use a congruence class, even for an unreduced residue.
pub open spec fn raw_has<W: Word>(m: W, r: W, x: W) -> bool {
    if m.view() == 0 { x == r }
    else { x.view() % m.view() == r.view() % m.view() }
}

/// A member after the least member is at least one full step away.
proof fn lemma_next(m: nat, r: nat, x: nat)
    requires m > 0, r < m, x % m == r,
    ensures r <= x, x == r || r + m <= x,
{
    lemma_mod_decreases(x, m);
    lemma_fundamental_div_mod(x as int, m as int);
    assert(x == r || r + m <= x) by (nonlinear_arith)
        requires m > 0, x == m * (x / m) + r;
}

impl<W: Word> Congruence<W> {
    pub closed spec fn modulus(&self) -> W { self.modulus }
    pub closed spec fn residue(&self) -> W { self.residue }

    pub open spec fn wf(&self) -> bool {
        self.modulus().view() == 0 || (
            self.residue().view() < self.modulus().view()
            && self.residue().view() + self.modulus().view() < W::modulus())
    }

    pub open spec fn gamma(&self, x: W) -> bool {
        if self.modulus().view() == 0 { x == self.residue() }
        else { x.view() % self.modulus().view() == self.residue().view() }
    }

    pub open spec fn has(&self, x: W) -> bool { self.gamma(x) }

    pub fn parts(&self) -> (r: (W, W))
        ensures r.0 == self.modulus(), r.1 == self.residue(),
    { (self.modulus, self.residue) }

    pub fn contains(&self, x: W) -> (r: bool)
        ensures r == self.gamma(x), r == self.has(x),
    {
        if self.modulus.eq(W::zero()) {
            proof { W::lemma_view_injective(x, self.residue); }
            x.eq(self.residue)
        } else { x.urem(self.modulus).eq(self.residue) }
    }

    pub fn constant(x: W) -> (r: Self)
        ensures r.wf(), r.modulus().view() == 0, r.residue() == x,
            forall|c: W| #[trigger] r.gamma(c) <==> c == x,
    { Self { modulus: W::zero(), residue: x } }

    pub fn top() -> (r: Self)
        ensures r.wf(), r.modulus().view() == 1, r.residue().view() == 0,
            forall|c: W| #[trigger] r.gamma(c),
    {
        proof { W::lemma_modulus(); }
        Self { modulus: W::one(), residue: W::zero() }
    }

    /// Normalize a raw class, collapsing progressions with only one word.
    /// For nonzero `modulus`, raw membership means `x % m == residue % m`,
    /// including when the input residue is not reduced. No addition wraps.
    pub fn new(modulus: W, residue: W) -> (r: Self)
        ensures r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> raw_has(modulus, residue, x),
    {
        if modulus.eq(W::zero()) { Self::constant(residue) }
        else {
            let rem = residue.urem(modulus);
            proof { lemma_mod_bound(residue.view() as int, modulus.view() as int); }
            match rem.checked_add(modulus) {
                Some(second) => {
                    proof { second.lemma_view_bounded(); }
                    Self { modulus, residue: rem }
                },
                None => {
                    let r = Self::constant(rem);
                    proof {
                        assert forall|x: W| #[trigger] r.gamma(x) <==> raw_has(modulus, residue, x) by {
                            x.lemma_view_bounded();
                            lemma_small_mod(rem.view(), modulus.view());
                            if raw_has(modulus, residue, x) {
                                lemma_next(modulus.view(), rem.view(), x.view());
                                W::lemma_view_injective(x, rem);
                            }
                        }
                    }
                    r
                },
            }
        }
    }

    /// Already-constructed values are canonical, so normalization is identity.
    /// To normalize a raw/legacy pair, use `new(modulus, residue)`.
    pub fn normalize(&self) -> (r: Self)
        requires self.wf(),
        ensures r.wf(), r == *self,
            forall|x: W| #[trigger] r.gamma(x) == self.gamma(x),
    { Self { modulus: self.modulus, residue: self.residue } }

    pub proof fn lemma_nonempty(&self)
        requires self.wf(),
        ensures exists|c: W| self.gamma(c),
    {
        if self.modulus.view() > 0 { lemma_small_mod(self.residue.view(), self.modulus.view()); }
        assert(self.gamma(self.residue));
    }

    proof fn lemma_least(&self, x: W)
        requires self.wf(), self.gamma(x),
        ensures self.residue.view() <= x.view(),
            self.modulus.view() > 0 ==> (x == self.residue || self.residue.view() + self.modulus.view() <= x.view()),
    {
        if self.modulus.view() > 0 {
            lemma_next(self.modulus.view(), self.residue.view(), x.view());
            W::lemma_view_injective(x, self.residue);
        }
    }

    proof fn lemma_second(&self) -> (s: W)
        requires self.wf(), self.modulus.view() > 0,
        ensures self.gamma(s), s.view() == self.residue.view() + self.modulus.view(),
    {
        let i = self.residue.view() + self.modulus.view();
        let s = W::from_int(i as int);
        W::lemma_from_int(i as int);
        lemma_small_mod(i, W::modulus());
        lemma_mod_add_multiples_vanish(self.residue.view() as int, self.modulus.view() as int);
        lemma_small_mod(self.residue.view(), self.modulus.view());
        s
    }

    pub proof fn lemma_canonical(a: &Self, b: &Self)
        requires a.wf(), b.wf(),
            forall|c: W| #![trigger a.gamma(c)] a.gamma(c) == b.gamma(c),
        ensures *a == *b,
    {
        // Equal sets have the same least member, hence the same residue.
        a.lemma_nonempty();
        b.lemma_nonempty();
        if a.modulus.view() > 0 { lemma_small_mod(a.residue.view(), a.modulus.view()); }
        if b.modulus.view() > 0 { lemma_small_mod(b.residue.view(), b.modulus.view()); }
        assert(a.gamma(a.residue) && b.gamma(b.residue));
        assert(a.gamma(b.residue) && b.gamma(a.residue));
        a.lemma_least(b.residue);
        b.lemma_least(a.residue);
        W::lemma_view_injective(a.residue, b.residue);
        // Each nonconstant has a second member. It rules out equality with
        // a singleton and bounds the other progression's step from above.
        // Applying this in both directions forces equal moduli, including top.
        if a.modulus.view() > 0 {
            let s = a.lemma_second();
            assert(b.gamma(s));
            b.lemma_least(s);
        }
        if b.modulus.view() > 0 {
            let s = b.lemma_second();
            assert(a.gamma(s));
            a.lemma_least(s);
        }
        W::lemma_view_injective(a.modulus, b.modulus);
    }
}
} // verus!
