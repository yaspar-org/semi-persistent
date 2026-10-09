// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, nonempty congruences over unsigned finite-width words.
//! This semantic core intentionally does not implement `Domain`: its lattice
//! operations belong to the subsequent Congruence core change.
use crate::word::Word;
use vstd::prelude::*;

verus! {

/// `(0, r)` is a singleton; `(1, 0)` is top. Other canonical pairs
/// satisfy `r < m` and have a representable second member `r + m`.
/// Use `new` for raw pairs; fields cannot bypass normalization.
#[derive(Copy)]
pub struct Congruence<W> {
    modulus: W,
    residue: W,
}

// Verus cannot specify Rust's derived Clone for this generic type.
// Use the Copy implementation directly and expose its structural contract.
impl<W: Copy> Clone for Congruence<W> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    { *self }
}

/// Raw descriptions use a congruence class, even for an unreduced residue.
pub open spec fn raw_has<W: Word>(m: W, r: W, x: W) -> bool {
    if m.view() == 0 { x == r }
    else { x.view() % m.view() == r.view() % m.view() }
}

impl<W: Word> Congruence<W> {
    pub closed spec fn modulus(&self) -> W { self.modulus }
    pub closed spec fn residue(&self) -> W { self.residue }

    pub open spec fn wf(&self) -> bool {
        self.modulus().view() == 0 || (
            self.residue().view() < self.modulus().view()
            && self.residue().view() + self.modulus().view() < W::modulus())
    }

    /// Integer congruence restricted to the unsigned finite word range.
    /// Wrapping arithmetic can lose exactness: at u8, `(3, 0) + 1`
    /// contains both 0 (from 255) and 1, so its best congruence is Top.
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
            modulus.view() == 0 ==> r.modulus().view() == 0 && r.residue() == residue,
            modulus.view() > 0 ==> r.residue().view() == residue.view() % modulus.view(),
            modulus.view() > 0 && residue.view() % modulus.view() + modulus.view() < W::modulus()
                ==> r.modulus() == modulus,
            modulus.view() > 0 && residue.view() % modulus.view() + modulus.view() >= W::modulus()
                ==> r.modulus().view() == 0,
    {
        if modulus.eq(W::zero()) { Self::constant(residue) }
        else {
            let rem = residue.urem(modulus);
            proof { vstd::arithmetic::div_mod::lemma_mod_bound(residue.view() as int, modulus.view() as int); }
            match rem.checked_add(modulus) {
                Some(_second) => {
                    proof { _second.lemma_view_bounded(); }
                    Self { modulus, residue: rem }
                },
                None => {
                    let r = Self::constant(rem);
                    proof {
                        assert forall|x: W| #[trigger] r.gamma(x) <==> raw_has(modulus, residue, x) by {
                            x.lemma_view_bounded();
                            vstd::arithmetic::div_mod::lemma_small_mod(rem.view(), modulus.view());
                            if raw_has(modulus, residue, x) {
                                let raw = Self { modulus, residue: rem };
                                raw.lemma_next(x);
                                W::lemma_view_injective(x, rem);
                            }
                        }
                    }
                    r
                },
            }
        }
    }

    /// Recognize the canonical top in constant time.
    pub fn is_top(&self) -> (r: bool)
        requires self.wf(),
        ensures r == (self.modulus().view() == 1 && self.residue().view() == 0),
            r == (forall|x: W| #[trigger] self.gamma(x)),
    {
        let top = Self::top();
        self.same(&top)
    }

    /// Extract exactly the singleton classes.
    pub fn as_constant(&self) -> (r: Option<W>)
        requires self.wf(),
        ensures r.is_some() == (self.modulus().view() == 0),
            match r {
                Some(c) => c == self.residue() && (forall|x: W| #[trigger] self.gamma(x) <==> x == c),
                None => exists|x: W| #[trigger] self.gamma(x) && x != self.residue(),
            },
    {
        if self.modulus.eq(W::zero()) { Some(self.residue) }
        else {
            proof {
                self.residue_member();
                let s = self.lemma_second();
                assert(self.gamma(s) && s != self.residue());
            }
            None
        }
    }

    /// Canonical equality: two word comparisons, with no enumeration.
    pub fn same(&self, other: &Self) -> (r: bool)
        requires self.wf(), other.wf(),
        ensures r == (*self == *other),
            r == (forall|x: W| #[trigger] self.gamma(x) == other.gamma(x)),
    {
        proof {
            W::lemma_view_injective(self.modulus, other.modulus);
            W::lemma_view_injective(self.residue, other.residue);
            if forall|x: W| #[trigger] self.gamma(x) == other.gamma(x) {
                Self::lemma_canonical(self, other);
            }
        }
        self.modulus.eq(other.modulus) && self.residue.eq(other.residue)
    }

    /// Any later member is at least one modulus beyond the residue.
    /// Only reduction is required, so this also applies before singleton collapse.
    pub proof fn lemma_next(&self, x: W)
        requires self.modulus().view() > 0,
            self.residue().view() < self.modulus().view(), self.gamma(x),
        ensures self.residue().view() <= x.view(),
            x == self.residue() || self.residue().view() + self.modulus().view() <= x.view(),
    {
        let m = self.modulus().view();
        let r = self.residue().view();
        let v = x.view();
        vstd::arithmetic::div_mod::lemma_mod_decreases(v, m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int, m as int);
        assert(v == r || r + m <= v) by (nonlinear_arith)
            requires m > 0, v == m * (v / m) + r;
        W::lemma_view_injective(x, self.residue());
    }

    /// The canonical residue is always a member.
    pub proof fn residue_member(&self)
        requires self.wf(),
        ensures self.gamma(self.residue()),
    {
        if self.modulus.view() > 0 { vstd::arithmetic::div_mod::lemma_small_mod(self.residue.view(), self.modulus.view()); }
    }

    pub proof fn lemma_nonempty(&self)
        requires self.wf(),
        ensures exists|c: W| self.gamma(c),
    {
        self.residue_member();
    }

    /// Decompose a member into the least member plus a nonnegative step count.
    pub proof fn member_decomposition(&self, x: W)
        requires self.wf(), self.gamma(x),
        ensures self.residue().view() <= x.view(),
            self.modulus().view() == 0 ==> x == self.residue(),
            self.modulus().view() > 0 ==> (
                x.view() == self.residue().view() + self.modulus().view() * (x.view() / self.modulus().view())
                && (x == self.residue() || self.residue().view() + self.modulus().view() <= x.view())),
    {
        if self.modulus.view() > 0 {
            self.lemma_next(x);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x.view() as int, self.modulus.view() as int);
            W::lemma_view_injective(x, self.residue);
        }
    }

    /// Every canonical nonconstant has this representable second member.
    pub proof fn lemma_second(&self) -> (s: W)
        requires self.wf(), self.modulus().view() > 0,
        ensures self.gamma(s), s.view() == self.residue().view() + self.modulus().view(),
    {
        let i = self.residue.view() + self.modulus.view();
        let s = W::from_int(i as int);
        W::lemma_from_int(i as int);
        vstd::arithmetic::div_mod::lemma_small_mod(i, W::modulus());
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(self.residue.view() as int, self.modulus.view() as int);
        vstd::arithmetic::div_mod::lemma_small_mod(self.residue.view(), self.modulus.view());
        s
    }

    pub proof fn lemma_canonical(a: &Self, b: &Self)
        requires a.wf(), b.wf(),
            forall|c: W| #![trigger a.gamma(c)] a.gamma(c) == b.gamma(c),
        ensures *a == *b,
    {
        // Equal sets have the same least member, hence the same residue.
        a.residue_member();
        b.residue_member();
        assert(a.gamma(a.residue) && b.gamma(b.residue));
        assert(a.gamma(b.residue) && b.gamma(a.residue));
        a.member_decomposition(b.residue);
        b.member_decomposition(a.residue);
        W::lemma_view_injective(a.residue, b.residue);
        // Each nonconstant has a second member. It rules out equality with
        // a singleton and bounds the other progression's step from above.
        // Applying this in both directions forces equal moduli, including top.
        if a.modulus.view() > 0 {
            let s = a.lemma_second();
            assert(b.gamma(s));
            b.member_decomposition(s);
        }
        if b.modulus.view() > 0 {
            let s = b.lemma_second();
            assert(a.gamma(s));
            a.member_decomposition(s);
        }
        W::lemma_view_injective(a.modulus, b.modulus);
    }
}
} // verus!
