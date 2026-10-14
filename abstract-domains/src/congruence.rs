// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, nonempty congruences over unsigned finite-width words.
//! `Domain` provides exact refinement/meet, least-upper-bound join, and
//! join-based widening. `Arith<Unsigned<W>>` provides sound add/sub/neg.
//! Empty intersections use external `BotOr`; all values remain canonical.
use crate::arithmetic::*;
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::Arith;
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

/// Reduce two integers from the same wrapping segment without changing their
/// congruence. The common offset is ghost-only, including at 128 bits.
proof fn same_segment<W: Word>(x: int, y: int, d: nat, offset: int)
    requires d > 0, x % (d as int) == y % (d as int),
        0 <= x + offset < W::modulus(), 0 <= y + offset < W::modulus(),
        offset == 0 || offset == W::modulus() as int || offset == -(W::modulus() as int),
    ensures W::from_int(x).view() % d == W::from_int(y).view() % d,
{
    W::lemma_modulus();
    W::lemma_from_int(x);
    W::lemma_from_int(y);
    let n = W::modulus() as int;
    let k = if offset == 0 { 0 } else if offset == n { 1 } else { -1 };
    congruence_shift(x + offset, x, n, k);
    congruence_shift(y + offset, y, n, k);
    vstd::arithmetic::div_mod::lemma_small_mod((x + offset) as nat, W::modulus());
    vstd::arithmetic::div_mod::lemma_small_mod((y + offset) as nat, W::modulus());
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, offset, d as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(y, offset, d as int);
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

    /// Decide exact containment over representable words.
    pub fn refines(&self, other: &Self) -> (result: bool)
        requires self.wf(), other.wf(),
        ensures result == (forall|x: W| #[trigger] self.has(x) ==> other.has(x)),
    {
        proof { self.residue_member(); assert(self.has(self.residue)); }
        if !other.contains(self.residue) { return false; }
        if self.modulus.eq(W::zero()) { return true; }
        let ghost second = self.lemma_second();
        proof { assert(self.has(second)); }
        if other.modulus.eq(W::zero()) {
            proof { assert(!other.has(second)); }
            return false;
        }
        let divides = self.modulus.urem(other.modulus).eq(W::zero());
        proof {
            if divides {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self.modulus.view() as int, other.modulus.view() as int);
                assert forall|x: W| #[trigger] self.has(x) implies other.has(x) by {
                    self.member_decomposition(x);
                    let m = self.modulus.view() as int;
                    let n = other.modulus.view() as int;
                    let r = self.residue.view() as int;
                    let q = x.view() as int / m;
                    let d = m / n;
                    assert(x.view() as int == r + n * (d * q)) by (nonlinear_arith)
                        requires x.view() as int == r + m * q, m == n * d;
                    congruence_shift(x.view() as int, r, n, d * q);
                }
            } else {
                if other.has(second) {
                    vstd::arithmetic::div_mod::lemma_mod_equivalence(second.view() as int, self.residue.view() as int,
                        other.modulus.view() as int);
                    assert(false);
                }
                assert(!other.has(second));
            }
        }
        divides
    }

    /// A divisor of the canonical stride preserves every member's residue.
    pub proof fn member_mod_divisor(&self, x: W, d: nat)
        requires self.wf(), self.has(x), d > 0,
            self.modulus().view() > 0 ==> self.modulus().view() % d == 0,
        ensures x.view() % d == self.residue().view() % d,
    {
        if self.modulus.view() > 0 {
            normalize_preserves_divisor(x.view(), self.modulus.view(), d);
        }
    }

    /// Semantic containment, including the singleton cases.
    pub open spec fn subset_of(&self, other: &Self) -> bool {
        forall|x: W| #[trigger] self.has(x) ==> other.has(x)
    }

    /// The first two members force every containing class to divide the stride.
    proof fn subset_stride(&self, other: &Self)
        requires self.wf(), other.wf(), self.subset_of(other),
        ensures other.has(self.residue()),
            other.modulus().view() == 0 ==> self.modulus().view() == 0,
            other.modulus().view() > 0 ==> self.modulus().view() % other.modulus().view() == 0,
    {
        self.residue_member();
        assert(self.has(self.residue));
        assert(other.has(self.residue));
        if self.modulus.view() > 0 {
            let second = self.lemma_second();
            assert(self.has(second));
            assert(other.has(second));
            if other.modulus.view() > 0 {
                vstd::arithmetic::div_mod::lemma_mod_equivalence(second.view() as int, self.residue.view() as int,
                    other.modulus.view() as int);
                assert(self.modulus.view() % other.modulus.view() == 0);
            }
        } else if other.modulus.view() > 0 {
            vstd::arithmetic::div_mod::lemma_small_mod(0, other.modulus.view());
        }
    }

    /// Least upper bound using the GCD of strides and residue distance.
    pub fn join(&self, other: &Self) -> (r: Self)
        requires self.wf(), other.wf(),
        ensures r.wf(),
            forall|x: W| #[trigger] self.has(x) ==> r.has(x),
            forall|x: W| #[trigger] other.has(x) ==> r.has(x),
            forall|c: Self| #[trigger] c.wf() && self.subset_of(&c) && other.subset_of(&c)
                ==> r.subset_of(&c),
    {
        let ghost a = self.residue.view();
        let ghost b = other.residue.view();
        let delta = if other.residue.le(self.residue) {
            self.residue.wrapping_sub(other.residue)
        } else {
            other.residue.wrapping_sub(self.residue)
        };
        proof {
            self.residue.lemma_view_bounded();
            other.residue.lemma_view_bounded();
            if a >= b {
                W::lemma_from_int(a - b);
                vstd::arithmetic::div_mod::lemma_small_mod((a - b) as nat, W::modulus());
            } else {
                W::lemma_from_int(b - a);
                vstd::arithmetic::div_mod::lemma_small_mod((b - a) as nat, W::modulus());
            }
        }
        let stride_gcd = gcd(self.modulus, other.modulus);
        let modulus = gcd(stride_gcd, delta);
        if modulus.eq(W::zero()) {
            proof { W::lemma_view_injective(self.residue, other.residue); }
            let r = Self::constant(self.residue);
            proof {
                assert forall|c: Self| #[trigger] c.wf() && self.subset_of(&c) && other.subset_of(&c)
                    implies r.subset_of(&c) by {
                    self.residue_member();
                    assert(self.has(self.residue));
                    assert(c.has(self.residue));
                }
            }
            return r;
        }
        proof {
            lemma_gcd_divisor_iff(self.modulus.view(), other.modulus.view(), modulus.view());
            if a >= b {
                vstd::arithmetic::div_mod::lemma_mod_equivalence(a as int, b as int, modulus.view() as int);
            } else {
                vstd::arithmetic::div_mod::lemma_mod_equivalence(b as int, a as int, modulus.view() as int);
            }
        }
        let r = Self::new(modulus, self.residue);
        proof {
            assert forall|x: W| #[trigger] self.has(x) implies r.has(x) by {
                self.member_mod_divisor(x, modulus.view());
            }
            assert forall|x: W| #[trigger] other.has(x) implies r.has(x) by {
                other.member_mod_divisor(x, modulus.view());
            }
            assert forall|c: Self| #[trigger] c.wf() && self.subset_of(&c) && other.subset_of(&c)
                implies r.subset_of(&c) by {
                self.subset_stride(&c);
                other.subset_stride(&c);
                let d = c.modulus.view();
                if d == 0 {
                    assert(self.residue == c.residue && other.residue == c.residue);
                    assert(false);
                } else {
                    if a >= b { vstd::arithmetic::div_mod::lemma_mod_equivalence(a as int, b as int, d as int); }
                    else { vstd::arithmetic::div_mod::lemma_mod_equivalence(b as int, a as int, d as int); }
                    lemma_gcd_divisor(self.modulus.view(), other.modulus.view(), d);
                    lemma_gcd_divisor(stride_gcd.view(), delta.view(), d);
                    assert forall|x: W| #[trigger] r.has(x) implies c.has(x) by {
                        normalize_preserves_divisor(x.view(), modulus.view(), d);
                        normalize_preserves_divisor(self.residue.view(), modulus.view(), d);
                    }
                }
            }
        }
        r
    }

    /// Greatest represented word, used to decide whether any sum can wrap.
    pub fn max_member(&self) -> (last: W)
        requires self.wf(),
        ensures self.has(last),
            forall|x: W| #[trigger] self.has(x) ==> x.view() <= last.view(),
    {
        if self.modulus.eq(W::zero()) { return self.residue; }
        let max = W::max();
        let distance = max.wrapping_sub(self.residue);
        let remainder = distance.urem(self.modulus);
        let last = max.wrapping_sub(remainder);
        proof {
            self.residue.lemma_view_bounded();
            W::lemma_from_int(max.view() - self.residue.view());
            vstd::arithmetic::div_mod::lemma_small_mod((max.view() - self.residue.view()) as nat, W::modulus());
            vstd::arithmetic::div_mod::lemma_mod_decreases(distance.view(), self.modulus.view());
            W::lemma_from_int(max.view() - remainder.view());
            vstd::arithmetic::div_mod::lemma_small_mod((max.view() - remainder.view()) as nat, W::modulus());
            vstd::arithmetic::div_mod::lemma_mod_bound(distance.view() as int, self.modulus.view() as int);
            vstd::arithmetic::div_mod::lemma_mod_decreases(distance.view(), self.modulus.view());
            vstd::arithmetic::div_mod::lemma_mod_equivalence(distance.view() as int, remainder.view() as int, self.modulus.view() as int);
            vstd::arithmetic::div_mod::lemma_small_mod(remainder.view(), self.modulus.view());
            vstd::arithmetic::div_mod::lemma_mod_equivalence(last.view() as int, self.residue.view() as int,
                self.modulus.view() as int);
            vstd::arithmetic::div_mod::lemma_small_mod(self.residue.view(), self.modulus.view());
            assert forall|x: W| #[trigger] self.has(x) implies x.view() <= last.view() by {
                x.lemma_view_bounded();
                if x.view() > last.view() {
                    vstd::arithmetic::div_mod::lemma_mod_equivalence(x.view() as int, last.view() as int,
                        self.modulus.view() as int);
                    vstd::arithmetic::div_mod::lemma_small_mod((x.view() - last.view()) as nat, self.modulus.view());
                    assert(false);
                }
            }
        }
        last
    }

    /// Preserve the stride when every sum is in one wrapping segment.
    /// Mixed wrapping conservatively includes the machine modulus in the GCD.
    pub fn add(&self, other: &Self) -> (r: Self)
        requires self.wf(), other.wf(),
        ensures r.wf(),
            forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
                ==> r.has(Unsigned::<W>::add(x, y)),
            self.modulus().view() == 0 && other.modulus().view() == 0 ==>
                r.modulus().view() == 0 && r.residue() == Unsigned::<W>::add(self.residue(), other.residue()),
    {
        let stride = gcd(self.modulus, other.modulus);
        let sum = self.residue.wrapping_add(other.residue);
        if stride.eq(W::zero()) { return Self::constant(sum); }
        let upper_a = self.max_member();
        let upper_b = other.max_member();
        let no_wrap = match upper_a.checked_add(upper_b) {
            Some(_total) => { proof { _total.lemma_view_bounded(); } true },
            None => false,
        };
        let all_wrap = self.residue.checked_add(other.residue).is_none();
        let modulus = if no_wrap || all_wrap { stride } else { gcd_machine_modulus(stride) };
        let r = Self::new(modulus, sum);
        proof {
            W::lemma_modulus();
            upper_a.lemma_view_bounded();
            upper_b.lemma_view_bounded();
            self.residue_member();
            other.residue_member();
            lemma_gcd_divisor_iff(self.modulus.view(), other.modulus.view(), modulus.view());
            let base = self.residue.view() as int + other.residue.view();
            W::lemma_from_int(base);
            assert forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
                implies r.has(Unsigned::<W>::add(x, y)) by {
                self.member_decomposition(x);
                other.member_decomposition(y);
                self.member_mod_divisor(x, modulus.view());
                other.member_mod_divisor(y, modulus.view());
                let value = x.view() as int + y.view();
                vstd::arithmetic::div_mod::lemma_add_mod_noop(x.view() as int, y.view() as int, modulus.view() as int);
                vstd::arithmetic::div_mod::lemma_add_mod_noop(self.residue.view() as int, other.residue.view() as int, modulus.view() as int);
                if no_wrap || all_wrap {
                    let offset = if no_wrap { 0 } else { -(W::modulus() as int) };
                    same_segment::<W>(value, base, modulus.view(), offset);
                } else {
                    lemma_wrapping_congruence::<W>(stride.view(), base);
                    lemma_wrapping_congruence::<W>(stride.view(), value);
                    W::lemma_from_int(value);
                }
            }
        }
        r
    }

    /// Negation is direct subtraction from zero. In particular, a class that
    /// excludes zero keeps its stride because all differences wrap together.
    pub fn neg(&self) -> (r: Self)
        requires self.wf(),
        ensures r.wf(), forall|x: W| #[trigger] self.has(x)
            ==> r.has(Unsigned::<W>::neg(x)),
            self.modulus().view() == 0 ==> r.modulus().view() == 0
                && r.residue() == Unsigned::<W>::neg(self.residue()),
    {
        let zero = W::zero();
        let c = Self::constant(zero);
        let r = c.sub(self);
        proof {
            assert(c.has(zero));
            assert forall|x: W| #[trigger] self.has(x) implies r.has(Unsigned::<W>::neg(x)) by {
                assert(r.has(Unsigned::<W>::sub(zero, x)));
            }
        }
        r
    }

    /// Direct subtraction: one stride GCD and no intermediate abstract negation.
    pub fn sub(&self, other: &Self) -> (r: Self)
        requires self.wf(), other.wf(),
        ensures r.wf(), forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
            ==> r.has(Unsigned::<W>::sub(x, y)),
            self.modulus().view() == 0 && other.modulus().view() == 0 ==>
                r.modulus().view() == 0 && r.residue() == Unsigned::<W>::sub(self.residue(), other.residue()),
    {
        let difference = self.residue.wrapping_sub(other.residue);
        let stride = gcd(self.modulus, other.modulus);
        if stride.eq(W::zero()) { return Self::constant(difference); }
        let upper_a = self.max_member();
        let upper_b = other.max_member();
        let no_wrap = self.residue.checked_sub(upper_b).is_some();
        let all_wrap = upper_a.checked_sub(other.residue).is_none();
        let modulus = if no_wrap || all_wrap { stride } else { gcd_machine_modulus(stride) };
        let r = Self::new(modulus, difference);
        proof {
            W::lemma_modulus();
            upper_a.lemma_view_bounded();
            upper_b.lemma_view_bounded();
            self.residue_member();
            other.residue_member();
            lemma_gcd_divisor_iff(self.modulus.view(), other.modulus.view(), modulus.view());
            let base = self.residue.view() as int - other.residue.view();
            W::lemma_from_int(base);
            assert forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
                implies r.has(Unsigned::<W>::sub(x, y)) by {
                self.member_decomposition(x);
                other.member_decomposition(y);
                self.member_mod_divisor(x, modulus.view());
                other.member_mod_divisor(y, modulus.view());
                let value = x.view() as int - y.view();
                vstd::arithmetic::div_mod::lemma_sub_mod_noop(x.view() as int, y.view() as int, modulus.view() as int);
                vstd::arithmetic::div_mod::lemma_sub_mod_noop(self.residue.view() as int, other.residue.view() as int, modulus.view() as int);
                if no_wrap || all_wrap {
                    let offset = if no_wrap { 0 } else { W::modulus() as int };
                    same_segment::<W>(value, base, modulus.view(), offset);
                } else {
                    lemma_wrapping_congruence::<W>(stride.view(), base);
                    lemma_wrapping_congruence::<W>(stride.view(), value);
                    W::lemma_from_int(value);
                }
            }
        }
        r
    }

    /// Exact intersection, with emptiness outside the domain.
    pub fn meet(&self, other: &Self) -> (result: BotOr<Self>)
        requires self.wf(), other.wf(),
        ensures match result {
            BotOr::Val(r) => r.wf() && (forall|x: W| #[trigger] r.has(x)
                <==> self.has(x) && other.has(x)),
            BotOr::Bot => forall|x: W| #[trigger] self.has(x) ==> !other.has(x),
        },
    {
        if self.modulus.eq(W::zero()) {
            return if other.contains(self.residue) {
                BotOr::Val(*self)
            } else { BotOr::Bot };
        }
        if other.modulus.eq(W::zero()) {
            return if self.contains(other.residue) {
                BotOr::Val(*other)
            } else { BotOr::Bot };
        }
        proof {
            vstd::arithmetic::div_mod::lemma_small_mod(self.residue.view(), self.modulus.view());
            vstd::arithmetic::div_mod::lemma_small_mod(other.residue.view(), other.modulus.view());
        }
        let merged = crt_merge(self.modulus, self.residue, other.modulus, other.residue);
        match merged {
            CrtMergeResult::Class { modulus, residue } => {
                let r = Self::new(modulus, residue);
                proof {
                    vstd::arithmetic::div_mod::lemma_small_mod(residue.view(), modulus.view());
                    assert forall|x: W| #[trigger] r.has(x) <==> self.has(x) && other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Val(r)
            },
            CrtMergeResult::Singleton { value } => {
                let r = Self::constant(value);
                proof {
                    assert forall|x: W| #[trigger] r.has(x) <==> self.has(x) && other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Val(r)
            },
            CrtMergeResult::Empty => {
                proof {
                    assert forall|x: W| #[trigger] self.has(x) implies !other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Bot
            },
        }
    }

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

impl<W: Word> Domain for Congruence<W> {
    type C = W;
    open spec fn wf(&self) -> bool { Congruence::wf(self) }
    open spec fn gamma(&self, x: W) -> bool { Congruence::gamma(self, x) }
    fn dup(&self) -> (r: Self) { Self { modulus: self.modulus, residue: self.residue } }
    fn top() -> (r: Self) { Congruence::top() }
    fn leq(&self, o: &Self) -> (b: bool)
        ensures b == self.subset_of(o),
    {
        let b = self.refines(o);
        proof {
            assert forall|x: W| #[trigger] <Self as Domain>::gamma(self, x) && b
                implies <Self as Domain>::gamma(o, x) by {
                assert(self.has(x));
                assert(o.has(x));
            }
        }
        b
    }
    fn join(&self, o: &Self) -> (r: Self)
        ensures forall|c: Self| #[trigger] c.wf() && self.subset_of(&c) && o.subset_of(&c)
            ==> r.subset_of(&c),
    {
        let r = Congruence::join(self, o);
        proof {
            assert forall|x: W| self.gamma(x) || o.gamma(x)
                implies #[trigger] <Self as Domain>::gamma(&r, x) by {
                assert(self.has(x) || o.has(x));
                assert(r.has(x));
            }
        }
        r
    }
    fn meet(&self, o: &Self) -> (r: BotOr<Self>)
        ensures match r {
            BotOr::Bot => forall|x: W| #[trigger] self.has(x) ==> !o.has(x),
            BotOr::Val(v) => forall|x: W| #[trigger] v.has(x) <==> self.has(x) && o.has(x),
        },
    {
        let r = Congruence::meet(self, o);
        proof {
            match &r {
                BotOr::Bot => {
                    assert forall|x: W| #[trigger] <Self as Domain>::gamma(self, x)
                        implies !<Self as Domain>::gamma(o, x) by {
                        assert(self.has(x));
                    }
                },
                BotOr::Val(v) => {
                    assert forall|x: W| self.gamma(x) && o.gamma(x)
                        implies #[trigger] <Self as Domain>::gamma(v, x) by {
                        assert(v.has(x));
                    }
                },
            }
        }
        r
    }
    // This finite lattice needs no loss of precision to widen.
    fn widen(&self, o: &Self) -> (r: Self) {
        let r = Congruence::join(self, o);
        proof {
            assert forall|x: W| self.gamma(x) || o.gamma(x)
                implies #[trigger] <Self as Domain>::gamma(&r, x) by {
                assert(self.has(x) || o.has(x));
                assert(r.has(x));
            }
        }
        r
    }
}

impl<W: Word> Canonical for Congruence<W> {
    proof fn lemma_nonempty(&self) {
        self.residue_member();
        assert(<Self as Domain>::gamma(self, self.residue));
    }
    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert forall|x: W| #[trigger] a.gamma(x) == b.gamma(x) by {
            assert(<Self as Domain>::gamma(a, x) == <Self as Domain>::gamma(b, x));
        }
        Congruence::lemma_canonical(a, b);
    }
}

impl<W: Word> Arith<Unsigned<W>> for Congruence<W> {
    fn add(&self, o: &Self) -> (r: Self)
        ensures self.modulus().view() == 0 && o.modulus().view() == 0 ==>
            r.modulus().view() == 0 && r.residue() == Unsigned::<W>::add(self.residue(), o.residue()),
    {
        let r = Congruence::add(self, o);
        proof {
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y)
                implies #[trigger] <Self as Domain>::gamma(&r, Unsigned::<W>::add(x, y)) by {
                assert(self.has(x) && o.has(y));
                assert(r.has(Unsigned::<W>::add(x, y)));
            }
        }
        r
    }
    fn sub(&self, o: &Self) -> (r: Self)
        ensures self.modulus().view() == 0 && o.modulus().view() == 0 ==>
            r.modulus().view() == 0 && r.residue() == Unsigned::<W>::sub(self.residue(), o.residue()),
    {
        let r = Congruence::sub(self, o);
        proof {
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y)
                implies #[trigger] <Self as Domain>::gamma(&r, Unsigned::<W>::sub(x, y)) by {
                assert(self.has(x) && o.has(y));
                assert(r.has(Unsigned::<W>::sub(x, y)));
            }
        }
        r
    }
    fn neg(&self) -> (r: Self)
        ensures self.modulus().view() == 0 ==> r.modulus().view() == 0
            && r.residue() == Unsigned::<W>::neg(self.residue()),
    {
        let r = Congruence::neg(self);
        proof {
            assert forall|x: W| self.gamma(x)
                implies #[trigger] <Self as Domain>::gamma(&r, Unsigned::<W>::neg(x)) by {
                assert(self.has(x));
                assert(r.has(Unsigned::<W>::neg(x)));
            }
        }
        r
    }
}

} // verus!
