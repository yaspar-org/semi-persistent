// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Signs of mathematical integers. Bottom is provided by the shared BotOr wrapper.
#![allow(unused_imports, unused_variables)]
use crate::facts_z::FactsZ;
use crate::ibig::IBig;
use crate::interval_z::{Hi, IntervalZ, Lo};
use crate::lattice::*;
use crate::reduce::Refine;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

#[derive(Copy, PartialEq, Eq, Debug)]
pub enum SignKind { Neg, Zero, Pos, NonPos, NonNeg, NonZero, Top }

#[derive(Copy, PartialEq, Eq)]
pub struct Sign {
    kind: SignKind,
}

impl Clone for Sign {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}
impl Clone for SignKind {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}

impl SignKind {
    pub open spec fn allows(self, x: int) -> bool {
        match self {
            Self::Neg => x < 0, Self::Zero => x == 0, Self::Pos => x > 0,
            Self::NonPos => x <= 0, Self::NonNeg => x >= 0,
            Self::NonZero => x != 0, Self::Top => true,
        }
    }
    fn categories(&self) -> (r: (bool, bool, bool))
        ensures r.0 == self.allows(-1), r.1 == self.allows(0), r.2 == self.allows(1),
    {
        match self {
            Self::Neg => (true,false,false), Self::Zero => (false,true,false),
            Self::Pos => (false,false,true), Self::NonPos => (true,true,false),
            Self::NonNeg => (false,true,true), Self::NonZero => (true,false,true),
            Self::Top => (true,true,true),
        }
    }
}

pub closed spec fn from_categories(n: bool, z: bool, p: bool) -> BotOr<Sign> {
    let kind = if n {
        if z { if p {SignKind::Top} else {SignKind::NonPos} }
        else { if p {SignKind::NonZero} else {SignKind::Neg} }
    } else {
        if z { if p {SignKind::NonNeg} else {SignKind::Zero} }
        else {SignKind::Pos}
    };
    if n || z || p {BotOr::Val(Sign {kind})} else {BotOr::Bot}
}

pub closed spec fn category(a: &BotOr<Sign>, x: int) -> bool {
    match a {BotOr::Bot => false, BotOr::Val(s) => s.kind.allows(x)}
}
pub closed spec fn union(a: &BotOr<Sign>, b: &BotOr<Sign>) -> BotOr<Sign> {
    from_categories(category(a,-1)||category(b,-1), category(a,0)||category(b,0), category(a,1)||category(b,1))
}
pub closed spec fn intersection(a: &BotOr<Sign>, b: &BotOr<Sign>) -> BotOr<Sign> {
    from_categories(category(a,-1)&&category(b,-1), category(a,0)&&category(b,0), category(a,1)&&category(b,1))
}
pub closed spec fn subset(a: &BotOr<Sign>, b: &BotOr<Sign>) -> bool {
    (!category(a,-1)||category(b,-1)) && (!category(a,0)||category(b,0)) && (!category(a,1)||category(b,1))
}

impl Sign {
    pub closed spec fn kind_of(&self) -> SignKind { self.kind }

    pub fn from_kind(kind: SignKind) -> (r: Self)
        ensures r.wf(), r.kind_of() == kind,
    { Self { kind } }

    pub fn kind(&self) -> (r: SignKind) ensures r == self.kind_of() { self.kind }

    fn build(n: bool, z: bool, p: bool) -> (r: BotOr<Self>)
        ensures r == from_categories(n,z,p),
    {
        if n {
            BotOr::Val(Self::from_kind(if z {if p {SignKind::Top}else{SignKind::NonPos}}
                else {if p {SignKind::NonZero}else{SignKind::Neg}}))
        } else if z {
            BotOr::Val(Self::from_kind(if p {SignKind::NonNeg}else{SignKind::Zero}))
        } else if p {BotOr::Val(Self::from_kind(SignKind::Pos))} else {BotOr::Bot}
    }

    /// Executable membership for a finite integer supplied by a caller.
    pub fn contains(&self, x: i128) -> (r: bool)
        ensures r == self.gamma(x as int),
    {
        match self.kind {
            SignKind::Neg => x < 0, SignKind::Zero => x == 0, SignKind::Pos => x > 0,
            SignKind::NonPos => x <= 0, SignKind::NonNeg => x >= 0,
            SignKind::NonZero => x != 0, SignKind::Top => true,
        }
    }
    pub fn from_value(x: i128) -> (r: Self)
        ensures r.wf(), r.gamma(x as int),
    { Self::from_kind(if x<0 {SignKind::Neg} else if x==0 {SignKind::Zero} else {SignKind::Pos}) }

    pub proof fn lattice_laws(a: BotOr<Self>, b: BotOr<Self>, c: BotOr<Self>)
        ensures
            union(&a,&b)==union(&b,&a), intersection(&a,&b)==intersection(&b,&a),
            union(&a,&a)==a, intersection(&a,&a)==a,
            union(&union(&a,&b),&c)==union(&a,&union(&b,&c)),
            intersection(&intersection(&a,&b),&c)==intersection(&a,&intersection(&b,&c)),
            union(&a,&intersection(&a,&b))==a, intersection(&a,&union(&a,&b))==a,
            union(&a,&BotOr::Bot)==a, intersection(&a,&BotOr::Bot)==BotOr::Bot,
            union(&a,&from_categories(true,true,true))==from_categories(true,true,true),
            intersection(&a,&from_categories(true,true,true))==a,
            subset(&a,&a), subset(&a,&union(&a,&b)), subset(&b,&union(&a,&b)),
            subset(&intersection(&a,&b),&a), subset(&intersection(&a,&b),&b),
            subset(&a,&b) && subset(&b,&a) ==> a==b,
            subset(&a,&b) && subset(&b,&c) ==> subset(&a,&c),
            subset(&a,&b) ==> subset(&union(&a,&c),&union(&b,&c)),
            subset(&a,&b) ==> subset(&intersection(&a,&c),&intersection(&b,&c)),
    {}

}

impl Domain for Sign {
    type C = int;
    open spec fn wf(&self) -> bool { true }
    closed spec fn gamma(&self, x: int) -> bool { self.kind.allows(x) }
    fn dup(&self) -> (r: Self) { *self }
    fn top() -> (r: Self) { Self::from_kind(SignKind::Top) }
    fn leq(&self, other: &Self) -> (r: bool)
        ensures r == (forall|x:int| #[trigger] self.gamma(x) ==> other.gamma(x)),
    {
        let (n,z,p)=self.kind.categories(); let (nn,zz,pp)=other.kind.categories();
        let r=(!n||nn)&&(!z||zz)&&(!p||pp);
        proof {
            if !r {
                let x:int=if n&&!nn {-1} else if z&&!zz {0} else {1};
                assert(self.gamma(x)&&!other.gamma(x));
            }
        }
        r
    }
    fn join(&self, other: &Self) -> (r: Self)
        ensures BotOr::Val(r)==union(&BotOr::Val(*self),&BotOr::Val(*other)),
            forall|x: int| #[trigger] r.gamma(x) == (self.gamma(x)||other.gamma(x)),
    {
        let (n,z,p)=self.kind.categories();let (nn,zz,pp)=other.kind.categories();
        match Self::build(n||nn,z||zz,p||pp) {
            BotOr::Val(r)=>r, BotOr::Bot=>{assert(false);Self::top()}
        }
    }
    fn meet(&self, other: &Self) -> (r: BotOr<Self>)
        ensures r==intersection(&BotOr::Val(*self),&BotOr::Val(*other)),
    {
        let (n,z,p)=self.kind.categories();let (nn,zz,pp)=other.kind.categories();
        Self::build(n&&nn,z&&zz,p&&pp)
    }
    /// Finite eight-state lattice: an ascending chain adds at most three signs.
    fn widen(&self, other: &Self) -> (r: Self) {self.join(other)}
}
impl Canonical for Sign {
    proof fn lemma_nonempty(&self) {
        let x:int=if self.kind.allows(-1) {-1} else if self.kind.allows(0) {0} else {1};
        assert(self.gamma(x));
    }
    proof fn lemma_canonical(a:&Self,b:&Self) {
        assert(a.gamma(-1)==b.gamma(-1));
        assert(a.gamma(0)==b.gamma(0));
        assert(a.gamma(1)==b.gamma(1));
    }
}

}

verus! {
impl Sign {
    fn nonempty(n:bool,z:bool,p:bool) -> (r:Self)
        requires n||z||p,
        ensures r.wf(), forall|x:int| #[trigger] r.gamma(x) == ((x<0&&n)||(x==0&&z)||(x>0&&p)),
    {
        match Self::build(n,z,p) { BotOr::Val(r)=>r, BotOr::Bot=>{assert(false);Self::top()} }
    }
    pub fn neg_int(&self)->(r:Self)
        ensures forall|x:int| self.gamma(x) ==> #[trigger] r.gamma(-x),
    { let(n,z,p)=self.kind.categories(); Self::nonempty(p,z,n) }
    pub fn add_int(&self,o:&Self)->(r:Self)
        ensures forall|x:int,y:int| self.gamma(x)&&o.gamma(y) ==> #[trigger] r.gamma(x+y),
    {
        let(n,z,p)=self.kind.categories();let(nn,zz,pp)=o.kind.categories();
        Self::nonempty(n||nn,(z&&zz)||(n&&pp)||(p&&nn),p||pp)
    }
    pub fn sub_int(&self,o:&Self)->(r:Self)
        ensures forall|x:int,y:int| self.gamma(x)&&o.gamma(y) ==> #[trigger] r.gamma(x-y),
    {
        let neg=o.neg_int();let r=self.add_int(&neg);
        proof { assert forall|x:int,y:int| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(x-y) by {
            assert(neg.gamma(-y));assert(r.gamma(x+(-y)));
        } }
        r
    }
    pub fn mul_int(&self,o:&Self)->(r:Self)
        ensures forall|x:int,y:int| self.gamma(x)&&o.gamma(y) ==> #[trigger] r.gamma(x*y),
    {
        let(n,z,p)=self.kind.categories();let(nn,zz,pp)=o.kind.categories();
        let r=Self::nonempty((n&&pp)||(p&&nn),z||zz,(n&&nn)||(p&&pp));
        proof { assert forall|x:int,y:int| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(x*y) by {
            assert((x<0&&y<0 ==> x*y>0)&&(x>0&&y>0 ==> x*y>0)
                &&(x<0&&y>0 ==> x*y<0)&&(x>0&&y<0 ==> x*y<0)) by(nonlinear_arith);
        } }
        r
    }
    /// The tight interval hull of this sign; NonZero cannot express its hole in FactsZ yet.
    fn interval_hull(&self)->(r:IntervalZ)
        ensures r.wf(), forall|x:int| self.gamma(x) ==> #[trigger] r.gamma(x),
    {
        let (lo,hi)=match self.kind {
            SignKind::Neg=>(Lo::NegInf,Hi::Fin(IBig::from_i64(-1))),
            SignKind::Pos=>(Lo::Fin(IBig::from_i64(1)),Hi::PosInf),
            SignKind::Zero=>(Lo::Fin(IBig::from_i64(0)),Hi::Fin(IBig::from_i64(0))),
            SignKind::NonNeg=>(Lo::Fin(IBig::from_i64(0)),Hi::PosInf),
            SignKind::NonPos=>(Lo::NegInf,Hi::Fin(IBig::from_i64(0))),
            _=>(Lo::NegInf,Hi::PosInf),
        };
        match IntervalZ::new(lo,hi) {Some(i)=>i,None=>{assert(false);IntervalZ::top()}}
    }
}
impl Refine for Sign {
    type F=FactsZ;
    fn to_channel(&self)->(r:BotOr<FactsZ>) {
        BotOr::Val(FactsZ::from_interval(self.interval_hull()))
    }
    fn refine(&self,f:&FactsZ)->(r:BotOr<Self>) {
        let i=f.interval();
        let ni=Self::from_kind(SignKind::Neg).interval_hull();
        let zi=Self::from_kind(SignKind::Zero).interval_hull();
        let pi=Self::from_kind(SignKind::Pos).interval_hull();
        let nm=i.meet_exact(&ni);let zm=i.meet_exact(&zi);let pm=i.meet_exact(&pi);
        let(n,z,p)=self.kind.categories();
        let r=Self::build(n && !matches!(nm,BotOr::Bot),z && !matches!(zm,BotOr::Bot),p && !matches!(pm,BotOr::Bot));
        proof { assert forall|x:int| self.gamma(x)&&f.gamma(x) implies #[trigger] r.gamma(x) by {
            assert(i.gamma(x));
            if x<0 {assert(ni.gamma(x));assert(nm.gamma(x));}
            if x==0 {assert(zi.gamma(x));assert(zm.gamma(x));}
            if x>0 {assert(pi.gamma(x));assert(pm.gamma(x));}
        } }
        r
    }
}
}
macro_rules! integer_transfers {
    ($s:ty) => {
        verus! {
            impl Arith<$s> for Sign {
                fn add(&self,o:&Self)->(r:Self) {self.add_int(o)}
                fn sub(&self,o:&Self)->(r:Self) {self.sub_int(o)}
                fn neg(&self)->(r:Self) {self.neg_int()}
            }
            impl Mul<$s> for Sign {fn mul(&self,o:&Self)->(r:Self) {self.mul_int(o)}}
        }
    };
}
integer_transfers!(Euclid);
integer_transfers!(Trunc);

verus! {
impl Sign {
    fn div_flag(d: &Self) -> (r: DivZero)
        ensures
            r is Never ==> !d.gamma(0),
            r is Always ==> forall|y: int| #[trigger] d.gamma(y) ==> y == 0,
            d.kind_of() != SignKind::Zero ==> !(r is Always),
    {
        match d.kind {
            SignKind::Neg | SignKind::Pos | SignKind::NonZero => DivZero::Never,
            SignKind::Zero => DivZero::Always,
            SignKind::NonPos | SignKind::NonNeg | SignKind::Top => DivZero::Maybe,
        }
    }

    proof fn lemma_trunc_div_sign(x: int, y: int)
        requires y != 0,
        ensures
            x == 0 ==> tdiv(x, y) == 0,
            x < 0 && y > 0 ==> tdiv(x, y) <= 0,
            x < 0 && y < 0 ==> tdiv(x, y) >= 0,
            x > 0 && y > 0 ==> tdiv(x, y) >= 0,
            x > 0 && y < 0 ==> tdiv(x, y) <= 0,
    {
        reveal(tdiv);
        reveal(iabs);
        assert(iabs(y) > 0) by {
            if y < 0 { assert(-y > 0); }
            else { assert(y > 0); }
        }
        lemma_div_pos_is_pos(iabs(x), iabs(y));
    }

    proof fn lemma_negative_one_div(d: int)
        requires d > 0,
        ensures (-1int) / d == -1,
    {
        lemma_fundamental_div_mod_converse(-1, d, -1, d - 1);
    }

    proof fn lemma_euclid_positive_divisor_sign(x: int, d: int)
        requires d > 0,
        ensures
            x < 0 ==> x / d < 0,
            x == 0 ==> x / d == 0,
            x > 0 ==> x / d >= 0,
    {
        if x < 0 {
            Self::lemma_negative_one_div(d);
            lemma_div_is_ordered(x, -1, d);
        } else if x == 0 {
            lemma_div_of0(d);
        } else {
            lemma_div_pos_is_pos(x, d);
        }
    }

    /// Euclidean division has the complementary sign behaviour for a negative
    /// divisor.  The remainder is always nonnegative, so a negative dividend
    /// produces a strictly positive quotient and a positive dividend produces
    /// a nonpositive quotient.
    proof fn lemma_euclid_negative_divisor_sign(x: int, d: int)
        requires d < 0,
        ensures
            x < 0 ==> x / d > 0,
            x == 0 ==> x / d == 0,
            x > 0 ==> x / d <= 0,
    {
        let q = x / d;
        let r = x % d;
        lemma_fundamental_div_mod(x, d);
        assert(x == d * q + r);
        assert(0 <= r);
        assert(r < -d);
        if x < 0 {
            if q <= 0 {
                lemma_mul_cancels_negatives(d, q);
                lemma_mul_nonnegative(-d, -q);
                assert(d * q >= 0);
                assert(d * q + r >= 0) by {
                    assert(d * q >= 0);
                    assert(r >= 0);
                }
                assert(x >= 0);
            }
        } else if x == 0 {
            lemma_div_of0(d);
        } else if q > 0 {
            lemma_mul_increases(q, -d);
            lemma_mul_unary_negation(-d, q);
            assert(d * q <= d);
            assert(d + r < d + (-d));
            assert(d + (-d) == 0);
            assert(d + r < 0);
            assert(d * q + r <= d + r) by {
                assert(d * q <= d);
            }
            assert(d * q + r < 0);
            assert(x < 0);
        }
    }

    /// Verus integer remainder is Euclidean, including for a negative divisor.
    proof fn lemma_euclid_rem_nonnegative(x: int, d: int)
        requires d != 0,
        ensures 0 <= x % d,
    {
        if d > 0 {
            lemma_mod_bound(x, d);
        } else {
            lemma_fundamental_div_mod(x, d);
            assert(0 <= x % d);
        }
    }

    /// A truncated remainder has the sign of its dividend.  Re-expressing it
    /// as the Euclidean remainder of the absolute values gives the required
    /// bound in all four sign combinations of dividend and divisor.
    proof fn lemma_trunc_rem_sign(x: int, d: int)
        requires d != 0,
        ensures
            x < 0 ==> trem(x, d) <= 0,
            x == 0 ==> trem(x, d) == 0,
            x > 0 ==> trem(x, d) >= 0,
    {
        reveal(trem);
        reveal(tdiv);
        reveal(iabs);
        if x > 0 {
            if d > 0 {
                lemma_fundamental_div_mod(x, d);
                lemma_mod_bound(x, d);
                assert(trem(x, d) == x - d * (x / d));
                assert(trem(x, d) == x % d);
            } else {
                let ad = -d;
                lemma_fundamental_div_mod(x, ad);
                lemma_mod_bound(x, ad);
                assert(tdiv(x, d) == -(x / ad));
                lemma_mul_unary_negation(d, x / ad);
                assert(trem(x, d) == x - d * tdiv(x, d));
                assert(d == -ad);
                assert(trem(x, d) == x - d * (-(x / ad)));
                assert(d * (x / ad) == -(ad * (x / ad)));
                assert(d * (-(x / ad)) == -(d * (x / ad)));
                assert(d * (-(x / ad)) == ad * (x / ad));
                assert(trem(x, d) == x - ad * (x / ad));
                assert(trem(x, d) == x % ad);
            }
        } else if x < 0 {
            let ax = -x;
            if d > 0 {
                lemma_fundamental_div_mod(ax, d);
                lemma_mod_bound(ax, d);
                assert(tdiv(x, d) == -(ax / d));
                lemma_mul_unary_negation(d, ax / d);
                assert(trem(x, d) == x - d * tdiv(x, d));
                assert(trem(x, d) == -ax - d * (-(ax / d)));
                assert(d * (-(ax / d)) == -(d * (ax / d)));
                assert(trem(x, d) == -ax + d * (ax / d));
                assert(trem(x, d) == -(ax - d * (ax / d)));
                assert(trem(x, d) == -(ax % d));
            } else {
                let ad = -d;
                lemma_fundamental_div_mod(ax, ad);
                lemma_mod_bound(ax, ad);
                assert(tdiv(x, d) == ax / ad);
                assert(trem(x, d) == x - d * tdiv(x, d));
                assert(d == -ad);
                assert(trem(x, d) == -ax - (-ad) * (ax / ad));
                lemma_mul_unary_negation(ad, ax / ad);
                assert((-ad) * (ax / ad) == -(ad * (ax / ad)));
                assert(trem(x, d) == -ax + ad * (ax / ad));
                assert(trem(x, d) == -(ax - ad * (ax / ad)));
                assert(trem(x, d) == -(ax % ad));
            }
        } else {
            lemma_div_of0(d);
            assert(tdiv(x, d) == 0);
            assert(trem(x, d) == x - d * 0);
            assert(x == 0);
            assert(trem(x, d) == 0);
        }
    }


}

impl DivRem<Euclid> for Sign {
    fn contains_zero(&self) -> (b: bool) {
        matches!(self.kind, SignKind::Zero | SignKind::NonPos | SignKind::NonNeg | SignKind::Top)
    }
    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        match d.kind {
            SignKind::Zero => (BotOr::Bot, DivZero::Always),
            _ => {
                let (xn, xz, xp) = self.kind.categories();
                let (dn, _, dp) = d.kind.categories();
                // Unlike truncated division, a negative numerator divided by a
                // positive denominator is never zero under Euclidean division.
                let q = Self::nonempty(
                    (xn && dp) || (xp && dn),
                    xz || xp,
                    (xn && dn) || (xp && dp),
                );
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) && y != 0
                            implies #[trigger] q.gamma(x / y) by {
                        if y > 0 {
                            Self::lemma_euclid_positive_divisor_sign(x, y);
                        } else {
                            Self::lemma_euclid_negative_divisor_sign(x, y);
                        }
                    }
                }
                (BotOr::Val(q), Self::div_flag(d))
            }
        }
    }
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        match d.kind {
            SignKind::Zero => (BotOr::Bot, DivZero::Always),
            _ => match self.kind {
            SignKind::Zero => {
                let q = Self::from_kind(SignKind::Zero);
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) && y != 0
                            implies #[trigger] q.gamma(x % y) by {
                        assert(self.kind.allows(x) == (x == 0));
                        assert(self.gamma(x) == self.kind.allows(x));
                        assert(x == 0);
                        assert((0int) % y == 0);
                    }
                }
                (BotOr::Val(q), Self::div_flag(d))
            }
            _ => {
                let q = Self::from_kind(SignKind::NonNeg);
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) && y != 0
                            implies #[trigger] q.gamma(x % y) by {
                        Self::lemma_euclid_rem_nonnegative(x, y);
                    }
                }
                (BotOr::Val(q), Self::div_flag(d))
            }
            }
        }
    }
}

impl DivRem<Trunc> for Sign {
    fn contains_zero(&self) -> (b: bool) {
        matches!(self.kind, SignKind::Zero | SignKind::NonPos | SignKind::NonNeg | SignKind::Top)
    }
    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        match d.kind {
            SignKind::Zero => (BotOr::Bot, DivZero::Always),
            _ => {
                let (xn, xz, xp) = self.kind.categories();
                let (dn, _, dp) = d.kind.categories();
                let q = Self::build(
                    (xn && dp) || (xp && dn),
                    xz || ((xn || xp) && (dn || dp)),
                    (xn && dn) || (xp && dp),
                );
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) && y != 0
                            implies #[trigger] q.gamma(tdiv(x, y)) by {
                        Self::lemma_trunc_div_sign(x, y);
                    }
                }
                (q, Self::div_flag(d))
            }
        }
    }
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        match d.kind {
            SignKind::Zero => (BotOr::Bot, DivZero::Always),
            _ => {
                let (xn, _, xp) = self.kind.categories();
                // A nonzero dividend may still divide evenly, hence zero is
                // always retained alongside the possible dividend signs.
                let q = Self::nonempty(xn, true, xp);
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) && y != 0
                            implies #[trigger] q.gamma(trem(x, y)) by {
                        Self::lemma_trunc_rem_sign(x, y);
                        if x < 0 {
                            assert(xn);
                        } else if x > 0 {
                            assert(xp);
                        }
                    }
                }
                (BotOr::Val(q), Self::div_flag(d))
            }
        }
    }
}
}
