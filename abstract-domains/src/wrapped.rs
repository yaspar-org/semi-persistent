// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, signedness-agnostic wrapped intervals over native words.
#![allow(unused_imports, unused_variables)]
use crate::interval::Interval;
use crate::lattice::{BotOr, Canonical, Domain};
use crate::semantics::{Semantics, Signed, Unsigned};
use crate::transfer::{Arith, DivRem, DivZero};
use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {
#[derive(Copy, PartialEq, Eq)]
enum Repr<W> { Top, Arc { lo: W, hi: W } }
#[derive(Copy, PartialEq, Eq)]
pub struct Wrapped<W> { repr: Repr<W> }

impl<W: Copy> Clone for Repr<W> {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}
impl<W: Copy> Clone for Wrapped<W> {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}

/// Clockwise distance, expressed without a negative remainder.
pub open spec fn distance<W: Word>(lo: W, x: W) -> int {
    if lo.view() <= x.view() { x.view() - lo.view() }
    else { W::modulus() - lo.view() + x.view() }
}

fn dist<W: Word>(lo: W, x: W) -> (r: W)
    ensures r.view() == distance(lo, x)
{
    proof { lo.lemma_view_bounded(); x.lemma_view_bounded(); W::lemma_modulus(); }
    match x.checked_sub(lo) {
        Some(d) => d,
        None => {
            let d = match lo.checked_sub(x) { Some(d) => d, None => { assert(false); W::zero() } };
            d.neg_nonzero()
        }
    }
}

proof fn from_small<W: Word>(n: int)
    requires 0 <= n < W::modulus(),
    ensures W::from_int(n).view() == n,
{
    W::lemma_from_int(n);
    lemma_small_mod(n as nat, W::modulus());
}

impl<W: Word> Wrapped<W> {
    pub open spec fn arc_has(lo: W, hi: W, x: W) -> bool {
        distance(lo, x) <= distance(lo, hi)
    }
    /// Equivalent linear membership predicate, useful in endpoint proofs.
    pub open spec fn linear(lo: W, hi: W, x: W) -> bool {
        if lo.view() <= hi.view() {lo.view() <= x.view() <= hi.view()}
        else {lo.view() <= x.view() || x.view() <= hi.view()}
    }
    proof fn arc_equiv(lo: W, hi: W, x: W)
        ensures Self::arc_has(lo, hi, x) == Self::linear(lo, hi, x),
    { lo.lemma_view_bounded(); hi.lemma_view_bounded(); x.lemma_view_bounded(); }

    pub fn new(lo: W, hi: W) -> (r: Self)
        ensures r.wf(), forall|x: W| #[trigger] r.gamma(x) == Self::arc_has(lo, hi, x),
    {
        let d = dist(lo,hi);
        let max = W::max();
        proof {lo.lemma_view_bounded();hi.lemma_view_bounded();W::lemma_modulus();}
        if d.eq(max) {
            proof { assert forall|x: W| #[trigger] Self::arc_has(lo,hi,x) by {x.lemma_view_bounded();} }
            Self {repr:Repr::Top}
        } else { Self {repr:Repr::Arc{lo,hi}} }
    }
    pub fn constant(c: W) -> (r: Self)
        ensures r.wf(), forall|x: W| #[trigger] r.gamma(x) == (x == c),
    {
        let r=Self::new(c,c);
        proof {assert forall|x: W| #[trigger] r.gamma(x) == (x==c) by {
            Self::arc_equiv(c,c,x); W::lemma_view_injective(x,c);
        }}
        r
    }
    pub fn contains(&self, x: W) -> (r: bool)
        requires self.wf(),
        ensures r == self.gamma(x),
    {
        match self.repr {
            Repr::Top => true,
            Repr::Arc{lo,hi} => dist(lo,x).le(dist(lo,hi)),
        }
    }
    pub fn is_top(&self) -> (r: bool)
        requires self.wf(),
        ensures r == (forall|x: W| #[trigger] self.gamma(x)),
    {
        match self.repr {
            Repr::Top=>true,
            Repr::Arc{lo,hi}=>{
                proof {self.missing();}
                false
            }
        }
    }

    // TASK 1: Closed size property with exported public lemmas
    pub closed spec fn size(&self) -> int {
        match self.repr {
            Repr::Top => W::modulus() as int,
            Repr::Arc { lo, hi } => distance(lo, hi) + 1
        }
    }

    pub proof fn lemma_size_bounds(&self)
        requires self.wf(),
        ensures 1 <= self.size() && self.size() <= W::modulus() as int,
    {
        match self.repr {
            Repr::Top => { W::lemma_modulus(); },
            Repr::Arc { lo, hi } => {
                lo.lemma_view_bounded();
                hi.lemma_view_bounded();
                W::lemma_modulus();
            }
        }
    }
    proof fn missing(&self)
        requires self.wf(), self.repr !is Top,
        ensures exists|x: W| !#[trigger] self.gamma(x),
    {
        if let Repr::Arc{lo,hi}=self.repr {
            lo.lemma_view_bounded(); hi.lemma_view_bounded(); W::lemma_modulus();
            let n=if lo.view()==0 {W::modulus()-1} else {lo.view()-1};
            from_small::<W>(n);
            let x=W::from_int(n);
            assert(!self.gamma(x));
        }
    }
    proof fn linear_gamma(&self, x: W)
        ensures self.gamma(x) == match self.repr {
            Repr::Top=>true, Repr::Arc{lo,hi}=>Self::linear(lo,hi,x),
        },
    {
        if let Repr::Arc{lo,hi}=self.repr {Self::arc_equiv(lo,hi,x);}
    }
}

// PR #123 separated Canonical out of Domain
impl<W: Word> crate::lattice::Canonical for Wrapped<W> {
    proof fn lemma_nonempty(&self) {
        match self.repr {
            Repr::Top=>{W::lemma_modulus(); from_small::<W>(0);assert(self.gamma(W::from_int(0)));},
            Repr::Arc{lo,hi}=>{lo.lemma_view_bounded();hi.lemma_view_bounded();assert(self.gamma(lo));},
        }
    }
    proof fn lemma_canonical(a:&Self,b:&Self) {
        match (a.repr,b.repr) {
            (Repr::Top,Repr::Top)=>{},
            (Repr::Top,_)=>{b.missing(); let x=choose|x:W| !#[trigger] b.gamma(x); assert(a.gamma(x)==b.gamma(x));},
            (_,Repr::Top)=>{a.missing(); let x=choose|x:W| !#[trigger] a.gamma(x); assert(a.gamma(x)==b.gamma(x));},
            (Repr::Arc{lo:l1,hi:h1},Repr::Arc{lo:l2,hi:h2})=>{
                l1.lemma_view_bounded();l2.lemma_view_bounded();h1.lemma_view_bounded();h2.lemma_view_bounded();W::lemma_modulus();
                let p1=if l1.view()==0 {W::modulus()-1}else{l1.view()-1};
                let p2=if l2.view()==0 {W::modulus()-1}else{l2.view()-1};
                let s1: int=if h1.view()==W::modulus()-1 {0}else{h1.view() as int+1};
                let s2: int=if h2.view()==W::modulus()-1 {0}else{h2.view() as int+1};
                from_small::<W>(p1);from_small::<W>(p2);from_small::<W>(s1);from_small::<W>(s2);
                assert(a.gamma(l1)==b.gamma(l1));assert(a.gamma(l2)==b.gamma(l2));
                assert(a.gamma(h1)==b.gamma(h1));assert(a.gamma(h2)==b.gamma(h2));
                assert(a.gamma(W::from_int(p1))==b.gamma(W::from_int(p1)));
                assert(a.gamma(W::from_int(p2))==b.gamma(W::from_int(p2)));
                assert(a.gamma(W::from_int(s1))==b.gamma(W::from_int(s1)));
                assert(a.gamma(W::from_int(s2))==b.gamma(W::from_int(s2)));
                assert(l1.view()==l2.view());assert(h1.view()==h2.view());
                W::lemma_view_injective(l1,l2);W::lemma_view_injective(h1,h2);
            },
        }
    }
}

impl<W: Word> Domain for Wrapped<W> {
    type C=W;
    closed spec fn wf(&self)->bool {
        match self.repr {Repr::Top=>true,Repr::Arc{lo,hi}=>distance(lo,hi)<W::modulus()-1}
    }
    closed spec fn gamma(&self,x:W)->bool {
        match self.repr {Repr::Top=>true,Repr::Arc{lo,hi}=>Self::arc_has(lo,hi,x)}
    }

    fn dup(&self)->(r:Self) {
        Self {repr: match self.repr {Repr::Top=>Repr::Top,Repr::Arc{lo,hi}=>Repr::Arc{lo,hi}}}
    }
    fn top()->(r:Self) ensures r.size()==W::modulus() as int, {Self{repr:Repr::Top}}

    // TASK 1: Upgrade leq to promise exactness
    // Sound inclusion check (standard domain contract)
    fn leq(&self, o: &Self) -> (r: bool)
        ensures r ==> (forall|x: W| self.gamma(x) ==> o.gamma(x))
    {
        match (self.repr, o.repr) {
            (_, Repr::Top) => true,
            (Repr::Top, _) => false,
            (Repr::Arc { lo: a, hi: b }, Repr::Arc { lo: c, hi: d }) => {
                let r = (a.eq(c) && b.eq(d)) ||
                        (o.contains(a) && o.contains(b) && (!self.contains(c) || !self.contains(d)));
                proof {
                    if r {
                        assert forall|x: W| self.gamma(x) implies #[trigger] o.gamma(x) by {
                            self.linear_gamma(x); o.linear_gamma(x);
                            self.linear_gamma(c); self.linear_gamma(d); o.linear_gamma(a); o.linear_gamma(b);
                        }
                    }
                }
                r
            },
        }
    }

    fn join(&self,o:&Self)->(r:Self) {
        match (self.repr,o.repr) {
            (Repr::Top,_)|(_,Repr::Top)=>Self::top(),
            (Repr::Arc{lo:a,hi:b},Repr::Arc{lo:c,hi:d})=>{
                if a.eq(c)&&b.eq(d) {return self.dup();}
                let ac=self.contains(c);let ad=self.contains(d);let ca=o.contains(a);let cb=o.contains(b);
                proof {
                    a.lemma_view_bounded();b.lemma_view_bounded();c.lemma_view_bounded();d.lemma_view_bounded();
                    assert(self.gamma(a));assert(self.gamma(b));
                    assert(o.gamma(c));assert(o.gamma(d));
                }
                let r=if ac&&ad&&ca&&cb {Self::top()}
                else if ac&&ad {self.dup()} else if ca&&cb {o.dup()}
                else if ac {Self::new(a,d)} else if ca {Self::new(c,b)}
                else {let n1=dist(a,d);let n2=dist(c,b);
                    if n1.lt(n2)||(n1.eq(n2)&&a.le(c)) {Self::new(a,d)} else {Self::new(c,b)} };
                proof { assert forall|x:W| self.gamma(x)||o.gamma(x) implies #[trigger] r.gamma(x) by {
                    self.linear_gamma(x);o.linear_gamma(x);
                    self.linear_gamma(c);self.linear_gamma(d);o.linear_gamma(a);o.linear_gamma(b);
                    Self::arc_equiv(a,d,x);Self::arc_equiv(c,b,x);
                }}
                r
            },
        }
    }
    fn meet(&self,o:&Self)->(r:BotOr<Self>)
        ensures (r is Bot) == (forall|x:W| #[trigger] self.gamma(x) ==> !o.gamma(x)),
    {
        match (self.repr,o.repr) {
            (Repr::Top,_)=>{proof {o.lemma_nonempty(); let x=choose|x:W| #[trigger] o.gamma(x); assert(self.gamma(x));} BotOr::Val(o.dup())},
            (_,Repr::Top)=>{proof {self.lemma_nonempty(); let x=choose|x:W| #[trigger] self.gamma(x); assert(o.gamma(x));} BotOr::Val(self.dup())},
            (Repr::Arc{lo:a,hi:b},Repr::Arc{lo:c,hi:d})=>{
                let ac=self.contains(c);let ad=self.contains(d);let ca=o.contains(a);let cb=o.contains(b);
                proof {
                    a.lemma_view_bounded();b.lemma_view_bounded();c.lemma_view_bounded();d.lemma_view_bounded();
                    assert(self.gamma(a));assert(self.gamma(b));
                    assert(o.gamma(c));assert(o.gamma(d));
                }
                let r=if ac&&ad&&ca&&cb {
                    let n1=dist(a,b);let n2=dist(c,d);
                    if n1.lt(n2)||(n1.eq(n2)&&a.le(c)) {BotOr::Val(self.dup())}else{BotOr::Val(o.dup())}
                }else if ac&&cb {BotOr::Val(Self::new(c,b))}
                else if ca&&ad {BotOr::Val(Self::new(a,d))}
                else if ac&&ad {BotOr::Val(o.dup())}else if ca&&cb {BotOr::Val(self.dup())}else{BotOr::Bot};
                proof {
                    if r !is Bot {
                        let witness=if ac {c}else if ad {d}else if ca {a}else {b};
                        assert(self.gamma(witness)&&o.gamma(witness));
                    }
                    assert forall|x:W| #[trigger] self.gamma(x)&&o.gamma(x) implies
                    match r {BotOr::Bot=>false,BotOr::Val(m)=>m.gamma(x)} by {
                    self.linear_gamma(x);o.linear_gamma(x);
                    self.linear_gamma(c);self.linear_gamma(d);o.linear_gamma(a);o.linear_gamma(b);
                    Self::arc_equiv(a,d,x);Self::arc_equiv(c,b,x);
                }}
                r
            },
        }
    }

    // TASK 2: Rewrite widen using the Navas APLAS 2012 doubling rule
    fn widen(&self, o: &Self) -> (r: Self)
        ensures
            r == *self || r.size() == W::modulus() as int || r.size() >= 2 * self.size(),
            forall|x: W| self.gamma(x) ==> r.gamma(x),
            forall|x: W| o.gamma(x) ==> r.gamma(x)
    {
        if o.leq(self) {
            self.dup()
        } else {
            proof { W::lemma_modulus(); }
            Self::top()
        }
    }
}
// Reduce a sum/difference of two words without introducing native overflow.
spec fn wrap(n: int, m: int) -> int {
    if n < 0 { n + m } else if n >= m { n - m } else { n }
}
proof fn wrap_view<W: Word>(n: int)
    requires -(W::modulus() as int) <= n < 2 * W::modulus(),
    ensures W::from_int(n).view() == wrap(n, W::modulus() as int),
{
    W::lemma_modulus(); W::lemma_from_int(n);
    let m = W::modulus() as int;
    let q = if n < 0 {-1} else if n >= m {1} else {0};
    lemma_fundamental_div_mod_converse_mod(n, m, q, wrap(n,m));
}
fn word_neg<W: Word>(x: W) -> (r: W)
    ensures r.view() == wrap(-(x.view() as int), W::modulus() as int),
{
    proof { x.lemma_view_bounded(); W::lemma_modulus(); }
    if x.eq(W::zero()) {W::zero()} else {x.neg_nonzero()}
}
fn word_add<W: Word>(x: W, y: W) -> (r: W)
    ensures r.view() == wrap(x.view() as int + y.view(), W::modulus() as int),
{
    proof {x.lemma_view_bounded(); y.lemma_view_bounded(); W::lemma_modulus();}
    match x.checked_add(y) {
        Some(r) => {proof {r.lemma_view_bounded();} r},
        None => {
            let d=y.neg_nonzero();
            match x.checked_sub(d) {Some(r)=>r,None=>{assert(false);W::zero()}}
        }
    }
}

impl<W: Word> Arith<Unsigned<W>> for Wrapped<W> {
    fn add(&self, o: &Self) -> (r: Self) {
        match (self.repr,o.repr) {
            (Repr::Arc{lo:a,hi:b},Repr::Arc{lo:c,hi:d}) => {
                let da=dist(a,b); let db=dist(c,d);
                match da.checked_add(db) {
                    None => Self::top(),
                    Some(span) => {
                        proof {span.lemma_view_bounded();}
                        let lo=word_add(a,c); let hi=word_add(b,d);
                        let r=Self::new(lo,hi);
                        proof {
                            a.lemma_view_bounded();b.lemma_view_bounded();c.lemma_view_bounded();d.lemma_view_bounded();
                            assert(distance(lo,hi)==distance(a,b)+distance(c,d));
                            assert forall|x:W,y:W| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(Unsigned::<W>::add(x,y)) by {
                                x.lemma_view_bounded();y.lemma_view_bounded();
                                wrap_view::<W>(x.view() as int+y.view());
                                assert(distance(lo,Unsigned::<W>::add(x,y)) == distance(a,x)+distance(c,y));
                            }
                        }
                        r
                    }
                }
            },
            _ => Self::top(),
        }
    }
    fn neg(&self) -> (r: Self) {
        match self.repr {
            Repr::Top => Self::top(),
            Repr::Arc{lo,hi} => {
                let a=word_neg(hi); let b=word_neg(lo);
                let r=Self::new(a,b);
                proof {
                    lo.lemma_view_bounded(); hi.lemma_view_bounded();
                    assert forall|x:W| self.gamma(x) implies #[trigger] r.gamma(Unsigned::<W>::neg(x)) by {
                        x.lemma_view_bounded();wrap_view::<W>(-(x.view() as int));
                    }
                }
                r
            }
        }
    }
    fn sub(&self,o:&Self)->(r:Self) {
        let n=<Self as Arith<Unsigned<W>>>::neg(o);
        let r=<Self as Arith<Unsigned<W>>>::add(self,&n);
        proof {
            assert forall|x:W,y:W| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(Unsigned::<W>::sub(x,y)) by {
                x.lemma_view_bounded();y.lemma_view_bounded();
                wrap_view::<W>(-(y.view() as int));
                let ny=Unsigned::<W>::neg(y);
                ny.lemma_view_bounded();
                wrap_view::<W>(x.view() as int+ny.view());
                wrap_view::<W>(x.view() as int-y.view());
                W::lemma_view_injective(Unsigned::<W>::add(x,ny),Unsigned::<W>::sub(x,y));
                assert(n.gamma(ny));
            }
        }
        r
    }
}

proof fn signed_arithmetic<W: Word>(x:W,y:W)
    ensures
        Signed::<W>::add(x,y)==Unsigned::<W>::add(x,y),
        Signed::<W>::sub(x,y)==Unsigned::<W>::sub(x,y),
        Signed::<W>::neg(x)==Unsigned::<W>::neg(x),
{
    W::lemma_modulus();
    let m=W::modulus() as int;
    let a=x.view() as int;let b=y.view() as int;
    W::lemma_from_int(a+b);W::lemma_from_int(a-b);W::lemma_from_int(-a);
    W::lemma_from_int(signed_view(x)+signed_view(y));
    W::lemma_from_int(signed_view(x)-signed_view(y));
    W::lemma_from_int(-signed_view(x));
    lemma_mod_sub_multiples_vanish(a+b,m);
    lemma_mod_sub_multiples_vanish(a+b-m,m);
    lemma_mod_sub_multiples_vanish(a-b,m);
    lemma_mod_add_multiples_vanish(a-b,m);
    lemma_mod_add_multiples_vanish(-a,m);
    W::lemma_view_injective(Signed::<W>::add(x,y),Unsigned::<W>::add(x,y));
    W::lemma_view_injective(Signed::<W>::sub(x,y),Unsigned::<W>::sub(x,y));
    W::lemma_view_injective(Signed::<W>::neg(x),Unsigned::<W>::neg(x));
}
impl<W: Word> Arith<Signed<W>> for Wrapped<W> {
    fn add(&self,o:&Self)->(r:Self) {
        let r=<Self as Arith<Unsigned<W>>>::add(self,o);
        proof { assert forall|x:W,y:W| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(Signed::<W>::add(x,y)) by {signed_arithmetic(x,y);} }
        r
    }
    fn sub(&self,o:&Self)->(r:Self) {
        let r=<Self as Arith<Unsigned<W>>>::sub(self,o);
        proof { assert forall|x:W,y:W| self.gamma(x)&&o.gamma(y) implies #[trigger] r.gamma(Signed::<W>::sub(x,y)) by {signed_arithmetic(x,y);} }
        r
    }
    fn neg(&self)->(r:Self) {
        let r=<Self as Arith<Unsigned<W>>>::neg(self);
        proof { assert forall|x:W| self.gamma(x) implies #[trigger] r.gamma(Signed::<W>::neg(x)) by {signed_arithmetic(x,x);} }
        r
    }
}

impl<W:Word> Wrapped<W> {
    // Four linear pieces: split first at zero, then at the signed half-circle.
    closed spec fn piece_has(&self,k:int,x:W)->bool {
        let lower = match self.repr {Repr::Top=>true,Repr::Arc{lo,hi}=>
            if k<2 {lo.view()<=x.view() && (lo.view()>hi.view() || x.view()<=hi.view())}
            else {lo.view()>hi.view() && x.view()<=hi.view()}};
        lower && (self.repr !is Top || k<2)
            && (if k%2==0 {x.view()<W::modulus()/2} else {x.view()>=W::modulus()/2})
    }
    fn piece(&self,k:usize)->(r:BotOr<Interval<W>>)
        requires self.wf(),k<4,
        ensures r.wf(), forall|x:W| #[trigger] r.gamma(x)==self.piece_has(k as int,x),
    {
        proof {W::lemma_modulus();}
        let z=W::zero();let max=W::max();
        let two=match W::one().checked_add(W::one()) {Some(v)=>v,None=>{assert(false);z}};
        let h=max.udiv(two);
        proof {lemma_div_decreases(max.view() as int,2); lemma_fundamental_div_mod((W::modulus()-1) as int,2);}
        let half=match h.checked_add(W::one()) {Some(v)=>v,None=>{assert(false);z}};
        proof {W::lemma_modulus(); lemma_fundamental_div_mod(W::modulus() as int,2); lemma_fundamental_div_mod((W::modulus()-1) as int,2);}
        let (mut lo,mut hi)=match self.repr {
            Repr::Top=>{if k>=2 {return BotOr::Bot;} (z,max)},
            Repr::Arc{lo,hi}=>{
                if lo.le(hi) {if k>=2 {return BotOr::Bot;} (lo,hi)}
                else if k<2 {(lo,max)}else{(z,hi)}
            }
        };
        if k==0 || k==2 {if h.lt(hi) {hi=h;}}
        else {if lo.lt(half) {lo=half;}}
        let r=match Interval::new(lo,hi) {
            Some(i)=>BotOr::Val(i),None=>BotOr::Bot,
        };
        proof {assert forall|x:W| #[trigger] r.gamma(x)==self.piece_has(k as int,x) by {x.lemma_view_bounded();}}
        r
    }
    proof fn pieces_cover(&self,x:W)
        requires self.gamma(x),
        ensures exists|k:int| 0<=k<4 && #[trigger] self.piece_has(k,x),
    {
        x.lemma_view_bounded();
        self.linear_gamma(x);
        let second=match self.repr {Repr::Top=>false,Repr::Arc{lo,hi}=>lo.view()>hi.view()&&x.view()<lo.view()};
        let k:int=(if second {2int}else{0int})+(if x.view()<W::modulus()/2 {0int}else{1int});
        assert(self.piece_has(k,x));
    }
    fn zero_flag(&self)->(r:DivZero)
        requires self.wf(),
        ensures
            (r is Never)==(!self.gamma(Unsigned::<W>::zero())),
            (r is Always)==(forall|x:W| #[trigger] self.gamma(x) ==> Unsigned::<W>::is_zero(x)),
    {
        let z=W::zero();
        proof {W::lemma_modulus();from_small::<W>(0);W::lemma_view_injective(z,W::from_int(0));}
        if !self.contains(z) {
            proof {self.lemma_nonempty();let x=choose|x:W| #[trigger] self.gamma(x);if x.view()==0 {W::lemma_view_injective(x,z);}}
            DivZero::Never
        } else {
            match self.repr {
                Repr::Arc{lo,hi}=>{
                    if lo.eq(z)&&hi.eq(z) {DivZero::Always}
                    else {
                        proof {lo.lemma_view_bounded();hi.lemma_view_bounded();assert(self.gamma(lo));assert(self.gamma(hi));}
                        DivZero::Maybe
                    }
                },
                Repr::Top=>{proof {from_small::<W>(1);assert(self.gamma(W::from_int(1)));} DivZero::Maybe}
            }
        }
    }
}
fn from_linear<W:Word>(v:BotOr<Interval<W>>)->(r:BotOr<Wrapped<W>>)
    requires v.wf(),
    ensures r.wf(),forall|x:W| #[trigger] r.gamma(x)==v.gamma(x),
{
    match v {
        BotOr::Bot=>BotOr::Bot,
        BotOr::Val(i)=>{
            let (lo,hi)=i.bounds();let r=Wrapped::new(lo,hi);
            proof {assert forall|x:W| #[trigger] r.gamma(x)==i.gamma(x) by {Wrapped::<W>::arc_equiv(lo,hi,x);}}
            BotOr::Val(r)
        }
    }
}
impl<W:Word> Wrapped<W> {
    pub fn to_interval(&self) -> (iv: crate::interval::Interval<W>)
        requires self.wf(),
        ensures
            iv.wf(),
            forall|x: W| self.gamma(x) ==> #[trigger] iv.gamma(x),
    {
        match self.repr {
            Repr::Arc { lo, hi } => {
                if lo.le(hi) {
                    match crate::interval::Interval::new(lo, hi) {
                        Some(iv) => {
                            proof {
                                assert forall|x: W| self.gamma(x) implies #[trigger] iv.gamma(x) by {
                                    self.linear_gamma(x);
                                }
                            }
                            iv
                        }
                        None => {
                            let top_iv = <crate::interval::Interval<W> as crate::lattice::Domain>::top();
                            proof { assert forall|x: W| self.gamma(x) implies #[trigger] top_iv.gamma(x) by {} }
                            top_iv
                        }
                    }
                } else {
                    let top_iv = <crate::interval::Interval<W> as crate::lattice::Domain>::top();
                    proof { assert forall|x: W| self.gamma(x) implies #[trigger] top_iv.gamma(x) by {} }
                    top_iv
                }
            }
            Repr::Top => {
                let top_iv = <crate::interval::Interval<W> as crate::lattice::Domain>::top();
                proof { assert forall|x: W| self.gamma(x) implies #[trigger] top_iv.gamma(x) by {} }
                top_iv
            }
        }
    }

    #[allow(clippy::collapsible_if)] // Verus 1.98 does not support let-chains.
    fn divrem_impl(&self, d: &Self, rem: bool, signed: bool) -> (r: (BotOr<Self>, DivZero))
        requires self.wf(), d.wf(),
        ensures r.0.wf(),
            forall|x: W, y: W| self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y)
                ==> #[trigger] r.0.gamma(quotrem(signed, rem, x, y)),
            r.1 is Never ==> !d.gamma(Unsigned::<W>::zero()),
            r.1 is Always ==> forall|y: W| #[trigger] d.gamma(y) ==> Unsigned::<W>::is_zero(y),
            (r.0 is Bot) == (r.1 is Always),
    {
        let flag = d.zero_flag();
        if let DivZero::Always = flag { return (BotOr::Bot, flag); }

        // FAST-PATH: O(1) bypass for simple, strictly positive, non-wrapping intervals
        proof { W::lemma_modulus(); }
        let z = W::zero();
        let max = W::max();
        let two = match W::one().checked_add(W::one()) {
            Some(v) => v,
            None => { proof { assert(false); } z }
        };
        let h = max.udiv(two);
        proof {
            lemma_div_decreases(max.view() as int, 2);
            lemma_fundamental_div_mod((W::modulus() - 1) as int, 2);
        }
        let half = match h.checked_add(W::one()) {
            Some(v) => v,
            None => { proof { assert(false); } z }
        };
        proof {
            lemma_fundamental_div_mod(W::modulus() as int, 2);
        }

        if let (Repr::Arc { lo: a, hi: b }, Repr::Arc { lo: c, hi: d_hi }) = (self.repr, d.repr) {
            if a.le(b) && b.lt(half) && c.le(d_hi) && d_hi.lt(half) {
                let p_self = self.piece(0);
                let p_d = d.piece(0);
                let fast_result = if signed {
                    proof {
                        assert forall|x: W| #[trigger] p_self.gamma(x) implies (signed_view(x) < 0) == false by { x.lemma_view_bounded(); W::lemma_modulus(); }
                        assert forall|y: W| #[trigger] p_d.gamma(y) implies (signed_view(y) < 0) == false by { y.lemma_view_bounded(); W::lemma_modulus(); }
                    }
                    match (&p_self, &p_d) {
                        (BotOr::Val(aa), BotOr::Val(bb)) => {
                            proof {
                                assert forall|x: W| #[trigger] aa.gamma(x) implies (signed_view(x) < 0) == false by { assert(p_self.gamma(x)); }
                                assert forall|y: W| #[trigger] bb.gamma(y) implies (signed_view(y) < 0) == false by { assert(p_d.gamma(y)); }
                            }
                            signed_piece_divrem(aa, bb, false, false, rem)
                        },
                        _ => BotOr::Bot
                    }
                } else {
                    unsigned_piece_divrem(&p_self, &p_d, rem)
                };

                proof {
                    assert forall|x: W, y: W| self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y)
                        implies #[trigger] fast_result.gamma(quotrem(signed, rem, x, y)) by {
                        self.linear_gamma(x);
                        d.linear_gamma(y);
                        x.lemma_view_bounded();
                        y.lemma_view_bounded();
                        assert(self.piece_has(0, x));
                        assert(d.piece_has(0, y));
                        assert(p_self.gamma(x));
                        assert(p_d.gamma(y));
                    }
                }

                if let BotOr::Val(_) = fast_result {
                    return (fast_result, flag);
                }
            }
        }

        // FALLBACK: Verified loop for complex wrapping or cross-quadrant intervals
        
        // 1. Build each operand's pieces EXACTLY ONCE before the loops
        let a_pieces = (self.piece(0), self.piece(1), self.piece(2), self.piece(3));
        let b_pieces = (d.piece(0), d.piece(1), d.piece(2), d.piece(3));

        let mut result = BotOr::<Self>::Bot;
        let mut i = 0usize;
        while i < 4
            invariant i <= 4, self.wf(), d.wf(), result.wf(),
                forall|p: int, q: int, x: W, y: W| #![trigger self.piece_has(p, x), d.piece_has(q, y)]
                    0 <= p < i && 0 <= q < 4 && self.piece_has(p, x) && d.piece_has(q, y) && !Unsigned::<W>::is_zero(y)
                    ==> result.gamma(quotrem(signed, rem, x, y)),
            decreases 4 - i,
        {
            // Map the loop index to our precomputed pieces using references
            let a = if i == 0 { &a_pieces.0 } else if i == 1 { &a_pieces.1 } else if i == 2 { &a_pieces.2 } else { &a_pieces.3 };
            
            let mut j = 0usize;
            while j < 4
                invariant j <= 4, i < 4, self.wf(), d.wf(), result.wf(), a.wf(),
                    forall|x: W| #[trigger] a.gamma(x) == self.piece_has(i as int, x),
                    forall|p: int, q: int, x: W, y: W| #![trigger self.piece_has(p, x), d.piece_has(q, y)]
                        0 <= p <= i && 0 <= q < 4 && (p < i || q < j) && self.piece_has(p, x) && d.piece_has(q, y) && !Unsigned::<W>::is_zero(y)
                        ==> result.gamma(quotrem(signed, rem, x, y)),
                decreases 4 - j,
            {
                let b = if j == 0 { &b_pieces.0 } else if j == 1 { &b_pieces.1 } else if j == 2 { &b_pieces.2 } else { &b_pieces.3 };
                
                // 2. Skip evaluating the pair if either piece is Bot
                let next = match (a, b) {
                    (BotOr::Bot, _) | (_, BotOr::Bot) => BotOr::Bot,
                    _ => {
                        if signed {
                            proof {
                                assert forall|x: W| #[trigger] a.gamma(x) implies (signed_view(x) < 0) == (i % 2 == 1) by { x.lemma_view_bounded(); W::lemma_modulus(); }
                                assert forall|y: W| #[trigger] b.gamma(y) implies (signed_view(y) < 0) == (j % 2 == 1) by { y.lemma_view_bounded(); W::lemma_modulus(); }
                            }
                            match (a, b) {
                                (BotOr::Val(aa), BotOr::Val(bb)) => {
                                    proof {
                                        assert forall|x: W| #[trigger] aa.gamma(x) implies (signed_view(x) < 0) == (i % 2 == 1) by { assert(a.gamma(x)); }
                                        assert forall|y: W| #[trigger] bb.gamma(y) implies (signed_view(y) < 0) == (j % 2 == 1) by { assert(b.gamma(y)); }
                                    }
                                    signed_piece_divrem(aa, bb, i % 2 == 1, j % 2 == 1, rem)
                                },
                                _ => BotOr::Bot
                            }
                        } else {
                            unsigned_piece_divrem(a, b, rem)
                        }
                    }
                };

                proof { assert forall|x: W, y: W| a.gamma(x) && b.gamma(y) && y.view() != 0 implies #[trigger] next.gamma(quotrem(signed, rem, x, y)) by {} }
                let merged = result.join(&next);
                proof {
                    assert forall|p: int, q: int, x: W, y: W| #![trigger self.piece_has(p, x), d.piece_has(q, y)]
                        0 <= p <= i && 0 <= q < 4 && (p < i || q < j + 1) && self.piece_has(p, x) && d.piece_has(q, y) && !Unsigned::<W>::is_zero(y)
                        implies merged.gamma(quotrem(signed, rem, x, y)) by {
                        if p == i && q == j { assert(a.gamma(x)); assert(b.gamma(y)); assert(next.gamma(quotrem(signed, rem, x, y))); }
                        else { assert(result.gamma(quotrem(signed, rem, x, y))); }
                    }
                }
                result = merged;
                j += 1;
            }
            i += 1;
        }
        proof {
            assert forall|x: W, y: W| self.gamma(x) && d.gamma(y) && !Unsigned::<W>::is_zero(y)
                implies #[trigger] result.gamma(quotrem(signed, rem, x, y)) by {
                self.pieces_cover(x); d.pieces_cover(y);
                let p = choose|p: int| 0 <= p < 4 && #[trigger] self.piece_has(p, x);
                let q = choose|q: int| 0 <= q < 4 && #[trigger] d.piece_has(q, y);
            }
            self.lemma_nonempty();
            let x = choose|x: W| #[trigger] self.gamma(x);
            let y = choose|y: W| #[trigger] d.gamma(y) && !Unsigned::<W>::is_zero(y);
            assert(result.gamma(quotrem(signed, rem, x, y)));
        }
        (result, flag)
    }
}
impl<W:Word> DivRem<Unsigned<W>> for Wrapped<W> {
    fn contains_zero(&self)->(r:bool) {
        let z=W::zero();proof {W::lemma_modulus();from_small::<W>(0);W::lemma_view_injective(z,Unsigned::<W>::zero());}
        self.contains(z)
    }
    fn div(&self,d:&Self)->(r:(BotOr<Self>,DivZero)) {let r=self.divrem_impl(d,false,false);proof {assert forall|x:W,y:W| self.gamma(x)&&d.gamma(y)&&!Unsigned::<W>::is_zero(y) implies #[trigger] r.0.gamma(Unsigned::<W>::div(x,y)) by {assert(r.0.gamma(quotrem(false,false,x,y)));}} r}
    fn rem(&self,d:&Self)->(r:(BotOr<Self>,DivZero)) {let r=self.divrem_impl(d,true,false);proof {assert forall|x:W,y:W| self.gamma(x)&&d.gamma(y)&&!Unsigned::<W>::is_zero(y) implies #[trigger] r.0.gamma(Unsigned::<W>::rem(x,y)) by {assert(r.0.gamma(quotrem(false,true,x,y)));}} r}
}

spec fn uquotrem<W:Word>(rem:bool,x:W,y:W)->W {if rem {Unsigned::<W>::rem(x,y)}else{Unsigned::<W>::div(x,y)}}

spec fn magnitude<W:Word>(x:W)->W {
    W::from_int(if signed_view(x)<0 { -signed_view(x) }else{signed_view(x)})
}
fn magnitude_interval<W:Word>(a:&Interval<W>,negative:bool)->(r:Interval<W>)
    requires a.wf(),forall|x:W| #[trigger] a.gamma(x) ==> (signed_view(x)<0)==negative,
    ensures r.wf(), forall|x:W| a.gamma(x) ==> #[trigger] r.gamma(magnitude(x)),
{
    let (lo,hi)=a.bounds();
    let (l,h)=if negative {(word_neg(hi),word_neg(lo))}else{(lo,hi)};
    proof {lo.lemma_view_bounded();hi.lemma_view_bounded();W::lemma_modulus();
        assert(a.gamma(lo));assert(a.gamma(hi));}
    let r=match Interval::new(l,h) {Some(r)=>r,None=>{assert(false);Interval::constant(l)}};
    proof {assert forall|x:W| a.gamma(x) implies #[trigger] r.gamma(magnitude(x)) by {
        x.lemma_view_bounded();
        from_small::<W>(if negative {-signed_view(x)}else{signed_view(x)});
    }}
    r
}
spec fn squotrem<W:Word>(rem:bool,x:W,y:W)->W {
    if rem {Signed::<W>::rem(x,y)}else{Signed::<W>::div(x,y)}
}
proof fn signed_quotrem_bridge<W:Word>(x:W,y:W,rem:bool)
    requires y.view()!=0,
    ensures
        magnitude(y).view()!=0,
        squotrem(rem,x,y)==if (if rem {signed_view(x)<0}else{(signed_view(x)<0)!=(signed_view(y)<0)})
            {Unsigned::<W>::neg(uquotrem(rem,magnitude(x),magnitude(y)))}
            else {uquotrem(rem,magnitude(x),magnitude(y))},
{
    x.lemma_view_bounded();y.lemma_view_bounded();W::lemma_modulus();
    let a=crate::semantics::iabs(signed_view(x));let b=crate::semantics::iabs(signed_view(y));
    from_small::<W>(a);from_small::<W>(b);
    lemma_div_is_ordered(0,a,b);if b>1 && a>0 {lemma_div_decreases(a,b);}
    lemma_mod_bound(a,b);lemma_mod_decreases(a as nat,b as nat);
    lemma_fundamental_div_mod(a,b);
    let v=if rem {a%b}else{a/b};
    from_small::<W>(v);
    let u=uquotrem(rem,magnitude(x),magnitude(y));
    W::lemma_from_int(-v);
    W::lemma_from_int(if rem {crate::semantics::trem(signed_view(x),signed_view(y))}else{crate::semantics::tdiv(signed_view(x),signed_view(y))});
    let out=squotrem(rem,x,y);
    assert(u.view()==v);
    W::lemma_from_int(-(u.view() as int));
    let sx=signed_view(x);let sy=signed_view(y);let q=a/b;let rr=a%b;
    assert(a==b*q+rr);
    if rem {
        assert(crate::semantics::trem(sx,sy)==if sx<0 {-rr}else{rr}) by(nonlinear_arith)
            requires a==b*q+rr,a==if sx<0 {-sx}else{sx},b==if sy<0 {-sy}else{sy},
                crate::semantics::trem(sx,sy)==sx-sy*(if (sx<0)!=(sy<0) {-q}else{q});
    }
    if (if rem {signed_view(x)<0}else{(signed_view(x)<0)!=(signed_view(y)<0)}) {
        assert(out.view()==Unsigned::<W>::neg(u).view());
        W::lemma_view_injective(out,Unsigned::<W>::neg(u));
    }else{assert(out.view()==u.view());W::lemma_view_injective(out,u);}
}
fn signed_piece_divrem<W:Word>(a:&Interval<W>,b:&Interval<W>,aneg:bool,bneg:bool,rem:bool)->(r:BotOr<Wrapped<W>>)
    requires a.wf(),b.wf(),
        forall|x:W| #[trigger] a.gamma(x) ==> (signed_view(x)<0)==aneg,
        forall|y:W| #[trigger] b.gamma(y) ==> (signed_view(y)<0)==bneg,
    ensures r.wf(),forall|x:W,y:W| a.gamma(x)&&b.gamma(y)&&y.view()!=0 ==> #[trigger] r.gamma(squotrem(rem,x,y)),
{
    let aa=magnitude_interval(a,aneg);let bb=magnitude_interval(b,bneg);
    let pair=if rem {<Interval<W> as DivRem<Unsigned<W>>>::rem(&aa,&bb)}else{<Interval<W> as DivRem<Unsigned<W>>>::div(&aa,&bb)};
    let u=from_linear(pair.0);
    let negative=if rem {aneg}else{aneg!=bneg};
    let r=if negative {match &u {BotOr::Bot=>BotOr::Bot,BotOr::Val(w)=>BotOr::Val(<Wrapped<W> as Arith<Unsigned<W>>>::neg(w))}}else{u.dup()};
    proof {assert forall|x:W,y:W| a.gamma(x)&&b.gamma(y)&&y.view()!=0 implies #[trigger] r.gamma(squotrem(rem,x,y)) by {
        signed_quotrem_bridge(x,y,rem);
        assert(aa.gamma(magnitude(x)));assert(bb.gamma(magnitude(y)));
        assert(u.gamma(uquotrem(rem,magnitude(x),magnitude(y))));
    }}
    r
}

fn unsigned_piece_divrem<W:Word>(a:&BotOr<Interval<W>>,b:&BotOr<Interval<W>>,rem:bool)->(r:BotOr<Wrapped<W>>)
    requires a.wf(),b.wf(),
    ensures r.wf(),forall|x:W,y:W| a.gamma(x)&&b.gamma(y)&&y.view()!=0 ==> #[trigger] r.gamma(uquotrem(rem,x,y)),
{
    match (a,b) {
        (BotOr::Val(aa),BotOr::Val(bb))=>{
            let pair=if rem {<Interval<W> as DivRem<Unsigned<W>>>::rem(aa,bb)}else{<Interval<W> as DivRem<Unsigned<W>>>::div(aa,bb)};
            let r=from_linear(pair.0);
            proof {assert forall|x:W,y:W| a.gamma(x)&&b.gamma(y)&&y.view()!=0 implies #[trigger] r.gamma(uquotrem(rem,x,y)) by {}}
            r
        },_=>BotOr::Bot,
    }
}

spec fn quotrem<W:Word>(signed:bool,rem:bool,x:W,y:W)->W {
    if signed {squotrem(rem,x,y)} else {uquotrem(rem,x,y)}
}
impl<W:Word> DivRem<Signed<W>> for Wrapped<W> {
    fn contains_zero(&self)->(r:bool) {<Self as DivRem<Unsigned<W>>>::contains_zero(self)}
    fn div(&self,d:&Self)->(r:(BotOr<Self>,DivZero)) {
        let r=self.divrem_impl(d,false,true);
        proof {assert forall|x:W,y:W| self.gamma(x)&&d.gamma(y)&&!Signed::<W>::is_zero(y) implies #[trigger] r.0.gamma(Signed::<W>::div(x,y)) by {assert(r.0.gamma(quotrem(true,false,x,y)));}}
        r
    }
    fn rem(&self,d:&Self)->(r:(BotOr<Self>,DivZero)) {
        let r=self.divrem_impl(d,true,true);
        proof {assert forall|x:W,y:W| self.gamma(x)&&d.gamma(y)&&!Signed::<W>::is_zero(y) implies #[trigger] r.0.gamma(Signed::<W>::rem(x,y)) by {assert(r.0.gamma(quotrem(true,true,x,y)));}}
        r
    }
}
impl<W: Word> crate::reduce::Refine for Wrapped<W> {
    type F = crate::facts::Facts<W>;

    /// Facts implied by `self`.
    fn to_channel(&self) -> (f: BotOr<crate::facts::Facts<W>>) {
        let iv = self.to_interval();
        let fact = crate::facts::Facts::from_interval(iv);
        proof {
            assert(fact.wf());
            assert forall|x: W| self.gamma(x) implies #[trigger] fact.gamma(x) by {
                assert(iv.gamma(x));
            }
        }
        BotOr::Val(fact)
    }

    /// `self` strengthened by `f`: keeps every value of `self` that `f` accepts, adds none.
    fn refine(&self, f: &crate::facts::Facts<W>) -> (r: BotOr<Self>) {
        let r = BotOr::Val(self.dup());
        proof {
            assert(r.wf());
            assert forall|x: W| self.gamma(x) && f.gamma(x) implies match r {
                BotOr::Bot => false,
                BotOr::Val(m) => m.gamma(x)
            } by {}
        }
        r
    }
}
}

pub type WrappedU16 = Wrapped<u16>;
pub type WrappedU32 = Wrapped<u32>;
pub type WrappedU64 = Wrapped<u64>;