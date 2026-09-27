// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, signedness-agnostic wrapped intervals over native words.
#![allow(unused_imports, unused_variables)]
use crate::lattice::{BotOr, Domain};
use crate::word::Word;
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
    pub closed spec fn size(&self) -> int {
        match self.repr {Repr::Top=>W::modulus() as int,Repr::Arc{lo,hi}=>distance(lo,hi)+1}
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

impl<W: Word> Domain for Wrapped<W> {
    type C=W;
    closed spec fn wf(&self)->bool {
        match self.repr {Repr::Top=>true,Repr::Arc{lo,hi}=>distance(lo,hi)<W::modulus()-1}
    }
    closed spec fn gamma(&self,x:W)->bool {
        match self.repr {Repr::Top=>true,Repr::Arc{lo,hi}=>Self::arc_has(lo,hi,x)}
    }
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
    fn dup(&self)->(r:Self) {
        Self {repr: match self.repr {Repr::Top=>Repr::Top,Repr::Arc{lo,hi}=>Repr::Arc{lo,hi}}}
    }
    fn top()->(r:Self) {Self{repr:Repr::Top}}
    fn leq(&self,o:&Self)->(r:bool) {
        match (self.repr,o.repr) {
            (_,Repr::Top)=>true,(Repr::Top,_)=>false,
            (Repr::Arc{lo:a,hi:b},Repr::Arc{lo:c,hi:d})=>{
                let r=(a.eq(c)&&b.eq(d)) || (o.contains(a)&&o.contains(b)&&(!self.contains(c)||!self.contains(d)));
                proof {assert forall|x:W| r && self.gamma(x) implies #[trigger] o.gamma(x) by {
                    self.linear_gamma(x);o.linear_gamma(x);
                    self.linear_gamma(c);self.linear_gamma(d);o.linear_gamma(a);o.linear_gamma(b);
                }}
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
    /// Stable inputs remain unchanged. Otherwise accept a cover only after
    /// cardinality at least doubles; smaller growth jumps to Top.
    /// Measure: remaining doublings before the finite universe is reached.
    fn widen(&self,o:&Self)->(r:Self) {
        if o.leq(self) {self.dup()} else {
            let j=self.join(o);
            match (self.repr,j.repr) {
                (Repr::Arc{lo:a,hi:b},Repr::Arc{lo:c,hi:d})=>{
                    let old=dist(a,b);let new=dist(c,d);
                    match old.checked_add(old) {
                        Some(twice)=>match twice.checked_add(W::one()) {
                            Some(threshold)=>if threshold.le(new) {j}else{Self::top()},
                            None=>Self::top(),
                        },
                        None=>Self::top(),
                    }
                },
                _=>Self::top(),
            }
        }
    }
}
}
