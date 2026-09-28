// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Signed machine-word signs. Bottom is provided by the shared BotOr wrapper.
#![allow(unused_imports, unused_variables)]
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use core::marker::PhantomData;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

#[derive(Copy, PartialEq, Eq, Debug)]
pub enum SignKind { Neg, Zero, Pos, NonPos, NonNeg, NonZero, Top }

#[derive(Copy, PartialEq, Eq)]
pub struct Sign<W> {
    kind: SignKind,
    marker: PhantomData<W>,
}

impl<W: Copy> Clone for Sign<W> {
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

pub closed spec fn from_categories<W: Word>(n: bool, z: bool, p: bool) -> BotOr<Sign<W>> {
    let kind = if n {
        if z { if p {SignKind::Top} else {SignKind::NonPos} }
        else { if p {SignKind::NonZero} else {SignKind::Neg} }
    } else {
        if z { if p {SignKind::NonNeg} else {SignKind::Zero} }
        else {SignKind::Pos}
    };
    if n || z || p {BotOr::Val(Sign {kind, marker: PhantomData})} else {BotOr::Bot}
}

pub closed spec fn category<W: Word>(a: &BotOr<Sign<W>>, x: int) -> bool {
    match a {BotOr::Bot => false, BotOr::Val(s) => s.kind.allows(x)}
}
pub closed spec fn union<W: Word>(a: &BotOr<Sign<W>>, b: &BotOr<Sign<W>>) -> BotOr<Sign<W>> {
    from_categories(category(a,-1)||category(b,-1), category(a,0)||category(b,0), category(a,1)||category(b,1))
}
pub closed spec fn intersection<W: Word>(a: &BotOr<Sign<W>>, b: &BotOr<Sign<W>>) -> BotOr<Sign<W>> {
    from_categories(category(a,-1)&&category(b,-1), category(a,0)&&category(b,0), category(a,1)&&category(b,1))
}
pub closed spec fn subset<W: Word>(a: &BotOr<Sign<W>>, b: &BotOr<Sign<W>>) -> bool {
    (!category(a,-1)||category(b,-1)) && (!category(a,0)||category(b,0)) && (!category(a,1)||category(b,1))
}

impl<W: Word> Sign<W> {
    pub closed spec fn kind_of(&self) -> SignKind { self.kind }

    pub fn from_kind(kind: SignKind) -> (r: Self)
        ensures r.wf(), r.kind_of() == kind,
    { Self { kind, marker: PhantomData } }

    pub fn kind(&self) -> (r: SignKind) ensures r == self.kind_of() { self.kind }

    fn build(n: bool, z: bool, p: bool) -> (r: BotOr<Self>)
        ensures r == from_categories::<W>(n,z,p),
    {
        if n {
            BotOr::Val(Self::from_kind(if z {if p {SignKind::Top}else{SignKind::NonPos}}
                else {if p {SignKind::NonZero}else{SignKind::Neg}}))
        } else if z {
            BotOr::Val(Self::from_kind(if p {SignKind::NonNeg}else{SignKind::Zero}))
        } else if p {BotOr::Val(Self::from_kind(SignKind::Pos))} else {BotOr::Bot}
    }

    pub fn contains(&self, x: W) -> (r: bool)
        requires self.wf(), ensures r == self.gamma(x),
    {
        let s = Self::from_value(x);
        let (n,z,p) = self.kind.categories();
        match s.kind {SignKind::Neg => n, SignKind::Zero => z, _ => p}
    }

    /// Abstract a bit pattern to its signed sign, not to a singleton value.
    pub fn from_value(x: W) -> (r: Self)
        ensures r.wf(), r.gamma(x),
            r.kind_of() == if signed_view(x)<0 {SignKind::Neg}
                else if signed_view(x)==0 {SignKind::Zero} else {SignKind::Pos},
    {
        proof {W::lemma_modulus(); x.lemma_view_bounded();}
        let two = match W::one().checked_add(W::one()) {Some(v)=>v, None=>{assert(false);W::one()}};
        let positive_max = W::max().udiv(two);
        proof {lemma_fundamental_div_mod(W::modulus() as int,2);lemma_fundamental_div_mod((W::modulus()-1) as int,2);}
        Self::from_kind(if x.eq(W::zero()) {SignKind::Zero}
            else if x.le(positive_max) {SignKind::Pos} else {SignKind::Neg})
    }

    pub fn refines(&self, other: &Self) -> (r: bool)
        requires self.wf(), other.wf(),
        ensures r == (forall|x: W| #[trigger] self.gamma(x) ==> other.gamma(x)),
    {
        let (n,z,p) = self.kind.categories();
        let (nn,zz,pp) = other.kind.categories();
        let r = (!n||nn) && (!z||zz) && (!p||pp);
        proof {
            Self::representatives();
            assert forall|x: W| r && self.gamma(x) implies #[trigger] other.gamma(x) by {
                x.lemma_view_bounded();
            }
            if !r {
                let x = if n && !nn {W::from_int(-1)}
                    else if z && !zz {W::from_int(0)} else {W::from_int(1)};
                assert(self.gamma(x) && !other.gamma(x));
            }
        }
        r
    }

    proof fn representatives()
        ensures signed_view(W::from_int(-1)) == -1,
            signed_view(W::from_int(0)) == 0, signed_view(W::from_int(1)) == 1,
    {
        W::lemma_modulus();
        W::lemma_from_int(-1); W::lemma_from_int(0); W::lemma_from_int(1);
        lemma_small_mod(0,W::modulus()); lemma_small_mod(1,W::modulus());
        lemma_mod_add_multiples_vanish(-1,W::modulus() as int);
        lemma_small_mod((W::modulus()-1) as nat,W::modulus());
        lemma_fundamental_div_mod(W::modulus() as int,2);
    }

    pub proof fn lattice_laws(a: BotOr<Self>, b: BotOr<Self>, c: BotOr<Self>)
        ensures
            union(&a,&b)==union(&b,&a), intersection(&a,&b)==intersection(&b,&a),
            union(&a,&a)==a, intersection(&a,&a)==a,
            union(&union(&a,&b),&c)==union(&a,&union(&b,&c)),
            intersection(&intersection(&a,&b),&c)==intersection(&a,&intersection(&b,&c)),
            union(&a,&intersection(&a,&b))==a, intersection(&a,&union(&a,&b))==a,
            union(&a,&BotOr::Bot)==a, intersection(&a,&BotOr::Bot)==BotOr::Bot,
            union(&a,&from_categories(true,true,true))==from_categories::<W>(true,true,true),
            intersection(&a,&from_categories(true,true,true))==a,
            subset(&a,&a), subset(&a,&union(&a,&b)), subset(&b,&union(&a,&b)),
            subset(&intersection(&a,&b),&a), subset(&intersection(&a,&b),&b),
            subset(&a,&b) && subset(&b,&a) ==> a==b,
            subset(&a,&b) && subset(&b,&c) ==> subset(&a,&c),
            subset(&a,&b) ==> subset(&union(&a,&c),&union(&b,&c)),
            subset(&a,&b) ==> subset(&intersection(&a,&c),&intersection(&b,&c)),
    {}

}

impl<W: Word> Domain for Sign<W> {
    type C = W;
    open spec fn wf(&self) -> bool { true }
    closed spec fn gamma(&self, x: W) -> bool { self.kind.allows(signed_view(x)) }
    proof fn lemma_nonempty(&self) {
        Self::representatives();
        let x = if self.kind.allows(-1) {W::from_int(-1)}
            else if self.kind.allows(0) {W::from_int(0)} else {W::from_int(1)};
        assert(self.gamma(x));
    }
    proof fn lemma_canonical(a: &Self, b: &Self) {
        Self::representatives();
        assert(a.gamma(W::from_int(-1))==b.gamma(W::from_int(-1)));
        assert(a.gamma(W::from_int(0))==b.gamma(W::from_int(0)));
        assert(a.gamma(W::from_int(1))==b.gamma(W::from_int(1)));
        assert(a.kind==b.kind);
    }
    fn dup(&self) -> (r: Self) { *self }
    fn top() -> (r: Self) { Self::from_kind(SignKind::Top) }
    fn leq(&self, other: &Self) -> (r: bool)
    {
        let (n,z,p) = self.kind.categories();
        let (nn,zz,pp) = other.kind.categories();
        let r = (!n||nn) && (!z||zz) && (!p||pp);
        proof {
            Self::representatives();
            assert forall|x: W| r && self.gamma(x) implies #[trigger] other.gamma(x) by {
                x.lemma_view_bounded();
            }
        }
        r
    }
    fn join(&self, other: &Self) -> (r: Self)
        ensures BotOr::Val(r)==union(&BotOr::Val(*self),&BotOr::Val(*other)),
            forall|x: W| #[trigger] r.gamma(x) == (self.gamma(x)||other.gamma(x)),
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
}
