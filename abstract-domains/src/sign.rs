// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Signed-width Sign core with canonical bottom in AbstractValue.
use crate::domains::AbstractValue;
use core::marker::PhantomData;
use vstd::prelude::*;
verus! {
#[derive(Copy, PartialEq, Eq)]
pub enum Sign<T> { Neg, Zero, Pos, NonPos, NonNeg, NonZero, Top(PhantomData<T>) }
impl<T: Copy> Clone for Sign<T> {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}
}
macro_rules! impl_sign_domain {
    ($ty:ty) => { verus! {
impl Sign<$ty> {
    /// Membership in the signed two's-complement value set of this width.
    pub open spec fn has(self, x: $ty) -> bool {
        match self {
            Self::Neg => x < 0, Self::Zero => x == 0, Self::Pos => x > 0,
            Self::NonPos => x <= 0, Self::NonNeg => x >= 0,
            Self::NonZero => x != 0, Self::Top(_) => true,
        }
    }

    /// Executable membership for the same signed width.
    pub fn contains(&self, x: $ty) -> (r: bool)
        ensures r == self.has(x)
    {
        match self {
            Self::Neg => x < 0, Self::Zero => x == 0, Self::Pos => x > 0,
            Self::NonPos => x <= 0, Self::NonNeg => x >= 0,
            Self::NonZero => x != 0, Self::Top(_) => true,
        }
    }

    /// Abstract a concrete value to its sign, not a singleton magnitude.
    pub fn from_value(x: $ty) -> (r: Self)
        ensures r.has(x)
    {
        if x < 0 { Self::Neg } else if x == 0 { Self::Zero } else { Self::Pos }
    }

    /// Every inner state has a concrete witness; only the outer Bot is empty.
    pub proof fn nonempty(self)
        ensures self.has((-1int) as $ty) || self.has(0) || self.has(1)
    {}

    pub fn top() -> (r: Self)
        ensures forall|x: $ty| r.has(x)
    { Self::Top(PhantomData) }

    pub fn refines(&self, other: &Self) -> (r: bool)
        ensures r == (forall|x: $ty| self.has(x) ==> other.has(x))
    {
        (!self.contains(-1) || other.contains(-1)) &&
        (!self.contains(0) || other.contains(0)) &&
        (!self.contains(1) || other.contains(1))
    }

    pub fn join(self, other: Self) -> (r: Self)
        ensures forall|x: $ty| r.has(x) == (self.has(x) || other.has(x))
    {
        match (self, other) {
            (Self::Neg, Self::Neg) => Self::Neg,
            (Self::Zero, Self::Zero) => Self::Zero,
            (Self::Pos, Self::Pos) => Self::Pos,
            (Self::Neg, Self::Zero) |
            (Self::Neg, Self::NonPos) |
            (Self::Zero, Self::Neg) |
            (Self::Zero, Self::NonPos) |
            (Self::NonPos, Self::Neg) |
            (Self::NonPos, Self::Zero) |
            (Self::NonPos, Self::NonPos) => Self::NonPos,
            (Self::Zero, Self::Pos) |
            (Self::Zero, Self::NonNeg) |
            (Self::Pos, Self::Zero) |
            (Self::Pos, Self::NonNeg) |
            (Self::NonNeg, Self::Zero) |
            (Self::NonNeg, Self::Pos) |
            (Self::NonNeg, Self::NonNeg) => Self::NonNeg,
            (Self::Neg, Self::Pos) |
            (Self::Neg, Self::NonZero) |
            (Self::Pos, Self::Neg) |
            (Self::Pos, Self::NonZero) |
            (Self::NonZero, Self::Neg) |
            (Self::NonZero, Self::Pos) |
            (Self::NonZero, Self::NonZero) => Self::NonZero,
            (Self::Neg, Self::NonNeg) |
            (Self::Neg, Self::Top(_)) |
            (Self::Zero, Self::NonZero) |
            (Self::Zero, Self::Top(_)) |
            (Self::Pos, Self::NonPos) |
            (Self::Pos, Self::Top(_)) |
            (Self::NonPos, Self::Pos) |
            (Self::NonPos, Self::NonNeg) |
            (Self::NonPos, Self::NonZero) |
            (Self::NonPos, Self::Top(_)) |
            (Self::NonNeg, Self::Neg) |
            (Self::NonNeg, Self::NonPos) |
            (Self::NonNeg, Self::NonZero) |
            (Self::NonNeg, Self::Top(_)) |
            (Self::NonZero, Self::Zero) |
            (Self::NonZero, Self::NonPos) |
            (Self::NonZero, Self::NonNeg) |
            (Self::NonZero, Self::Top(_)) |
            (Self::Top(_), Self::Neg) |
            (Self::Top(_), Self::Zero) |
            (Self::Top(_), Self::Pos) |
            (Self::Top(_), Self::NonPos) |
            (Self::Top(_), Self::NonNeg) |
            (Self::Top(_), Self::NonZero) |
            (Self::Top(_), Self::Top(_)) => Self::Top(PhantomData),
        }
    }

    pub fn meet(self, other: Self) -> (r: AbstractValue<Self>)
        ensures forall|x: $ty| r.has(x) == (self.has(x) && other.has(x))
    {
        match (self, other) {
            (Self::Neg, Self::Zero) |
            (Self::Neg, Self::Pos) |
            (Self::Neg, Self::NonNeg) |
            (Self::Zero, Self::Neg) |
            (Self::Zero, Self::Pos) |
            (Self::Zero, Self::NonZero) |
            (Self::Pos, Self::Neg) |
            (Self::Pos, Self::Zero) |
            (Self::Pos, Self::NonPos) |
            (Self::NonPos, Self::Pos) |
            (Self::NonNeg, Self::Neg) |
            (Self::NonZero, Self::Zero) => AbstractValue::Bot,
            (Self::Neg, Self::Neg) |
            (Self::Neg, Self::NonPos) |
            (Self::Neg, Self::NonZero) |
            (Self::Neg, Self::Top(_)) |
            (Self::NonPos, Self::Neg) |
            (Self::NonPos, Self::NonZero) |
            (Self::NonZero, Self::Neg) |
            (Self::NonZero, Self::NonPos) |
            (Self::Top(_), Self::Neg) => AbstractValue::NonBot(Self::Neg),
            (Self::Zero, Self::Zero) |
            (Self::Zero, Self::NonPos) |
            (Self::Zero, Self::NonNeg) |
            (Self::Zero, Self::Top(_)) |
            (Self::NonPos, Self::Zero) |
            (Self::NonPos, Self::NonNeg) |
            (Self::NonNeg, Self::Zero) |
            (Self::NonNeg, Self::NonPos) |
            (Self::Top(_), Self::Zero) => AbstractValue::NonBot(Self::Zero),
            (Self::Pos, Self::Pos) |
            (Self::Pos, Self::NonNeg) |
            (Self::Pos, Self::NonZero) |
            (Self::Pos, Self::Top(_)) |
            (Self::NonNeg, Self::Pos) |
            (Self::NonNeg, Self::NonZero) |
            (Self::NonZero, Self::Pos) |
            (Self::NonZero, Self::NonNeg) |
            (Self::Top(_), Self::Pos) => AbstractValue::NonBot(Self::Pos),
            (Self::NonPos, Self::NonPos) |
            (Self::NonPos, Self::Top(_)) |
            (Self::Top(_), Self::NonPos) => AbstractValue::NonBot(Self::NonPos),
            (Self::NonNeg, Self::NonNeg) |
            (Self::NonNeg, Self::Top(_)) |
            (Self::Top(_), Self::NonNeg) => AbstractValue::NonBot(Self::NonNeg),
            (Self::NonZero, Self::NonZero) |
            (Self::NonZero, Self::Top(_)) |
            (Self::Top(_), Self::NonZero) => AbstractValue::NonBot(Self::NonZero),
            (Self::Top(_), Self::Top(_)) => AbstractValue::NonBot(Self::Top(PhantomData)),
        }
    }
}

/// Lifted operations cover empty inputs as well as nonempty Sign values.
impl AbstractValue<Sign<$ty>> {
    pub open spec fn has(self, x: $ty) -> bool {
        match self { Self::Bot => false, Self::NonBot(s) => s.has(x) }
    }

    pub fn contains(&self, x: $ty) -> (r: bool)
        ensures r == self.has(x)
    {
        match self { Self::Bot => false, Self::NonBot(s) => s.contains(x) }
    }

    pub fn refines(&self, other: &Self) -> (r: bool)
        ensures r == (forall|x: $ty| self.has(x) ==> other.has(x))
    {
        (!self.contains(-1) || other.contains(-1)) &&
        (!self.contains(0) || other.contains(0)) &&
        (!self.contains(1) || other.contains(1))
    }

    pub open spec fn from_categories(n: bool, z: bool, p: bool) -> Self {
        if n { if z { if p { Self::NonBot(Sign::Top(PhantomData)) } else {Self::NonBot(Sign::NonPos)} }
            else {if p {Self::NonBot(Sign::NonZero)} else {Self::NonBot(Sign::Neg)}} }
        else {if z {if p {Self::NonBot(Sign::NonNeg)} else {Self::NonBot(Sign::Zero)}}
            else {if p {Self::NonBot(Sign::Pos)} else {Self::Bot}}}
    }
    pub open spec fn union(self, other: Self) -> Self {
        Self::from_categories(self.has((-1int) as $ty)||other.has((-1int) as $ty),self.has(0)||other.has(0),self.has(1)||other.has(1))
    }
    pub open spec fn intersection(self, other: Self) -> Self {
        Self::from_categories(self.has((-1int) as $ty)&&other.has((-1int) as $ty),self.has(0)&&other.has(0),self.has(1)&&other.has(1))
    }
    pub open spec fn subset(self, other: Self) -> bool {
        forall|x: $ty| self.has(x) ==> other.has(x)
    }
    pub proof fn lattice_laws(a: Self, b: Self, c: Self)
        ensures
            a.union(b) == b.union(a), a.intersection(b) == b.intersection(a),
            a.union(a) == a, a.intersection(a) == a,
            a.union(b).union(c) == a.union(b.union(c)),
            a.intersection(b).intersection(c) == a.intersection(b.intersection(c)),
            a.union(a.intersection(b)) == a, a.intersection(a.union(b)) == a,
            a.union(Self::Bot) == a, a.intersection(Self::Bot) == Self::Bot,
            a.union(Self::NonBot(Sign::Top(PhantomData))) == Self::NonBot(Sign::Top(PhantomData)),
            a.intersection(Self::NonBot(Sign::Top(PhantomData))) == a,
            a.subset(a),
            a.subset(a.union(b)), b.subset(a.union(b)),
            a.intersection(b).subset(a), a.intersection(b).subset(b),
            a.subset(b) && b.subset(a) ==> a == b,
            a.subset(b) && b.subset(c) ==> a.subset(c),
            a.subset(b) ==> a.union(c).subset(b.union(c)),
            a.subset(b) ==> a.intersection(c).subset(b.intersection(c)),
    {}

    pub fn join(self, other: Self) -> (r: Self)
        ensures r == self.union(other),
            forall|x: $ty| r.has(x) == (self.has(x) || other.has(x))
    {
        match (self, other) {
            (Self::Bot, x) | (x, Self::Bot) => x,
            (Self::NonBot(a), Self::NonBot(b)) => Self::NonBot(a.join(b)),
        }
    }

    pub fn meet(self, other: Self) -> (r: Self)
        ensures r == self.intersection(other),
            forall|x: $ty| r.has(x) == (self.has(x) && other.has(x))
    {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::NonBot(a), Self::NonBot(b)) => a.meet(b),
        }
    }
}

} };
}
impl_sign_domain!(i8);
impl_sign_domain!(i16);
impl_sign_domain!(i32);
impl_sign_domain!(i64);
impl_sign_domain!(i128);
