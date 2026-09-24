// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Nonempty sign sets, with canonical bottom provided by AbstractValue.
//! Adapted from Vignesvern's feature/sign-domain (1f4bcd3).
use crate::domains::AbstractValue;
use vstd::prelude::*;

verus! {
#[derive(Copy, PartialEq, Eq)]
pub enum Sign { Neg, Zero, Pos, NonPos, NonNeg, NonZero, Top }

impl Clone for Sign {
    fn clone(&self) -> (r: Self) ensures r == *self { *self }
}

impl Sign {
    /// Mathematical integers; sign sets do not depend on machine width.
    pub open spec fn has(self, x: int) -> bool {
        match self {
            Self::Neg => x < 0, Self::Zero => x == 0, Self::Pos => x > 0,
            Self::NonPos => x <= 0, Self::NonNeg => x >= 0,
            Self::NonZero => x != 0, Self::Top => true,
        }
    }

    /// All signed primitive integers embed losslessly in i128.
    pub fn contains(&self, x: i128) -> (r: bool)
        ensures r == self.has(x as int)
    {
        match self {
            Self::Neg => x < 0, Self::Zero => x == 0, Self::Pos => x > 0,
            Self::NonPos => x <= 0, Self::NonNeg => x >= 0,
            Self::NonZero => x != 0, Self::Top => true,
        }
    }

    /// Abstract a concrete value to its sign, not a singleton magnitude.
    pub fn from_value(x: i128) -> (r: Self)
        ensures r.has(x as int)
    {
        if x < 0 { Self::Neg } else if x == 0 { Self::Zero } else { Self::Pos }
    }

    pub fn join(self, other: Self) -> (r: Self)
        ensures forall|x: int| r.has(x) == (self.has(x) || other.has(x))
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
            (Self::Neg, Self::Top) |
            (Self::Zero, Self::NonZero) |
            (Self::Zero, Self::Top) |
            (Self::Pos, Self::NonPos) |
            (Self::Pos, Self::Top) |
            (Self::NonPos, Self::Pos) |
            (Self::NonPos, Self::NonNeg) |
            (Self::NonPos, Self::NonZero) |
            (Self::NonPos, Self::Top) |
            (Self::NonNeg, Self::Neg) |
            (Self::NonNeg, Self::NonPos) |
            (Self::NonNeg, Self::NonZero) |
            (Self::NonNeg, Self::Top) |
            (Self::NonZero, Self::Zero) |
            (Self::NonZero, Self::NonPos) |
            (Self::NonZero, Self::NonNeg) |
            (Self::NonZero, Self::Top) |
            (Self::Top, Self::Neg) |
            (Self::Top, Self::Zero) |
            (Self::Top, Self::Pos) |
            (Self::Top, Self::NonPos) |
            (Self::Top, Self::NonNeg) |
            (Self::Top, Self::NonZero) |
            (Self::Top, Self::Top) => Self::Top,
        }
    }

    pub fn meet(self, other: Self) -> (r: AbstractValue<Self>)
        ensures forall|x: int| r.has(x) == (self.has(x) && other.has(x))
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
            (Self::Neg, Self::Top) |
            (Self::NonPos, Self::Neg) |
            (Self::NonPos, Self::NonZero) |
            (Self::NonZero, Self::Neg) |
            (Self::NonZero, Self::NonPos) |
            (Self::Top, Self::Neg) => AbstractValue::NonBot(Self::Neg),
            (Self::Zero, Self::Zero) |
            (Self::Zero, Self::NonPos) |
            (Self::Zero, Self::NonNeg) |
            (Self::Zero, Self::Top) |
            (Self::NonPos, Self::Zero) |
            (Self::NonPos, Self::NonNeg) |
            (Self::NonNeg, Self::Zero) |
            (Self::NonNeg, Self::NonPos) |
            (Self::Top, Self::Zero) => AbstractValue::NonBot(Self::Zero),
            (Self::Pos, Self::Pos) |
            (Self::Pos, Self::NonNeg) |
            (Self::Pos, Self::NonZero) |
            (Self::Pos, Self::Top) |
            (Self::NonNeg, Self::Pos) |
            (Self::NonNeg, Self::NonZero) |
            (Self::NonZero, Self::Pos) |
            (Self::NonZero, Self::NonNeg) |
            (Self::Top, Self::Pos) => AbstractValue::NonBot(Self::Pos),
            (Self::NonPos, Self::NonPos) |
            (Self::NonPos, Self::Top) |
            (Self::Top, Self::NonPos) => AbstractValue::NonBot(Self::NonPos),
            (Self::NonNeg, Self::NonNeg) |
            (Self::NonNeg, Self::Top) |
            (Self::Top, Self::NonNeg) => AbstractValue::NonBot(Self::NonNeg),
            (Self::NonZero, Self::NonZero) |
            (Self::NonZero, Self::Top) |
            (Self::Top, Self::NonZero) => AbstractValue::NonBot(Self::NonZero),
            (Self::Top, Self::Top) => AbstractValue::NonBot(Self::Top),
        }
    }
}

/// Lifted operations cover empty inputs as well as nonempty Sign values.
impl AbstractValue<Sign> {
    pub open spec fn has(self, x: int) -> bool {
        match self { Self::Bot => false, Self::NonBot(s) => s.has(x) }
    }

    pub fn contains(&self, x: i128) -> (r: bool)
        ensures r == self.has(x as int)
    {
        match self { Self::Bot => false, Self::NonBot(s) => s.contains(x) }
    }

    pub fn join(self, other: Self) -> (r: Self)
        ensures forall|x: int| r.has(x) == (self.has(x) || other.has(x))
    {
        match (self, other) {
            (Self::Bot, x) | (x, Self::Bot) => x,
            (Self::NonBot(a), Self::NonBot(b)) => Self::NonBot(a.join(b)),
        }
    }

    pub fn meet(self, other: Self) -> (r: Self)
        ensures forall|x: int| r.has(x) == (self.has(x) && other.has(x))
    {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::NonBot(a), Self::NonBot(b)) => a.meet(b),
        }
    }
}
} // verus!
