// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::{
    lattice::{BotOr, Domain},
    sign::{Sign, SignKind},
};

fn states() -> [SignKind; 7] {
    [
        SignKind::Neg,
        SignKind::Zero,
        SignKind::Pos,
        SignKind::NonPos,
        SignKind::NonNeg,
        SignKind::NonZero,
        SignKind::Top,
    ]
}

#[test]
fn exhaustive_i8_membership_and_lattice_operations() {
    for left_kind in states() {
        let left = Sign::<u8>::from_kind(left_kind);
        for right_kind in states() {
            let right = Sign::<u8>::from_kind(right_kind);
            let join = left.join(&right);
            let meet = left.meet(&right);
            for bits in 0..=u8::MAX {
                let expected_left = left.contains(bits);
                let expected_right = right.contains(bits);
                assert_eq!(join.contains(bits), expected_left || expected_right);
                match &meet {
                    BotOr::Bot => assert!(!(expected_left && expected_right)),
                    BotOr::Val(value) => {
                        assert_eq!(value.contains(bits), expected_left && expected_right)
                    }
                }
            }
            assert_eq!(
                left.refines(&right),
                (0..=u8::MAX).all(|x| !left.contains(x) || right.contains(x))
            );
        }
    }
}

#[test]
fn bottom_and_top_are_canonical() {
    type S = Sign<u8>;
    let negative = S::from_kind(SignKind::Neg);
    let positive = S::from_kind(SignKind::Pos);
    assert!(matches!(negative.meet(&positive), BotOr::Bot));
    assert!(matches!(S::top().meet(&negative), BotOr::Val(value) if value == negative));
    assert!(S::top().contains(0));
    assert!(S::top().contains(127));
    assert!(S::top().contains(128));
}

#[test]
fn signed_width_boundaries_have_the_expected_sign() {
    macro_rules! check {
        ($word:ty) => {{
            type S = Sign<$word>;
            let zero = S::from_value(0);
            let one = S::from_value(1);
            let min_bits = (1 as $word) << (<$word>::BITS - 1);
            let positive_max = S::from_value(min_bits - 1);
            let min = S::from_value(min_bits);
            assert_eq!(zero.kind(), SignKind::Zero);
            assert_eq!(one.kind(), SignKind::Pos);
            assert_eq!(positive_max.kind(), SignKind::Pos);
            assert_eq!(min.kind(), SignKind::Neg);
        }};
    }
    check!(u8);
    check!(u16);
    check!(u32);
    check!(u64);
}

#[test]
fn join_meet_and_widen_obey_the_sign_table() {
    type S = Sign<u8>;
    let neg = S::from_kind(SignKind::Neg);
    let zero = S::from_kind(SignKind::Zero);
    let pos = S::from_kind(SignKind::Pos);
    assert_eq!(neg.join(&zero).kind(), SignKind::NonPos);
    assert_eq!(zero.join(&pos).kind(), SignKind::NonNeg);
    assert_eq!(neg.join(&pos).kind(), SignKind::NonZero);
    assert_eq!(neg.widen(&pos).kind(), SignKind::NonZero);
    assert!(matches!(neg.meet(&zero), BotOr::Bot));
    assert!(
        matches!(S::from_kind(SignKind::NonZero).meet(&neg), BotOr::Val(value) if value == neg)
    );
}

use semi_persistent_abstract_domains::{
    semantics::Signed,
    transfer::{Arith, Mul},
};

#[test]
fn exhaustive_i8_signed_transfers_are_sound() {
    type S = Sign<u8>;
    for left_kind in states() {
        let left = S::from_kind(left_kind);
        let neg = <S as Arith<Signed<u8>>>::neg(&left);
        for x in 0..=u8::MAX {
            if left.contains(x) {
                assert!(neg.contains(x.wrapping_neg()), "neg: {left_kind:?}, {x}");
            }
        }
        for right_kind in states() {
            let right = S::from_kind(right_kind);
            let add = <S as Arith<Signed<u8>>>::add(&left, &right);
            let sub = <S as Arith<Signed<u8>>>::sub(&left, &right);
            let mul = <S as Mul<Signed<u8>>>::mul(&left, &right);
            for x in 0..=u8::MAX {
                if left.contains(x) {
                    for y in 0..=u8::MAX {
                        if right.contains(y) {
                            assert!(add.contains(x.wrapping_add(y)), "add: {left_kind:?}, {right_kind:?}, {x}, {y}");
                            assert!(sub.contains(x.wrapping_sub(y)), "sub: {left_kind:?}, {right_kind:?}, {x}, {y}");
                            assert!(mul.contains(x.wrapping_mul(y)), "mul: {left_kind:?}, {right_kind:?}, {x}, {y}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn signed_transfers_are_monotone_over_the_sign_lattice() {
    type S = Sign<u8>;
    for narrow_left_kind in states() {
        let narrow_left = S::from_kind(narrow_left_kind);
        for wide_left_kind in states() {
            let wide_left = S::from_kind(wide_left_kind);
            if !narrow_left.refines(&wide_left) { continue; }
            assert!(
                <S as Arith<Signed<u8>>>::neg(&narrow_left)
                    .refines(&<S as Arith<Signed<u8>>>::neg(&wide_left))
            );
            for narrow_right_kind in states() {
                let narrow_right = S::from_kind(narrow_right_kind);
                for wide_right_kind in states() {
                    let wide_right = S::from_kind(wide_right_kind);
                    if !narrow_right.refines(&wide_right) { continue; }
                    assert!(
                        <S as Arith<Signed<u8>>>::add(&narrow_left, &narrow_right)
                            .refines(&<S as Arith<Signed<u8>>>::add(&wide_left, &wide_right))
                    );
                    assert!(
                        <S as Arith<Signed<u8>>>::sub(&narrow_left, &narrow_right)
                            .refines(&<S as Arith<Signed<u8>>>::sub(&wide_left, &wide_right))
                    );
                    assert!(
                        <S as Mul<Signed<u8>>>::mul(&narrow_left, &narrow_right)
                            .refines(&<S as Mul<Signed<u8>>>::mul(&wide_left, &wide_right))
                    );
                }
            }
        }
    }
}
