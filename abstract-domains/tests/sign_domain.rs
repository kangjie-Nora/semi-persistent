// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive small-model checks for the mathematical-integer Sign domain.

use semi_persistent_abstract_domains::{
    lattice::{BotOr, Domain},
    semantics::{Euclid, Trunc},
    sign::{Sign, SignKind},
    transfer::{Arith, DivRem, Mul},
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

fn members(s: &Sign) -> impl Iterator<Item = i128> + '_ {
    (-12..=12).filter(move |x| s.contains(*x))
}

#[test]
fn lattice_is_exact_on_all_categories() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let join = a.join(&b);
            let meet = a.meet(&b);
            for x in -12..=12 {
                assert_eq!(join.contains(x), a.contains(x) || b.contains(x));
                assert_eq!(
                    match &meet {
                        BotOr::Bot => false,
                        BotOr::Val(v) => v.contains(x),
                    },
                    a.contains(x) && b.contains(x)
                );
            }
            assert_eq!(
                a.leq(&b),
                (-12..=12).all(|x| !a.contains(x) || b.contains(x))
            );
        }
    }
}

#[test]
fn integer_transfers_contain_every_small_model_result() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        let neg = <Sign as Arith<Euclid>>::neg(&a);
        for x in members(&a) {
            assert!(neg.contains(-x), "neg: {a_kind:?}, {x}");
        }
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let add = <Sign as Arith<Euclid>>::add(&a, &b);
            let sub = <Sign as Arith<Euclid>>::sub(&a, &b);
            let mul = <Sign as Mul<Euclid>>::mul(&a, &b);
            for x in members(&a) {
                for y in members(&b) {
                    assert!(add.contains(x + y), "add: {a_kind:?}, {b_kind:?}, {x}, {y}");
                    assert!(sub.contains(x - y), "sub: {a_kind:?}, {b_kind:?}, {x}, {y}");
                    assert!(mul.contains(x * y), "mul: {a_kind:?}, {b_kind:?}, {x}, {y}");
                }
            }
        }
    }
}

#[test]
fn division_flags_and_results_are_sound() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let (eq, ef) = <Sign as DivRem<Euclid>>::div(&a, &b);
            let (er, rf) = <Sign as DivRem<Euclid>>::rem(&a, &b);
            let (tq, tf) = <Sign as DivRem<Trunc>>::div(&a, &b);
            let (tr, tf_r) = <Sign as DivRem<Trunc>>::rem(&a, &b);
            if b.kind() == SignKind::Zero {
                assert!(matches!(
                    (eq, er, tq, tr, ef, rf, tf, tf_r),
                    (BotOr::Bot, BotOr::Bot, BotOr::Bot, BotOr::Bot, _, _, _, _)
                ));
                continue;
            }
            for x in members(&a) {
                for y in members(&b).filter(|y| *y != 0) {
                    assert!(matches!(&eq, BotOr::Val(v) if v.contains(x.div_euclid(y))));
                    assert!(matches!(&er, BotOr::Val(v) if v.contains(x.rem_euclid(y))));
                    assert!(matches!(&tq, BotOr::Val(v) if v.contains(x / y)));
                    assert!(matches!(&tr, BotOr::Val(v) if v.contains(x % y)));
                }
            }

            // All possible sign categories are witnessed in this bounded model,
            // so this is an exactness check for truncated integer division.
            if let BotOr::Val(q) = tq {
                for z in -12..=12 {
                    let concrete =
                        members(&a).any(|x| members(&b).filter(|y| *y != 0).any(|y| x / y == z));
                    assert_eq!(
                        q.contains(z),
                        concrete,
                        "trunc div: {a_kind:?}, {b_kind:?}, {z}"
                    );
                }
            }
        }
    }
}
