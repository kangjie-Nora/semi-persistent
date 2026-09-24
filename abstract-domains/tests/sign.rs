// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::{domains::AbstractValue, sign::Sign};
use AbstractValue::{Bot, NonBot};

// Independent finite-set model: columns denote negative, zero, positive.
const CASES: [(AbstractValue<Sign>, [bool; 3]); 8] = [
    (Bot, [false, false, false]),
    (NonBot(Sign::Neg), [true, false, false]),
    (NonBot(Sign::Zero), [false, true, false]),
    (NonBot(Sign::Pos), [false, false, true]),
    (NonBot(Sign::NonPos), [true, true, false]),
    (NonBot(Sign::NonNeg), [false, true, true]),
    (NonBot(Sign::NonZero), [true, false, true]),
    (NonBot(Sign::Top), [true, true, true]),
];
fn reference(set: [bool; 3], x: i128) -> bool {
    set[if x < 0 {
        0
    } else if x == 0 {
        1
    } else {
        2
    }]
}
fn check_values(values: &[i128]) {
    for (a, sa) in CASES {
        for &x in values {
            assert_eq!(a.contains(x), reference(sa, x));
        }
        for (b, sb) in CASES {
            let j = a.join(b);
            let m = a.meet(b);
            let intersection = std::array::from_fn::<_, 3, _>(|i| sa[i] && sb[i]);
            assert!(matches!(m, Bot) == !intersection.iter().any(|&v| v));
            for &x in values {
                assert_eq!(j.contains(x), reference(sa, x) || reference(sb, x));
                assert_eq!(m.contains(x), reference(sa, x) && reference(sb, x));
            }
            // Every result is a canonical state, and represented sets are unique.
            for result in [j, m] {
                assert_eq!(CASES.iter().filter(|(v, _)| *v == result).count(), 1);
            }
        }
    }
}
#[test]
fn all_sign_pairs_at_every_i8_value() {
    check_values(&(i8::MIN..=i8::MAX).map(i128::from).collect::<Vec<_>>());
}
#[test]
fn lattice_laws_all_states_and_triples() {
    for (a, _) in CASES {
        assert!(a.join(a) == a && a.meet(a) == a);
        assert!(a.join(Bot) == a && a.meet(Bot) == Bot);
        assert!(a.join(NonBot(Sign::Top)) == NonBot(Sign::Top));
        assert!(a.meet(NonBot(Sign::Top)) == a);
        for (b, _) in CASES {
            assert!(a.join(b) == b.join(a) && a.meet(b) == b.meet(a));
            assert!(a.join(a.meet(b)) == a && a.meet(a.join(b)) == a);
            for (c, _) in CASES {
                assert!(a.join(b).join(c) == a.join(b.join(c)));
                assert!(a.meet(b).meet(c) == a.meet(b.meet(c)));
                assert!(a.meet(b.join(c)) == a.meet(b).join(a.meet(c)));
                assert!(a.join(b.meet(c)) == a.join(b).meet(a.join(c)));
            }
        }
    }
}
macro_rules! boundary {
    ($name:ident, $ty:ty) => {
        #[test]
        fn $name() {
            check_values(&[
                <$ty>::MIN as i128,
                (<$ty>::MIN + 1) as i128,
                -1,
                0,
                1,
                (<$ty>::MAX - 1) as i128,
                <$ty>::MAX as i128,
            ]);
        }
    };
}
boundary!(i8_boundaries, i8);
boundary!(i16_boundaries, i16);
boundary!(i32_boundaries, i32);
boundary!(i64_boundaries, i64);
boundary!(i128_boundaries, i128);
#[test]
fn concrete_constructor_and_clone() {
    for x in [i128::MIN, -1, 0, 1, i128::MAX] {
        let s = Sign::from_value(x);
        assert!(s.contains(x));
        assert!(
            s == if x < 0 {
                Sign::Neg
            } else if x == 0 {
                Sign::Zero
            } else {
                Sign::Pos
            }
        );
        assert!(s.clone() == s);
    }
    for (a, _) in CASES {
        assert!(a.clone() == a);
    }
}

#[test]
fn arithmetic_all_i8_pairs_against_concrete_i128_results() {
    for (a, sa) in CASES {
        assert!(matches!(a.neg_math(), Bot) == matches!(a, Bot));
        for x in i8::MIN..=i8::MAX {
            let x = i128::from(x);
            if reference(sa, x) {
                assert!(a.neg_math().contains(-x));
            }
        }
        for (b, sb) in CASES {
            let results = [
                a.add_math(b),
                a.sub_math(b),
                a.mul_math(b),
                a.min_math(b),
                a.max_math(b),
            ];
            let mut witnessed = [[false; 3]; 5];
            for r in results {
                assert!(matches!(r, Bot) == (matches!(a, Bot) || matches!(b, Bot)));
            }
            for x in i8::MIN..=i8::MAX {
                let x = i128::from(x);
                if !reference(sa, x) {
                    continue;
                }
                for y in i8::MIN..=i8::MAX {
                    let y = i128::from(y);
                    if !reference(sb, y) {
                        continue;
                    }
                    // Promote before computing: these are mathematical, not wrapping, results.
                    for (i, value) in [x + y, x - y, x * y, x.min(y), x.max(y)]
                        .into_iter()
                        .enumerate()
                    {
                        assert!(results[i].contains(value), "operation {i} lost {value}");
                        witnessed[i][if value < 0 {
                            0
                        } else if value == 0 {
                            1
                        } else {
                            2
                        }] = true;
                    }
                }
            }
            // Every included sign category has a concrete witness in this finite range.
            for (i, result) in results.into_iter().enumerate() {
                for (j, x) in [-1, 0, 1].into_iter().enumerate() {
                    assert_eq!(result.contains(x), witnessed[i][j]);
                }
            }
        }
    }
}

#[test]
fn arithmetic_boundary_values_without_host_overflow() {
    let xs = [
        i128::MIN,
        i128::MIN + 1,
        -129,
        -128,
        -1,
        0,
        1,
        127,
        128,
        i128::MAX - 1,
        i128::MAX,
    ];
    for (a, sa) in CASES {
        for x in xs {
            if reference(sa, x) {
                if let Some(n) = x.checked_neg() {
                    assert!(a.neg_math().contains(n));
                }
            }
        }
        for (b, sb) in CASES {
            for x in xs {
                for y in xs {
                    if !reference(sa, x) || !reference(sb, y) {
                        continue;
                    }
                    for (result, concrete) in [
                        (a.add_math(b), x.checked_add(y)),
                        (a.sub_math(b), x.checked_sub(y)),
                        (a.mul_math(b), x.checked_mul(y)),
                        (a.min_math(b), Some(x.min(y))),
                        (a.max_math(b), Some(x.max(y))),
                    ] {
                        if let Some(value) = concrete {
                            assert!(result.contains(value));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn mathematical_semantics_and_zero_precision_regressions() {
    assert!(Sign::Pos.add_math(Sign::Pos) == Sign::Pos);
    assert!(Sign::Pos.add_math(Sign::Pos).contains(127i128 + 1));
    // i8 wrap-around would be negative: do not use this transfer for that operation.
    assert!(!Sign::Pos
        .add_math(Sign::Pos)
        .contains(127i8.wrapping_add(1) as i128));
    assert!(Sign::Top.mul_math(Sign::Zero) == Sign::Zero);
    assert!(Sign::Neg.mul_math(Sign::Neg) == Sign::Pos);
    assert!(Sign::Pos.sub_math(Sign::Pos) == Sign::Top);
    assert!(Sign::NonZero.neg_math() == Sign::NonZero);
    assert!(Sign::Neg.min_math(Sign::Pos) == Sign::Neg);
    assert!(Sign::Neg.max_math(Sign::Pos) == Sign::Pos);
}
