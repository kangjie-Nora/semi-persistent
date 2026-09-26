// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use core::marker::PhantomData;
use semi_persistent_abstract_domains::{domains::AbstractValue, sign::Sign};
use AbstractValue::{Bot, NonBot};

macro_rules! suite {
    ($module:ident, $ty:ty) => {
        mod $module {
            use super::*;
            // Independent category-set oracle: negative, zero, positive.
            const CASES: [(AbstractValue<Sign<$ty>>, [bool; 3]); 8] = [
                (Bot, [false, false, false]),
                (NonBot(Sign::Neg), [true, false, false]),
                (NonBot(Sign::Zero), [false, true, false]),
                (NonBot(Sign::Pos), [false, false, true]),
                (NonBot(Sign::NonPos), [true, true, false]),
                (NonBot(Sign::NonNeg), [false, true, true]),
                (NonBot(Sign::NonZero), [true, false, true]),
                (NonBot(Sign::Top(PhantomData)), [true, true, true]),
            ];
            fn reference(s: [bool; 3], x: $ty) -> bool {
                s[if x < 0 {
                    0
                } else if x == 0 {
                    1
                } else {
                    2
                }]
            }
            pub(super) fn check_values(xs: &[$ty]) {
                for (a, sa) in CASES {
                    for &x in xs {
                        assert_eq!(a.contains(x), reference(sa, x));
                    }
                    assert!(a.clone() == a);
                    for (b, sb) in CASES {
                        let subset = (0..3).all(|i| !sa[i] || sb[i]);
                        assert_eq!(a.refines(&b), subset);
                        if let (NonBot(aa), NonBot(bb)) = (a, b) {
                            assert_eq!(aa.refines(&bb), subset);
                            assert!(NonBot(aa.join(bb)) == a.join(b));
                            assert!(aa.meet(bb) == a.meet(b));
                        }
                        let j = a.join(b);
                        let m = a.meet(b);
                        assert_eq!(matches!(m, Bot), !(0..3).any(|i| sa[i] && sb[i]));
                        for &x in xs {
                            assert_eq!(j.contains(x), reference(sa, x) || reference(sb, x));
                            assert_eq!(m.contains(x), reference(sa, x) && reference(sb, x));
                        }
                    }
                }
            }
            #[test]
            fn boundary_and_constructors() {
                let xs = [
                    <$ty>::MIN,
                    <$ty>::MIN + 1,
                    -1,
                    0,
                    1,
                    <$ty>::MAX - 1,
                    <$ty>::MAX,
                ];
                check_values(&xs);
                for x in xs {
                    let s = Sign::<$ty>::from_value(x);
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
                    assert!(Sign::<$ty>::top().contains(x));
                }
                assert!(Sign::<$ty>::from_value(<$ty>::MAX.wrapping_add(1)) == Sign::Neg);
                assert!(Sign::<$ty>::from_value(<$ty>::MIN.wrapping_sub(1)) == Sign::Pos);
                assert!(Sign::<$ty>::from_value(<$ty>::MIN.wrapping_neg()) == Sign::Neg);
            }
            #[test]
            fn lattice_and_order_laws() {
                for (a, _) in CASES {
                    assert!(a.refines(&a));
                    assert!(a.join(a) == a && a.meet(a) == a);
                    assert!(a.join(Bot) == a && a.meet(Bot) == Bot);
                    for (b, _) in CASES {
                        assert!(a.join(b) == b.join(a) && a.meet(b) == b.meet(a));
                        assert!(a.join(a.meet(b)) == a && a.meet(a.join(b)) == a);
                        if a.refines(&b) && b.refines(&a) {
                            assert!(a == b);
                        }
                        for (c, _) in CASES {
                            assert!(a.join(b).join(c) == a.join(b.join(c)));
                            assert!(a.meet(b).meet(c) == a.meet(b.meet(c)));
                            if a.refines(&b) {
                                assert!(a.join(c).refines(&b.join(c)));
                                assert!(a.meet(c).refines(&b.meet(c)));
                                if b.refines(&c) {
                                    assert!(a.refines(&c));
                                }
                            }
                        }
                    }
                }
            }
        }
    };
}
suite!(signed8, i8);
suite!(signed16, i16);
suite!(signed32, i32);
suite!(signed64, i64);
suite!(signed128, i128);
#[test]
fn exhaustive_i8_membership_refinement_and_set_operations() {
    signed8::check_values(&(i8::MIN..=i8::MAX).collect::<Vec<_>>());
}
