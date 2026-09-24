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
