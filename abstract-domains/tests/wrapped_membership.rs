// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Production membership and normalization tests; arithmetic is not tested.
#[allow(dead_code)]
#[path = "support/wrapped_oracle.rs"]
mod wrapped_oracle;
#[allow(dead_code)]
#[path = "support/wrapped_u32_cases.rs"]
mod wrapped_u32_cases;
use semi_persistent_abstract_domains::domains::Wrapped;
use wrapped_oracle::{Oracle, Repr};

#[test]
fn exhaustive_u8_and_i8_membership_against_ring_enumeration() {
    let oracle = Oracle::new(8).unwrap();
    for repr in oracle.raw_representations() {
        let (unsigned, signed) = match repr {
            Repr::Empty => (Wrapped::<u8>::Bottom, Wrapped::<i8>::Bottom),
            Repr::Full => (Wrapped::<u8>::Top, Wrapped::<i8>::Top),
            Repr::Arc { lo, hi } => (
                Wrapped::Arc {
                    lo: lo as u8,
                    hi: hi as u8,
                },
                Wrapped::Arc {
                    lo: lo as u8 as i8,
                    hi: hi as u8 as i8,
                },
            ),
        };
        let expected = oracle.values(repr).unwrap();
        for x in 0..256 {
            assert_eq!(
                unsigned.contains(x as u8),
                expected.contains(x),
                "u8 {repr:?}, x={x}"
            );
            assert_eq!(
                signed.contains(x as u8 as i8),
                expected.contains(x),
                "i8 {repr:?}, bits={x}"
            );
        }
    }
}

#[test]
fn production_u32_membership_uses_prepared_boundary_checker() {
    wrapped_u32_cases::check_membership(|repr, x| {
        let actual = match repr {
            Repr::Empty => Wrapped::<u32>::Bottom,
            Repr::Full => Wrapped::<u32>::Top,
            Repr::Arc { lo, hi } => Wrapped::Arc { lo, hi },
        };
        actual.contains(x)
    })
    .unwrap();
}

// Distance along the bit-pattern ring is independent of signed ordering.
// Use wrapping subtraction in the corresponding unsigned type, including u128.
macro_rules! boundary_test {
    ($name:ident, $ty:ty, $bits:ty) => {
        #[test]
        fn $name() {
            let points: [$ty; 7] = [
                <$ty>::MIN,
                <$ty>::MIN.wrapping_add(1),
                0,
                1,
                <$ty>::MAX.wrapping_sub(1),
                <$ty>::MAX,
                (1 as $bits).rotate_right(1) as $ty,
            ];
            for x in points {
                assert!(!Wrapped::<$ty>::Bottom.contains(x));
                assert!(Wrapped::<$ty>::Top.contains(x));
            }
            for lo in points {
                for hi in points {
                    let arc = Wrapped::<$ty>::Arc { lo, hi };
                    let mut probes = points.to_vec();
                    probes.extend([
                        lo.wrapping_sub(1),
                        lo.wrapping_add(1),
                        hi.wrapping_sub(1),
                        hi.wrapping_add(1),
                    ]);
                    for x in probes {
                        let expected = (x as $bits).wrapping_sub(lo as $bits)
                            <= (hi as $bits).wrapping_sub(lo as $bits);
                        assert_eq!(arc.contains(x), expected, "lo={lo}, hi={hi}, x={x}");
                    }
                }
            }
        }
    };
}
boundary_test!(u16_boundaries, u16, u16);
boundary_test!(u32_boundaries, u32, u32);
boundary_test!(u64_boundaries, u64, u64);
boundary_test!(u128_boundaries, u128, u128);
boundary_test!(i16_boundaries, i16, u16);
boundary_test!(i32_boundaries, i32, u32);
boundary_test!(i64_boundaries, i64, u64);
boundary_test!(i128_boundaries, i128, u128);

#[test]
fn exhaustive_u8_and_i8_normalization_against_oracle() {
    let oracle = Oracle::new(8).unwrap();
    for repr in oracle.raw_representations() {
        let to_u8 = |r| match r {
            Repr::Empty => Wrapped::<u8>::Bottom,
            Repr::Full => Wrapped::<u8>::Top,
            Repr::Arc { lo, hi } => Wrapped::Arc {
                lo: lo as u8,
                hi: hi as u8,
            },
        };
        let to_i8 = |r| match r {
            Repr::Empty => Wrapped::<i8>::Bottom,
            Repr::Full => Wrapped::<i8>::Top,
            Repr::Arc { lo, hi } => Wrapped::Arc {
                lo: lo as u8 as i8,
                hi: hi as u8 as i8,
            },
        };
        let expected = oracle.values(repr).unwrap();
        let canonical = oracle.normalize(repr).unwrap();
        let unsigned = to_u8(repr).normalize();
        let signed = to_i8(repr).normalize();
        assert!(unsigned == to_u8(canonical), "u8 canonical output {repr:?}");
        assert!(signed == to_i8(canonical), "i8 canonical output {repr:?}");
        assert!(unsigned.normalize() == unsigned);
        assert!(signed.normalize() == signed);
        for x in 0..256 {
            assert_eq!(
                unsigned.contains(x as u8),
                expected.contains(x),
                "u8 {repr:?}, x={x}"
            );
            assert_eq!(
                signed.contains(x as u8 as i8),
                expected.contains(x),
                "i8 {repr:?}, bits={x}"
            );
        }
    }
}

macro_rules! normalization_boundary_test {
    ($name:ident, $ty:ty, $bits:ty) => {
        #[test]
        fn $name() {
            assert!(Wrapped::<$ty>::Bottom.normalize() == Wrapped::Bottom);
            assert!(Wrapped::<$ty>::Top.normalize() == Wrapped::Top);
            let points: [$ty; 7] = [
                <$ty>::MIN,
                <$ty>::MIN.wrapping_add(1),
                0,
                1,
                <$ty>::MAX.wrapping_sub(1),
                <$ty>::MAX,
                (1 as $bits).rotate_right(1) as $ty,
            ];
            for lo in points {
                // Full-circle arcs at every selected cut, including signed wrap.
                let full = Wrapped::<$ty>::Arc {
                    lo,
                    hi: lo.wrapping_sub(1),
                };
                assert!(full.normalize() == Wrapped::Top);
                let singleton = Wrapped::<$ty>::Arc { lo, hi: lo };
                assert!(singleton.normalize() == singleton);
                for hi in points {
                    let original = Wrapped::<$ty>::Arc { lo, hi };
                    let normalized = original.normalize();
                    let distance = (hi as $bits).wrapping_sub(lo as $bits);
                    if distance == <$bits>::MAX {
                        assert!(normalized == Wrapped::Top);
                    } else {
                        assert!(normalized == original);
                    }
                    assert!(normalized.normalize() == normalized);
                    let mut probes = points.to_vec();
                    probes.extend([
                        lo.wrapping_sub(1),
                        lo.wrapping_add(1),
                        hi.wrapping_sub(1),
                        hi.wrapping_add(1),
                    ]);
                    for x in probes {
                        let expected = (x as $bits).wrapping_sub(lo as $bits) <= distance;
                        assert_eq!(normalized.contains(x), expected, "lo={lo}, hi={hi}, x={x}");
                    }
                }
            }
        }
    };
}
normalization_boundary_test!(u16_normalization, u16, u16);
normalization_boundary_test!(u32_normalization, u32, u32);
normalization_boundary_test!(u64_normalization, u64, u64);
normalization_boundary_test!(u128_normalization, u128, u128);
normalization_boundary_test!(i16_normalization, i16, u16);
normalization_boundary_test!(i32_normalization, i32, u32);
normalization_boundary_test!(i64_normalization, i64, u64);
normalization_boundary_test!(i128_normalization, i128, u128);

#[test]
#[allow(clippy::clone_on_copy)]
fn explicit_clone_preserves_all_variants_for_supported_types() {
    macro_rules! check {
        ($ty:ty) => {
            for value in [
                Wrapped::<$ty>::Bottom,
                Wrapped::<$ty>::Top,
                Wrapped::<$ty>::Arc {
                    lo: <$ty>::MAX,
                    hi: <$ty>::MIN,
                },
                Wrapped::<$ty>::Arc { lo: 0, hi: 0 },
            ] {
                assert!(value.clone() == value);
            }
        };
    }
    check!(u8);
    check!(u16);
    check!(u32);
    check!(u64);
    check!(u128);
    check!(i8);
    check!(i16);
    check!(i32);
    check!(i64);
    check!(i128);
}
