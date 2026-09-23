// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::domains::{AbstractValue, Wrapped};
#[allow(dead_code)]
#[path = "support/wrapped_oracle.rs"]
mod wrapped_oracle;
use wrapped_oracle::{Oracle, Repr};

#[test]
fn complementary_arcs_join_must_cover_ring() {
    let a = Wrapped::<u8>::Arc { lo: 0, hi: 1 };
    let b = Wrapped::<u8>::Arc { lo: 1, hi: 0 };
    let j = a.join(&b);
    for x in 0..=255 {
        assert!(j.contains(x), "lost {x}");
    }
}

#[test]
fn sampled_endpoint_pairs_exhaustive_u8_values() {
    let o = Oracle::new(8).unwrap();
    let endpoints = [
        0, 1, 2, 3, 7, 8, 14, 15, 16, 127, 128, 129, 252, 253, 254, 255,
    ];
    let mut cases = vec![(Wrapped::<u8>::Top, o.values(Repr::Full).unwrap())];
    for lo in endpoints {
        for hi in endpoints {
            cases.push((
                Wrapped::Arc { lo, hi },
                o.values(Repr::Arc {
                    lo: lo as u32,
                    hi: hi as u32,
                })
                .unwrap(),
            ));
        }
    }
    for (a, sa) in &cases {
        for (b, sb) in &cases {
            let j = a.join(b);
            let m = a.meet(b);
            assert!(j == a.join(b));
            assert!(m == a.meet(b));
            let expected_meet = sa.intersection(sb);
            assert_eq!(
                matches!(m, AbstractValue::Bot),
                expected_meet.cardinality() == 0
            );
            for x in 0..=255u8 {
                if sa.contains(x as u32) || sb.contains(x as u32) {
                    assert!(j.contains(x), "join missing {x}");
                }
                if expected_meet.contains(x as u32) {
                    assert!(
                        match m {
                            AbstractValue::Bot => false,
                            AbstractValue::NonBot(w) => w.contains(x),
                        },
                        "meet missing {x}"
                    );
                }
            }
        }
    }
}

#[test]
fn split_meet_preserves_both_components() {
    let a = Wrapped::<u8>::Arc { lo: 250, hi: 6 };
    let b = Wrapped::<u8>::Arc { lo: 4, hi: 252 };
    let r = a.meet(&b);
    for x in [4, 5, 6, 250, 251, 252] {
        assert!(matches!(r, AbstractValue::NonBot(w) if w.contains(x)));
    }
    assert!(r == AbstractValue::NonBot(a));
    assert!(b.meet(&a) == AbstractValue::NonBot(b));
}

macro_rules! boundary {
    ($name:ident,$ty:ty,$bits:ty) => {
        #[test]
        fn $name() {
            let p: [$ty;5] = [<$ty>::MIN,0,1,<$ty>::MAX,
                (1 as $bits).rotate_right(1) as $ty];
            let mut cases = vec![Wrapped::<$ty>::Top];
            for lo in p {for hi in p { cases.push(Wrapped::Arc{lo,hi}); }}
            let has = |w: Wrapped<$ty>, x:$ty| match w {
                Wrapped::Top=>true,
                Wrapped::Arc{lo,hi}=>(x as $bits).wrapping_sub(lo as $bits)
                    <= (hi as $bits).wrapping_sub(lo as $bits),
            };
            for a in &cases {for b in &cases {
                let j=a.join(b); let m=a.meet(b);
                assert!(j==j.normalize());
                if let AbstractValue::NonBot(w)=m {assert!(w==w.normalize());}
                assert!(j==a.join(b));assert!(m==a.meet(b));
                let mut xs=p.to_vec();
                for w in [*a,*b] {if let Wrapped::Arc{lo,hi}=w {
                    xs.extend([lo,hi,lo.wrapping_sub(1),lo.wrapping_add(1),hi.wrapping_sub(1),hi.wrapping_add(1)]);
                }}
                for x in xs {
                    if has(*a,x)||has(*b,x){assert!(has(j,x));}
                    if has(*a,x)&&has(*b,x){assert!(matches!(m,AbstractValue::NonBot(w) if has(w,x)));}
                }
            }}
        }
    };
}
boundary!(u8_boundaries, u8, u8);
boundary!(i8_boundaries, i8, u8);
boundary!(u16_boundaries, u16, u16);
boundary!(i16_boundaries, i16, u16);
boundary!(u32_boundaries, u32, u32);
boundary!(i32_boundaries, i32, u32);
boundary!(u64_boundaries, u64, u64);
boundary!(i64_boundaries, i64, u64);
boundary!(u128_boundaries, u128, u128);
boundary!(i128_boundaries, i128, u128);
