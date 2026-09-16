// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! WI-W4-02: oracle self-tests only; no production WrappedInterval is connected.
#[path = "support/wrapped_oracle.rs"]
mod wrapped_oracle;
use wrapped_oracle::{Oracle, Repr};

fn arc(lo: u32, hi: u32) -> Repr {
    Repr::Arc { lo, hi }
}

#[test]
fn familiar_four_bit_examples() {
    let o = Oracle::new(4).unwrap();
    for (r, expected) in [
        (Repr::Empty, vec![]),
        (Repr::Full, (0..16).collect()),
        (arc(3, 6), vec![3, 4, 5, 6]),
        (arc(14, 2), vec![0, 1, 2, 14, 15]),
        (arc(5, 5), vec![5]),
    ] {
        assert_eq!(
            o.values(r).unwrap().elements().collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn exhaustive_membership_all_raw_arcs_widths_one_through_four() {
    for width in 1..=4 {
        let o = Oracle::new(width).unwrap();
        for r in o.raw_representations() {
            let expected = o.values(r).unwrap();
            // A second, endpoint-based definition cross-checks ring enumeration.
            let candidate = o.sample_membership(|x| match r {
                Repr::Empty => false,
                Repr::Full => true,
                Repr::Arc { lo, hi } if lo <= hi => lo <= x && x <= hi,
                Repr::Arc { lo, hi } => x >= lo || x <= hi,
            });
            expected.check_exact(&candidate).unwrap();
        }
    }
}

#[test]
fn exhaustive_normalization_preserves_sets_and_is_idempotent() {
    for width in 1..=4 {
        let o = Oracle::new(width).unwrap();
        for r in o.raw_representations() {
            let n = o.normalize(r).unwrap();
            o.values(r)
                .unwrap()
                .check_exact(&o.values(n).unwrap())
                .unwrap();
            assert_eq!(o.normalize(n).unwrap(), n);
        }
        let canonical = o.canonical_representations();
        assert_eq!(canonical.len(), (2 + o.size() * (o.size() - 1)) as usize);
        let mut sets = std::collections::HashSet::new();
        for r in canonical {
            assert!(sets.insert(o.values(r).unwrap().elements().collect::<Vec<_>>()));
        }
        for lo in 0..o.size() {
            assert_eq!(
                o.normalize(arc(lo, (lo + o.size() - 1) % o.size()))
                    .unwrap(),
                Repr::Full
            );
            assert_eq!(o.values(arc(lo, lo)).unwrap().cardinality(), 1);
        }
    }
}

#[test]
fn exhaustive_pairwise_set_oracle_widths_one_through_four() {
    for width in 1..=4 {
        let o = Oracle::new(width).unwrap();
        let sets: Vec<_> = o
            .canonical_representations()
            .into_iter()
            .map(|r| o.values(r).unwrap())
            .collect();
        for a in &sets {
            for b in &sets {
                let union = a.union(b);
                let intersection = a.intersection(b);
                for x in 0..o.size() {
                    assert_eq!(union.contains(x), a.contains(x) || b.contains(x));
                    assert_eq!(intersection.contains(x), a.contains(x) && b.contains(x));
                }
                a.check_contained_by(&union).unwrap();
                b.check_contained_by(&union).unwrap();
                intersection.check_contained_by(a).unwrap();
                intersection.check_contained_by(b).unwrap();
            }
        }
    }
}

#[test]
fn rejects_dropping_either_half_of_split_meet() {
    let o = Oracle::new(4).unwrap();
    let exact = o
        .values(arc(12, 6))
        .unwrap()
        .intersection(&o.values(arc(4, 14)).unwrap());
    assert_eq!(
        exact.elements().collect::<Vec<_>>(),
        vec![4, 5, 6, 12, 13, 14]
    );
    for bad in [arc(4, 6), arc(12, 14)] {
        assert!(exact.check_contained_by(&o.values(bad).unwrap()).is_err());
    }
    // Both are sound covers, not competing intersection components.
    for cover in [arc(4, 14), arc(12, 6)] {
        let candidate = o.values(cover).unwrap();
        exact.check_contained_by(&candidate).unwrap();
        assert!(exact.check_exact(&candidate).is_err());
    }
}

#[test]
fn rejects_broken_membership_and_widening_normalization() {
    let o = Oracle::new(4).unwrap();
    let expected = o.values(arc(14, 2)).unwrap();
    let broken = o.sample_membership(|x| x >= 14 && x <= 2);
    assert!(expected.check_exact(&broken).is_err());
    let full = o.values(Repr::Full).unwrap();
    expected.check_contained_by(&full).unwrap();
    assert!(expected.check_exact(&full).is_err());
}

#[test]
fn concrete_addition_reference_for_sponsor_example() {
    let o = Oracle::new(8).unwrap();
    let actual = o.binary_image(
        &o.values(arc(200, 210)).unwrap(),
        &o.values(arc(50, 60)).unwrap(),
        |x, y| Some((x + y) % o.size()),
    );
    actual
        .check_exact(&o.values(arc(250, 14)).unwrap())
        .unwrap();
    assert_eq!(actual.cardinality(), 21);
    assert!(
        actual
            .check_contained_by(&o.values(arc(250, 255)).unwrap())
            .is_err()
    );
}

#[test]
fn empty_and_full_reference_cases() {
    let o = Oracle::new(4).unwrap();
    let empty = o.values(Repr::Empty).unwrap();
    let full = o.values(Repr::Full).unwrap();
    let one = o.values(arc(1, 1)).unwrap();
    assert_eq!(
        o.binary_image(&empty, &full, |x, y| Some((x + y) % 16)),
        empty
    );
    assert_eq!(o.binary_image(&full, &one, |x, y| Some((x + y) % 16)), full);
    assert_eq!(empty.union(&full), full);
    assert_eq!(empty.intersection(&full), empty);
}

#[test]
fn rejects_invalid_inputs_and_incomparable_universes() {
    assert!(Oracle::new(0).is_err());
    assert!(Oracle::new(9).is_err());
    let o = Oracle::new(4).unwrap();
    assert!(o.values(arc(16, 0)).is_err());
    assert!(o.values(arc(0, 16)).is_err());
    assert!(
        o.empty()
            .check_contained_by(&Oracle::new(3).unwrap().empty())
            .is_err()
    );
}
