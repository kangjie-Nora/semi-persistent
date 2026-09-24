# Wrapped join and meet

`Wrapped<T>` represents nonempty arcs and Top. Empty intersection results use
`AbstractValue::Bot`.

## Required semantics

- Join must contain every value represented by either operand.
- Meet must contain every value common to both operands; a detected empty
  intersection must be represented by `AbstractValue::Bot`.
- If an exact intersection has two disconnected components, do not discard
  either. A single-arc result must soundly cover both, without losing values.
- Result selection is deterministic and independent of argument order.
- Normalize nonempty outputs under the existing full-circle-to-Top convention.
- Wrapped is not an ordinary lattice. Do not assume approximate meet refines
  both inputs, or claim all lattice laws without establishing them.

## Precision policy

Follow the biased over-join and over-meet design in Gange et al.,
*Interval Analysis and Machine Arithmetic*, sections 3.2–3.3 / Figure 4:
https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf

- Split intersection: both original arcs cover the two exact components. Choose
  the smaller arc.
- Disjoint union: consider Arc(l1,h2) and Arc(l2,h1). Choose the smaller cover.
- Compare unsigned modular endpoint distances (cardinality minus one). This
  avoids overflow for a full 128-bit circle. Signed types use the corresponding
  unsigned type for the comparison, preserving bit-pattern semantics.
- Break size ties by the numerically smaller unsigned start bits. This makes the
  choice independent of argument order. Normalize nonempty results.

For example, meet(Arc(250,6), Arc(4,252)) covers both [4,6] and [250,252]
with Arc(250,6), regardless of argument order. Join([0,0],[128,128]) chooses
Arc(0,128) over the equally sized Arc(128,0).

This is a minimum-cardinality covering-arc algorithm; it does not make Wrapped
an ordinary lattice. Associativity and monotonicity must not be assumed, and
an approximate meet need not be contained in both operands. Universal Verus
contracts prove containment only, not optimality or commutativity.

## Tests

The 14 join/meet tests include a regression requiring the union of Arc(0,1)
and the full-circle Arc(1,0) to contain every u8 value.

 The independent finite-set oracle checks
66,049 ordered pairs from Top and 256 endpoint combinations (16 chosen u8
endpoints), at all 256 concrete values per pair. It additionally compares result
cardinality with 256 minus the longest uncovered circular gap in the exact
union/intersection, handles empty intersections, and checks argument-order
independence. This is NOT exhaustive over all u8 arcs. Boundary checks across
all ten types check symmetry as well; dedicated signed/unsigned tie witnesses
check the unsigned tie-break. These finite precision checks are not universal
optimality proofs.

Reproduce the runtime checks with:

```sh
cargo test -p semi-persistent-abstract-domains --test wrapped_join_meet
```

Run `cargo verus verify` from `abstract-domains` for the containment proofs.
The current verification inventory is recorded in `doc/proof-status.md`.
