# Wrapped join/meet: second-stage work

This draft starts from the first-stage representation and oracle integration at
3750fd6. It records the implemented operations, validation, and remaining integration work.
Development uses `wrapped-join-meet`; `kangjie` remains the first-stage review
branch. Initially target the draft PR at `kangjie` so its diff contains only the
second-stage work. Incorporate first-stage review fixes as needed and rebase or
retarget after the upstream first-stage PR is merged.

## Coordination

Continue the pair's implementation/testing split: Vignesvern focuses on the
production operations; Kangjie prepares oracle cases and connects production
tests. Coordinate contracts and proof work together before editing the same
functions. Confirm exact signatures and responsibility for wrapper lifting first.
The current representation is `AbstractValue<Wrapped<T>>`, with Bot outside the
nonempty Wrapped domain. Do not introduce a second shared wrapper.

## Required semantics

- Join must contain every value represented by either operand.
- Meet must contain every value common to both operands; a detected empty
  intersection must be represented by `AbstractValue::Bot`.
- If an exact intersection has two disconnected components, do not discard
  either. A single-arc result must soundly cover both, as advised by Remi.
- Repeated calls on identical inputs must select the same result. Agree on the
  tie-break rule and whether commutativity is required before asserting it.
- Normalize nonempty outputs under the existing full-circle-to-Top convention.
- Wrapped is not an ordinary lattice. Do not assume approximate meet refines
  both inputs, or claim all lattice laws without establishing them.

## Planned tests and proof obligations

- Use the independent finite-set oracle for exact union/intersection references.
  Compare production results for containment; demand exactness only where the
  agreed operation specification requires it. Record precision separately.
- Cover Bot, Top, singletons, identical operands, containment, disjoint arcs,
  overlapping arcs, wrap-around and split intersections.
- Exhaustively compare small-width production operations only at their actual
  supported width. Estimate pair/value enumeration cost before choosing a full
  u8 run; a four-bit reference alone does not validate a fixed-u8 implementation.
- Add signed/unsigned and wider boundary cases matching the actual semantics.
- Prove production operation containment and any agreed additional contracts in
  Verus, including conservative Top results. Add no admit/assume proof escapes.
- Run the affected runtime tests and pinned Verus verification; update
  proof-status and document precision limitations and any remaining work.

## Current implementation and evidence

Integrated only Wrapped join/meet from Vignesvern's a269434 (PR #6); that PR
also contains Sign code, which is deliberately deferred to a separate stage.
The original join failed the concrete oracle: joining Arc(0,1) with the
full-circle Arc(1,0) lost value 2. Two fixes distinguish mutual endpoint
containment (return Top), and select a containing operand only when BOTH of
its counterpart's endpoints are included. Equal endpoints are compared directly
rather than relying on derived PartialEq in proof reasoning. All returned
nonempty values are normalized.

Both methods prove universal containment for all ten primitive types.

## Precision policy (revised)

Follow the biased over-join and over-meet design in Gange et al.,
*Interval Analysis and Machine Arithmetic*, sections 3.2–3.3 / Figure 4:
https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf

- Split intersection: both original arcs cover the two exact components. Choose
  the smaller arc, rather than always returning the left operand.
- Disjoint union: consider Arc(l1,h2) and Arc(l2,h1). Choose the smaller cover,
  rather than always returning Top.
- Compare unsigned modular endpoint distances (cardinality minus one). This
  avoids overflow for a full 128-bit circle. Signed types use the corresponding
  unsigned type for the comparison, preserving bit-pattern semantics.
- Break size ties by the numerically smaller unsigned start bits. This makes the
  choice independent of argument order. Normalize results as before.

For example, meet(Arc(250,6), Arc(4,252)) covers both [4,6] and [250,252]
with Arc(250,6), regardless of argument order. Join([0,0],[128,128]) chooses
Arc(0,128) over the equally sized Arc(128,0).

This is a minimum-cardinality covering-arc algorithm; it does not make Wrapped
an ordinary lattice. Associativity and monotonicity must not be assumed, and
an approximate meet need not be contained in both operands. Universal Verus
contracts prove containment only, not optimality or commutativity.

Validation: 14 new join/meet tests. The independent finite-set oracle checks
66,049 ordered pairs from Top and 256 endpoint combinations (16 chosen u8
endpoints), at all 256 concrete values per pair. It additionally compares result
cardinality with 256 minus the longest uncovered circular gap in the exact
union/intersection, handles empty intersections, and checks argument-order
independence. This is NOT exhaustive over all u8 arcs. Boundary checks across
all ten types check symmetry as well; dedicated signed/unsigned tie witnesses
check the unsigned tie-break. These finite precision checks are not universal
optimality proofs.

Full crate: 72 tests pass, one ignored doctest. Verus: 1036 verified, 0 errors.
No Sign implementation or generic production lifted join/meet is added.
Generic AbstractValue lifted-operation ownership and final sponsor review remain
separate integration work; the previous left-biased/Top precision fallbacks
are no longer pending decisions.
