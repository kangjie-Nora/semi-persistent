# Wrapped join/meet: second-stage work

This draft starts from the first-stage representation and oracle integration at
3750fd6. It records planned work, not completed operations or approved interfaces.
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

## Current status

Only this planning document is added initially. Join/meet implementations,
production tests, tie-break policy and new proofs are pending. No new runtime or
verification result is claimed by this documentation-only change.
