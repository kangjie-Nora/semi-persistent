# Sign representation and exact set operations

Based on Vignesvern's PR #5 (`feature/sign-domain`, 1f4bcd3), independently
integrated on the first-stage `kangjie` base 3750fd6. Wrapped week-two work is
in a separate branch and is not a dependency of this change.

## Representation and interface

`sign::Sign` contains seven nonempty states: Neg, Zero, Pos, NonPos, NonNeg,
NonZero, Top. `domains::AbstractValue<Sign>` adds the only empty state, Bot.
There is no `_Marker` variant: in the original generic enum, its `has` predicate
was false, permitting a second empty representation inside NonBot.

Sign no longer carries a machine-width parameter. The mathematical predicate
`has(x: int)` describes integer signs; `contains(x: i128)` checks it at runtime.
All signed primitive widths embed losslessly in i128 (`x as i128`). This change
replaces the proposed `Sign<T>` interface; there were no existing callers on the
base branch. It does not define unsigned sign domains or machine arithmetic
transfers. Future arithmetic must explicitly choose overflow semantics.

`from_value` returns Neg, Zero or Pos; it abstracts the sign, not the magnitude.
Nonempty Sign join returns Sign; meet returns AbstractValue<Sign>. Specialized
lifted join/meet/contains on AbstractValue<Sign> support empty inputs. This is
not a generic Domain trait or an implementation for all AbstractValue<D>.

## Verified contracts

- contains is exactly equivalent to mathematical has for its concrete argument.
- join has(x) iff either input has(x), for every mathematical integer x.
- meet has(x) iff both inputs have(x), for every mathematical integer x.
- Both lifted operations have the same exact set contracts, including Bot.
- from_value contains its source value; Clone preserves equality.

These exactness proofs imply no missing or extra values for set union and
intersection. This is stronger than containment alone and differs from Wrapped,
where a single arc cannot always represent the exact set operation.

## Tests and evidence

Eight new tests call the production implementation. An independent three-category
set model checks all 64 pairs of the eight states for every i8 value, plus
boundary values for i8/i16/i32/i64/i128. Tests require canonical Bot exactly when
the intersection is empty. All 512 triples are checked for associativity and
distributivity; tests also check commutativity, idempotence, absorption, Bot/Top
identities, construction and cloning. Lattice laws are runtime checks, not
separate Verus proof functions.

Validation: 66 crate tests passed (58 existing plus 8 Sign tests), one ignored
doctest. Crate Verus result: 1024 verified, 0 errors. Dependency verification
counts are not part of this crate total.

Out of this PR: Sign arithmetic transfers, Sign–Interval reduction, unsigned
semantics, generic domain interfaces, and e-graph integration.
