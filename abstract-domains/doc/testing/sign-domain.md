# Sign representation and exact set operations

## Representation and interface

`sign::Sign` contains seven nonempty states: Neg, Zero, Pos, NonPos, NonNeg,
NonZero, Top. `domains::AbstractValue<Sign>` adds the only empty state, Bot.
Sign is independent of machine width. The mathematical predicate `has(x: int)`
describes integer signs; `contains(x: i128)` checks it at runtime. All signed
primitive widths embed losslessly in i128 (`x as i128`). The `_math` arithmetic transfers use unbounded mathematical integers, without
overflow. They must not be bound to wrapping machine-integer operators.

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

## Mathematical arithmetic

`neg_math`, `add_math`, `sub_math`, `mul_math`, `min_math`, and `max_math`
implement the sign rules for mathematical integers, following the extended sign
domain in section 4.2 of Miné's *Tutorial on Static Inference of Numeric
Invariants by Abstract Interpretation*. Their contracts quantify over Verus int,
not i128 machine arithmetic. For example, Pos + Pos returns Pos even when
concrete operands would overflow a machine type. The transfer implementation
operates on sign states only and never performs that machine addition.

Each operation proves containment of every corresponding mathematical result.
Subtraction composes negation and addition. Multiplication sign lemmas use
nonlinear arithmetic proofs. Specialized AbstractValue<Sign> operations propagate
Bot when an input is empty. Arithmetic contracts promise containment, not exact
sets of integer magnitudes or formally optimal precision.

Division is not implemented: it requires an explicit quotient rounding convention
and a result/alarm policy for possible zero divisors. Sign–Interval reduction and
machine-wrapping transfers are separate operations.

## Tests and evidence

Eight representation/set-operation tests call the production implementation. An independent three-category
set model checks all 64 pairs of the eight states for every i8 value, plus
boundary values for i8/i16/i32/i64/i128. Tests require canonical Bot exactly when
the intersection is empty. All 512 triples are checked for associativity and
distributivity; tests also check commutativity, idempotence, absorption, Bot/Top
identities, construction and cloning. Lattice laws are runtime checks, not
separate Verus proof functions.

Run the production tests with:

```sh
cargo test -p semi-persistent-abstract-domains --test sign
```

Run `cargo verus verify` from `abstract-domains` for the exact set contracts.
The current verification inventory is recorded in `doc/proof-status.md`.

Three arithmetic tests additionally enumerate every i8 operand pair for every
abstract input-state pair, promote inputs to i128, and check concrete add/sub/mul/
min/max results. Every returned sign category must have a finite concrete witness.
Boundary tests use checked i128 arithmetic; overflowing concrete calculations are
skipped, not treated as passing examples. Universal mathematical containment is
covered by Verus, including results outside i128. A regression distinguishes the
mathematical positive sum 127+1 from its negative i8 wrapping result.

Division, Sign–Interval reduction, unsigned semantics and e-graph integration are
not implemented by this module.
