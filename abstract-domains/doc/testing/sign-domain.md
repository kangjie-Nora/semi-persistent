# Signed-width Sign domain

## Representation and semantics

`Sign<T>` supports i8, i16, i32, i64 and i128. Membership takes a concrete
value of that same signed type, interpreted in two's complement. The seven
nonempty states are Zero, Pos, Neg, NonNeg, NonPos, NonZero and Top.
`AbstractValue<Sign<T>>::Bot` is the only empty state. Top holds PhantomData<T>;
there is no additional marker variant. A verified nonemptiness lemma provides
one of -1, 0 or 1 as a concrete witness for every inner state. Consequently no
separate well-formedness precondition is required to exclude invalid states.

`from_value` returns the sign of a concrete value; `top` represents every value
of the selected type. `contains` agrees exactly with `has`. `refines(a,b)` is
true exactly when every value represented by a is also represented by b.
Sign::join returns a nonempty Sign; Sign::meet can return Bot. Specialized outer
operations on AbstractValue<Sign<T>> support Bot inputs directly.

## Verified contracts

At each supported width:

- contains is equivalent to has; Clone preserves equality; constructors are sound.
- refines is equivalent to universal concrete-set inclusion, including outer Bot.
- join and meet have exact union/intersection contracts, not only containment.
- Outer executable join/meet equal their specification functions union/intersection.
- lattice_laws proves commutativity, associativity, idempotence, absorption,
  Bot/Top identities, upper/lower-bound properties, reflexivity, antisymmetry,
  transitivity, and union/intersection monotonicity under subset.

The executable/specification correspondence connects these laws to the runtime
operations. No arithmetic-transfer or arithmetic-monotonicity theorem is claimed.

## Tests

The independent oracle represents each state as a subset of {negative, zero,
positive}. Tests check every pair of eight states over all i8 values for membership,
refinement, exact union/intersection and canonical Bot results. Every supported
width also tests MIN/MAX, adjacent values, -1/0/1, constructors, cloning and all
512 triples for lattice/order properties.

Boundary regressions interpret MAX.wrapping_add(1), MIN.wrapping_sub(1), and
MIN.wrapping_neg() using native signed types. These test concrete interpretation;
they do not constitute abstract neg/add/sub implementations.

```sh
cargo test -p semi-persistent-abstract-domains --test sign
```

Run `cargo verus verify` from `abstract-domains` for the proofs. The complete
verification inventory is recorded in `doc/proof-status.md`.

## Deferred arithmetic

Future neg/add/sub transfers use fixed-width two's-complement wrapping semantics.
When signs alone cannot establish a narrower sound result, a documented Top
result is permitted and still needs a containment proof. In particular, Pos+Pos
cannot generally return Pos, and negating MIN leaves a negative value.
Mathematical-integer `_math` transfers are not part of this interface.
Multiplication is stretch scope. Division, min/max transfers, product reduction
and e-graph integration are not provided by this module.
