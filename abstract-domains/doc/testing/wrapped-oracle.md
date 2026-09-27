# Wrapped interval verification and oracle tests

## Public interface

`wrapped::Wrapped<W: Word>` is a single domain per bit width. The current Word
instances are u8, u16, u32 and u64. Signed interpretation uses the same bit
patterns; signedness belongs to transfer semantics, not a second domain type.
No u128 Word implementation is currently provided.

The private representation is Top or a nonempty clockwise arc. `new(lo, hi)`
converts every full-circle arc to Top; callers cannot construct a raw arc.
`constant` is executable. `wf` excludes full-circle arcs, and `lemma_canonical`
proves that equal concretizations of well-formed values imply structural equality.
`is_top` is equivalent to containing the entire universe for well-formed values.

Membership compares clockwise distances from lo. Distance is x-lo when x>=lo
and 2^N-lo+x otherwise: the nonnegative modular distance, including wraparound.
`contains` proves equivalence to `Domain::gamma`. `lemma_nonempty` proves that
all well-formed inner values contain a concrete word. Empty results and lifted
operations use the shared `lattice::BotOr`, not a domain-specific wrapper.

## Domain operations

`leq`, `join`, `meet` and `widen` implement the shared Domain contracts against
gamma. Join chooses the smaller covering arc; split meet preserves both exact
intersection components and chooses their smaller cover. Equal-size choices use
the unsigned lower endpoint. These operations are not ordinary lattice joins
and meets; associativity and monotonicity must not be assumed.

Meet additionally proves Bot if and only if the exact intersection is empty.
Widen leaves contained inputs unchanged. Otherwise it accepts the joined arc only
when cardinality at least doubles, and jumps to Top for smaller growth. Thus an
unstable step increases cardinality by at least a factor of two, capped at 2^N;
the measure is the number of remaining doublings. The shared formal widening
contract proves soundness; the growth policy is additionally runtime-tested.

## Tests and limits

- 13 independent oracle self-tests cover small model widths, reference operations
  and sparse u32 cases. They are not production arithmetic verification.
- The production membership test enumerates all 65,536 u8 endpoint pairs and
  every u8 value. It checks the same bits under signed reinterpretation and
  records one canonical representation per concrete set, including Top.
- The operation test covers 66,049 ordered pairs from 16 sampled endpoints plus
  Top, checking all 256 values per pair. It checks containment, exact leq,
  Bot iff disjoint, symmetry, minimum covering cardinality via an independent
  longest-gap oracle, and widening growth. This is not every possible u8 pair.
- A split-intersection regression and actual shared BotOr lifting are exercised.
- Four-width boundary tests include constants, sign boundaries and full circles.

```sh
cargo test -p semi-persistent-abstract-domains
cargo verus verify --manifest-path abstract-domains/Cargo.toml
```

Use the versions pinned by the repository. Proof totals and scope are recorded
in `doc/proof-status.md`. Arith/DivRem transfers, pole splitting, bitwise operations,
shifts, casts and comparisons are not implemented by this core port. The Domain
port does not claim the full Wrapped arithmetic roadmap is complete.
