# Wrapped Interval oracle (WI-W4-02)

This PR provides an independent finite-set reference and an exhaustive test
harness. It does **not** implement a production WrappedInterval or prove its
soundness in Verus. No Vignesvern implementation is connected yet.

## Run

From the repository root:

```sh
cargo test -p semi-persistent-abstract-domains --test wrapped_oracle
```

The harness only uses the Rust standard library. It can also run without building
the domain crate (choose an output path for the temporary executable):

```sh
rustc --edition=2024 --test abstract-domains/tests/wrapped_oracle.rs -o /tmp/wrapped-oracle-tests
/tmp/wrapped-oracle-tests
```

## Reference semantics

The oracle supports test universes of 1 through 8 bits. Exhaustive self-tests use
widths 1 through 4; the sponsor's addition example uses 8 bits. These are test
widths, not verified production u16/u32/u64 instances.

- `Empty` represents no values; `Full` represents all values in the universe.
- `Arc { lo, hi }` visits lo, lo+1, ... modulo 2^width, stopping at hi inclusive.
- Equal endpoints represent a singleton.
- An arc covering the entire universe normalizes to explicit Full. For example,
  in four bits both Arc(0,15) and Arc(5,4) normalize to Full.
- Out-of-range endpoints are rejected rather than silently reduced modulo width.

These are explicit test conventions to review with the implementation owner.
The reference enumerates by walking the ring. A separate endpoint-comparison
membership definition cross-checks the enumerator. Canonical representations
must have distinct represented sets; normalization preserves the set and is
idempotent.

## Coverage and limits

For widths 1..=4, test every raw endpoint pair and each concrete value, every
normalization case, and every pair of canonical representations for the concrete
set union/intersection oracle. There are 4, 14, 58, and 242 canonical values,
respectively (2 + N*(N-1)). This covers 62,140 ordered canonical pairs in total.
It is NOT exhaustive testing of production operations, which are not connected.
Arithmetic reference checks are selected examples, not an exhaustive arithmetic
claim. A `binary_image` callback supplies the concrete operation semantics.
Returning None models absence of a successful value only; division alarms need
separate tests and are not implemented here.

Negative tests deliberately reject:

- wrapped membership implemented with AND instead of OR;
- a normalization that widens a non-full arc to Full;
- either discarded component of a split intersection;
- the high-only part of a wrapped addition result;
- invalid endpoints, unsupported oracle widths and mismatched universes.

For the 4-bit intersection of Arc(12,6) and Arc(4,14), the exact result is
{4,5,6,12,13,14}. Returning just [4,6] or just [12,14] is unsound. Either input
arc is a sound but inexact cover in this example. This PR deliberately does not
choose or implement a join/meet algorithm or tie-break policy.

## Connecting the production implementation later

Keep the reference independent of the production membership algorithm:

1. Translate a reference Repr to the actual constructor (adapt enum names and
   canonicalization conventions after agreement).
2. Use `Oracle::sample_membership` with executable production membership to
   collect the values represented by its result. If membership is spec-only,
   use a reviewed executable decoder instead; do not claim that a Rust mirror
   itself establishes correspondence with Verus definitions.
3. For constructors, membership and normalization, use `check_exact`.
4. For join, compare the concrete union with the candidate using
   `check_contained_by`; for meet use the concrete intersection. Do not demand
   exactness when one arc cannot express the exact answer.
5. For arithmetic, enumerate concrete operands via `binary_image` using the
   agreed modular, signedness and error semantics, then check containment.
6. Run identical inputs repeatedly to check the selected deterministic policy.
   Algebraic laws must be assessed individually: wrapped intervals do not form
   an ordinary lattice. One-way containment alone does not prove a narrowing
   operation or all properties needed by the later e-class analysis.

Start with 4-bit exhaustive operations to control runtime. Keep a documented
coverage boundary for any larger-width or sampled checks. Generic comparison
helpers can be reused for conversion tests: ordinary-to-wrapped conversion may
be exact, while wrapped-to-one-ordinary-interval may require a sound cover.
Do not assert set equality for an unrepresentable conversion.

## Verification status

This adds ordinary Rust tests and documentation only, with no production source
or verification-contract changes and no new dependencies. Passing these tests
means the oracle passed its self-checks. Production adapter tests and universal
Verus containment proofs remain future work. Consequently, no new verified
operation is added to `doc/proof-status.md` by this PR.
