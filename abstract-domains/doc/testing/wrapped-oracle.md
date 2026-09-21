# Wrapped Interval oracle (WI-W4-02)

This PR provides an independent finite-set reference and an exhaustive test
harness. Production `Wrapped<T>::contains` is now connected in a separate
`wrapped_membership` test target. Production normalization is also connected; join/meet and arithmetic remain
outside this integration.

## Run

From the repository root:

```sh
cargo test -p semi-persistent-abstract-domains --test wrapped_oracle
cargo test -p semi-persistent-abstract-domains --test wrapped_membership
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
These 1–4 bit tests exercise the reference only. Production membership coverage
is described below.
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

## Production membership integration (2026-09-19; validation superseded below)

PR #2 was merged into this fork's main and integrated into the test branch.
It supplies `Wrapped<T>` for u8/u16/u32/u64/u128 and i8/i16/i32/i64/i128.
The macro now expands to a `verus!` block so generated specification syntax is
processed before Rust parses the implementation. This fixes the compile error
in the imported representation. The membership algorithm is unchanged.

`wrapped_membership.rs` calls actual production `contains`:

- Exhaustive u8 and i8 membership: every raw endpoint pair plus Bottom and Top,
  each checked at every 8-bit pattern (33,555,456 checks across both types).
  Expected sets come from the independent 8-bit ring-walking oracle. Signed
  operands preserve the same bit patterns via u8-to-i8 casts.
- The prepared sparse u32 checker is connected to real Wrapped<u32> values.
- Eight additional tests cover all wider unsigned and signed types, including
  minima, maxima, zero, the sign boundary, endpoints and adjacent values.
  Expectations use unsigned wrapping distance, independent of signed ordering.
  These are sampled wider-width checks, not exhaustive testing of those widths.

The 13 original oracle self-tests remain separate from these 10 production tests.
The full crate test run passes 55 tests (32 existing, 13 oracle, 10 production),
with one ignored doctest. `cargo verus verify` reports 1005 verified, 0 errors.
The executable membership contract `result == self.has(x)` verifies for all ten
implementations. A warning remains for the derived Clone lacking an explicit
specification; this is not a membership verification failure.

## Production normalization integration (2026-09-20)

Integrated Vignesvern's normalize implementation from commit 61c304c, retaining
the macro expansion fix. Full-circle arcs become Top; other values are unchanged.
Its universal membership-preservation contract verifies for all ten types.

Nine additional production tests compare normalized u8/i8 values with the
independent ring oracle across all raw representations and concrete values.
They also check canonical output and idempotence. Wider types have boundary
checks for full-circle arcs, singletons, signed/unsigned extrema, exact sampled
membership and idempotence. These wider checks are not exhaustive.

The full crate now has 64 passing tests (32 existing, 13 oracle, 19 production)
and one ignored doctest. Verus reports 1015 verified, 0 errors, with the existing
derived Clone warning. Canonical output and idempotence are tested; the new
universal postcondition proves exact membership preservation, not separate
canonicality/idempotence postconditions.

The public enum still permits raw full-circle Arc construction; callers must
invoke normalize to obtain canonical values. constant/is_top/is_bottom remain
spec-only. No join/meet, wrapped arithmetic or conversion is implemented here.
Later operations should normalize their outputs under the agreed convention.

Only use exhaustive small-width operation tests for implementations with matching
width semantics. Wider tests remain sampled. Algebraic laws must be considered
individually because wrapped intervals are not an ordinary lattice.
