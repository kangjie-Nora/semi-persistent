# Abstract Domains Proof Status

Last refreshed: 2026-09-20.

## Current result

```text
cargo verus verify
1015 verified, 0 errors
```

The project source contains no executable `admit()` or `assume()` calls. CI
enforces that policy with a source scan and runs ordinary Verus verification.
The pinned `vstd` dependency contains admitted specifications; global
`--no-cheating` fails while compiling `vstd` before reaching this crate. Those
dependency specifications, Verus, and the solver remain part of the trust
boundary.

Enabled executable widths:

- `d8` (`u8`)
- `d16` (`u16`)
- `d32` (`u32`)
- `d64` (`u64`)

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. Do not describe `u128` as an enabled or
verified executable instance of the existing d* domains. The separate
Wrapped<u128>/Wrapped<i128> membership implementations described below do verify.

The separate Rust mirror suite contains 32 tests:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `ReducedProduct` | `reduce`, `add` |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. `ReducedProduct::add` composes the four component containment
postconditions and then applies the proved containment of `reduce`.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
Unum conversions/arithmetic helpers, and ReducedProduct bitwise operations,
subtraction, multiplication, division, shifts, joins, meets, and negation.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.


## Wrapped membership

`Wrapped<T>::contains` verifies `result == self.has(x)` for u8/u16/u32/u64/u128
and i8/i16/i32/i64/i128. This is membership/spec correspondence, not an arithmetic
transfer containment theorem. The macro expansion fix allows ordinary Rust and
Verus to process the same implementations. An explicit `Clone` implementation for `T: Copy` verifies `result == *self`;
all ten supported integer types satisfy this bound. No warning suppression or
proof escape was added.

The membership subset contains 10 production tests:
exhaustive u8/i8 endpoint/value combinations and sampled boundary cases for all
wider types. `wrapped_oracle` has 13 reference self-tests. The current totals including normalization are listed below; one doctest is ignored.
Executable normalize now verifies exact membership preservation for all ten types:
`forall|x| result.has(x) == self.has(x)`. Nine additional normalization tests bring
the production target to 19 tests; an additional Clone regression brings
the current totals to 20 production tests and 65 passing crate tests.
Canonical output and idempotence are tested, not separate verified postconditions.
Raw full-circle Arc values remain constructible; callers must invoke normalize.
Join/meet and wrapped arithmetic remain unimplemented and unverified here.
