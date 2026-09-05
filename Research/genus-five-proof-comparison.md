# Comparing the six old genus-five proofs with discrete specialization

5 September 2026 (UTC).

The comparison concerns rows 01, 02, 03, 04, 07, and 13. Both implementations
prove the same `ClosedSubdivisionDharConstruction` statements, including
every permitted nonloopy forest contraction face. The candidate obtains
these statements from one canonical two-pole construction and a reusable
integer-rounding specialization theorem.

The specialization theorem formalized here transfers signed core-supported
winnability, and consequently ordinary divisor rank at least one. It does
not formalize the arbitrary-rank inequality in the
[mathematical note](discrete-specialization-by-rounding.md), or a general
semicontinuity theorem for Brill–Noether rank.

## Source size

Counts are physical Lean source lines, including comments and blank lines.
External packages are excluded. A dependency closure includes the indicated
modules and every local module they import transitively.

| Scope | Old modules | New modules | Old lines | New lines |
|---|---:|---:|---:|---:|
| Modules rebuilt for the six-row comparison | 11 | 12 | 6,020 | 3,030 |
| Entire local dependency closure of the six rows | 111 | 98 | 40,819 | 30,783 |
| Entire local dependency closure of the public genus-five theorem | 233 | 234 | 85,535 | 82,522 |

The first row includes all infrastructure needed by the candidate that is
not already shared by the two versions of the public theorem: nine utility
modules totaling 2,110 lines, plus three application modules. The reduction
is not obtained by hiding new generic proofs outside the count. Some
infrastructure no longer needed by these six rows remains necessary for
other genus-five rows, which explains the smaller reduction in the full
public closure.

Excluding blank lines and Lean comments, the compared modules contain
4,428 old lines versus 2,341 new lines, a 47.1% reduction. This secondary
count strips nested block comments and line comments while preserving
strings; it confirms that documentation formatting is not driving the
physical-line reduction.

## Timing protocol

This is a small engineering comparison: one serial pass per implementation,
old first, with `LEAN_NUM_THREADS=4`. Only the modules specific to the six-row
proof branch are rebuilt. Byte-identical dependencies shared by the full
public theorem remain cached, as do the pinned external packages. These
measurements are not cold builds of the entire repository.

Both arms use immutable source snapshots and separate output trees. Shared
local artifact families are captured once and linked into both trees;
neither arm can load replacement artifacts from the live workspace. Source
hashes and import closures are checked. A small Lean probe following each
arm checks all six results against identical closed-row statement types.
Probe time is reported separately from proof compilation.

The old ledger was read from Git `HEAD`; the remaining old sources came
from a captured working-tree baseline. Shared infrastructure is held fixed
between arms. The toolchain is Lean 4.33.0 on macOS 26.6.2, Apple Silicon.

The initial old-arm launch failed during import lookup, before proof
elaboration: Lean did not fall through from an arm's namespace directory
to the separate shared-cache directory. Linking the captured shared
artifacts into both arm trees fixed this. The failed launch is excluded
from the measurements.

Wall time and total CPU time are reported separately because this 8 GB
machine spends substantial elapsed time outside CPU execution. The
one-pass timings should not be read as statistically precise estimates.

The [measurement data](genus-five-proof-comparison.json) retain per-module
timings, measured source hashes, toolchain and snapshot information, and
both endpoint results. A comment-aware import audit confirmed the closure
counts; the shared compiled artifacts retained identical hashes throughout.

| Measurement | Old | New | Reduction |
|---|---:|---:|---:|
| Proof compilation, elapsed | 1,160.41 s (19m20s) | 897.10 s (14m57s) | 22.7% |
| Proof compilation, CPU | 215.89 s | 183.25 s | 15.1% |
| Endpoint probe, elapsed | 109.72 s | 87.63 s | — |
| Endpoint probe, CPU | 12.97 s | 10.83 s | — |
| Total including probe, elapsed | 1,270.13 s | 984.73 s | — |
| Total including probe, CPU | 228.86 s | 194.08 s | — |

Every compilation and both six-statement endpoint probes passed. These
results support replacement: approximately half the proof source, with
lower measured compilation cost in both elapsed and CPU time. They do not
establish the speedup of a full cold repository build.

## Replacement

The public construction ledger now uses the six theorems in
[GenusFiveTwoPoleClosed.lean](../LowGenus/GenusFiveTwoPoleClosed.lean).
The six old row modules and five exclusively used helpers were removed:

- `LowGenus.GenusFiveRow01`, `GenusFiveRow02`, `GenusFiveRow03`,
  `GenusFiveRow04`, `GenusFiveRow07`, and `GenusFiveRow13`;
- `LowGenus.ConfigurationReservoirChain`, `ConfigurationReservoirPair`,
  and `GuardingOrbit`;
- `Utilities.Subdivision.DegenerateCanonical` and
  `DegenerateRelabelingReaches`.

Their source hashes were checked against the captured baseline before
deletion, and the two library roots had the retired imports removed.
Independent generated checks remain available. The public theorem statement
is unchanged. After timing, the positive module's two-line header was
updated to describe the new closure; its proof code and line count did not
change.

## Validation

Both affected library roots built successfully after the replacement and
source retirement. The public existence theorem compiled with the new
closed-row constructions. Integration and the axiom audit can be reproduced
with:

```sh
LEAN_NUM_THREADS=4 lake build Utilities LowGenus
LEAN_NUM_THREADS=4 lake env lean Research/genus-five-specialization-audit.lean
```

The [audit file](genus-five-specialization-audit.lean) covers the common
rounding offset, the degree bound on firing scripts, quantitative
winnability and rank-one descent, all six closed constructions, and
`AtanasovRanganathan.brillNoetherExistenceThroughFive`.

The audit completed successfully. Every listed result depends only on
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional
axiom appears. The [complete output](genus-five-specialization-axioms.txt)
is retained alongside the audit source.
