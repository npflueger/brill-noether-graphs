# Formalization notes for the twice-marked banana results

The Lean statements occasionally make conventions or hypotheses explicit where
the published notation leaves them implicit. The principal differences are
listed here so that the relationship between the source and the checked
statements is transparent.

- A vertex shared by two strands has more than one coordinate description.
  Statements involving endpoint coordinates therefore use equality of the
  represented vertices, or impose interiority when equality of coordinate
  pairs is required.
- The same-strand rank-zero argument includes the hypothesis
  `rank (w + u) = 0`; this excludes the reflected rank-one case.
- Over natural numbers, the large-period threshold is written
  `g + 2 ≤ 2 * k`.
- The counting argument corresponding to Proposition 6.1 uses the interval
  through the second coordinate `b'`, as implemented in
  `CrossOneOff/CrossingInversionCount.lean`.
- In the iterated-gluing construction, each successive factor is glued to the
  graph obtained at the preceding step.
- Results involving a positive torsion order state both distinctness of the
  marks and exactness of the order explicitly.
- The checked classification includes the length-two midpoint family captured
  by `CorrectedMidpointException`; the corresponding checked statements include
  `corrected_bananaSimple`, `corrected_banana_torsion_classification`, and
  `corrected_highGenus_banana_not_kGeneral`.
- Revised Lemma 4.33 (`lem-midpointTorsion`) is proved in
  `Bananas/Transmission/MidpointTorsion.lean`. Both assertions appear in the
  proved index and statement-only challenge as `s4_lem4_33a` and `s4_lem4_33b`:
  no positive even multiple through `2g - 2` is principal, and no positive
  multiple below `g` is principal. These statements concern any proposed
  period, not just the exact torsion order. The proof follows the manuscript's
  quotient/remainder reduction and Dhar argument using the existing reduced
  normal forms; the zero-remainder case absorbs the residue chip into the left
  endpoint. The library proves the reflected case as well, and only needs the
  first mark to be a midpoint (its strand need not have length two).
  Proposition 4.19 now uses this result in its length-two branch. The obsolete
  length-two slope argument has been removed; slope results needed for the
  endpoint and near-opposite branches remain.
- Revised Lemma 4.34 (`lem-midpointSubmodularity`) appears as `s4_lem4_34`
  in both indexes. Its library theorem `length_two_midpoint_allSubmodular`
  in `Bananas/CrossOneOff/LengthTwoCrossMonotonicity.lean` includes genus one
  and two: the existing underlying rank proof has no high-genus restriction.
  The older `NSMForBananaLengthTwoCrossException` now specializes this theorem
  for the high-genus classification. The manuscript follows the same proof;
  the normalization and endpoint-debt details are explained below.
- The cross-one-off calculation uses a single residue convention throughout.
  The checked row formula and inversion count are given by the declarations in
  `Bananas/CrossOneOff/`, including
  `crossOneOff_cutoff_le_torsionOrder_of_not_both_two`.
- The pole-order term in the statement corresponding to Proposition 6.10 uses
  the sign appearing in `chain_word_poleOrder`.

The proved, paper-order index is [`TwiceMarkedBananas.lean`](../TwiceMarkedBananas.lean).
The Mathlib-only statement copy is
[`TwiceMarkedBananasStatements.lean`](../TwiceMarkedBananasStatements.lean).

## Lemma 4.34: proof comparison and suggested clarification

The manuscript's argument is faithful to the Lean proof: canonical duality
reduces to degree at most `g`; a reduced normal form gives nonnegative endpoint
coefficients; the presence of the midpoint chip determines whether deleting
that chip drops rank; and normalizing deletion on the other strand preserves
the occupied midpoint. The `a = b = 0` case is handled by semibreak support
and Dhar burning in both proofs. If the initial divisor has rank `-1`, all
three deletions also have rank `-1`, so its second difference is zero; spelling
this out explains the assumption `r(D) ≥ 0`.

The final paragraph would benefit from explicit normalization formulas. The
stated lower bounds `a' ≥ a - 1` and `b' ≥ b - 1` alone do not establish all
hypotheses of Corollary 2.24 (`cor-BanaRankComp`): an endpoint coefficient may
be `-1`, and the upper bounds involving `deg E'` must also be checked. The
following is a suggested expansion of that step, using `L = v_{0,0}`,
`R = v_{0,2}`, `n = n_1`, and `v_s = v_{1,s}`.

Write `D = aL + bR + E`, with `a,b ≥ 0`, `a+b+deg E ≤ g`, and `a+b > 0`.
In the contradictory case the midpoint `u` belongs to `E`. On strand 1,
there is either no chip of `E`, or a unique chip `v_ℓ`. The following choices
give `D-v_j ∼ D' = a'L+b'R+E'`:

| Chip on strand 1 | `a'` | `b'` | `E'` |
| --- | --- | --- | --- |
| None | `a-1` | `b-1` | `E + v_{n-j}` |
| `v_ℓ`, with `ℓ < j` | `a` | `b-1` | `E - v_ℓ + v_{n+ℓ-j}` |
| `v_ℓ`, with `ℓ = j` | `a` | `b` | `E - v_j` |
| `v_ℓ`, with `ℓ > j` | `a-1` | `b` | `E - v_ℓ + v_{ℓ-j}` |

These are precisely the empty-strand, tail-sum, reflected-pair, and
head-excess cases in the Lean proof, after choosing the normalized orientation.
Every new chip in the table is interior. In every case `E'` is effective,
has at most one chip on each strand, and retains the chip at `u`. Moreover,

- `a',b' ≥ -1`, and at least one is nonnegative;
- `a'+deg E' ≤ g` and `b'+deg E' ≤ g`;
- `deg D' = deg D - 1 ≤ g - 1`.

Corollary 2.24 therefore applies both to `D'` and to `D'-u`. Since
`min(a',b') ≥ -1` and their degree-minus-genus terms are at most `-1`, it
gives `r(D') = min(a',b') = r(D'-u)`. This contradicts the rank drop required
by `Δ(D) = -1`. This explicit check justifies the manuscript's sentence
claiming that the new divisor again satisfies the rank formula's hypotheses,
including the endpoint coefficient `-1` cases.

The analogous earlier use of the rank formula for `D-u` is valid after the
`a=b=0` case has been excluded: when `u` is absent from `E`, the representative
has coefficients `a-1,b-1` and semibreak part `E+u`, so at least one endpoint
coefficient remains nonnegative. Mentioning this makes that boundary case
transparent as well.
