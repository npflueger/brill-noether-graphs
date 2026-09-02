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
- The cross-one-off calculation uses a single residue convention throughout.
  The checked row formula and inversion count are given by the declarations in
  `Bananas/CrossOneOff/`, including
  `crossOneOff_cutoff_le_torsionOrder_of_not_both_two`.
- The pole-order term in the statement corresponding to Proposition 6.10 uses
  the sign appearing in `chain_word_poleOrder`.

The proved, paper-order index is [`TwiceMarkedBananas.lean`](../TwiceMarkedBananas.lean).
The Mathlib-only statement copy is
[`TwiceMarkedBananasStatements.lean`](../TwiceMarkedBananasStatements.lean).
