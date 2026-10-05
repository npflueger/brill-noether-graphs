module

public import DraismaVargasCount.DiagonalClassification
public import DraismaVargasCount.BallotCoreIdentification

@[expose] public section

/-!
# The base count from the exhaustion package

This module turns `BallotSlopes.DiagonalClassification` into the count of open classes
of odd multiplicity over the caterpillar of loops.  The ballot family members of
`BallotCoreIdentification` are open, of odd multiplicity and diagonal, and realise every
ballot diagonal; together with `DiagonalClassification` they form a
`CaterpillarBallot.BallotClassification`, so the open odd count is the Catalan number
`catalan (m + 1)`, which is five in genus six.  This is the count of Vargas, Part II
(arXiv:2609.09109), `prop-divisors-on-chain`, for the open classes of odd multiplicity;
`CaterpillarAllMembers` uses it for the base count, step 1 of `Assembly`.

## What is proved

* `ballotClassification'` -- a `CaterpillarBallot.BallotClassification m request`
  from `BallotSlopes.DiagonalClassification m request` and a positive request,
  with every family-side argument proved.
* `openOddCount_eq_catalan'` -- the open odd count is `catalan (m + 1)`.
* `openOddCount_genusSix_eq_five'` -- the genus-six instance, `= 5`.
* `openOddCount_genusSix_eq_five_of_rowSingleColumn` -- the same with the
  `diagonal` field replaced by its single-column source: `RowSingleColumn` on every
  stable row of every open odd member, together with the `extract` and `rigid`
  statements restricted to diagonal members, gives the genus-six count.

## What is NOT proved here

* **`DiagonalClassification` is not inhabited here**; every statement below carries
  it.  At genus six it is inhabited in `CaterpillarAllMembers`
  (`diagonalClassification_genusSix`).
* `openOddCount_genusSix_eq_five_of_rowSingleColumn` carries the `extract`
  and `rigid` statements as hypotheses; only the `diagonal` field is replaced.
* Nothing here bears on the walls or the type changes of the count (steps 2 and 3
  of `Assembly`).
-/

namespace DraismaVargas.Count.BallotCoreIdentification

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar

/-- **A ballot classification from the exhaustion package alone.**  The ballot family
members, with `BallotSlopes.DiagonalClassification`. -/
noncomputable def ballotClassification' (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification m request) :
    CaterpillarBallot.BallotClassification m request :=
  BallotSlopes.ballotClassificationOfDiagonal' (ballotFamilyMember m request)
    (ballotFamilyMember_open m hRequest) (ballotFamilyMember_hasOddMult m request)
    (fun s ↦ BallotSlopes.diagonal_of_matrix_eq s (ballotFamilyMember_matrix m request s))
    (fun s ↦ BallotSlopes.coreDiag_eq_of_matrix_eq s
      (ballotFamilyMember_matrix m request s) (ballotFamilyMember_slotMap m request s))
    (fun slot ↦ (hRequest slot).ne') classification

/-- **The open odd count over the caterpillar is the Catalan number**, given the
exhaustion package. -/
theorem openOddCount_eq_catalan' (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification m request) :
    GeometricFibre.openOddCount (catCore m) request (m + 2) = catalan (m + 1) :=
  CaterpillarBallot.openOddCount_eq_catalan (ballotClassification' m hRequest classification)

/-- **Genus six**: the base count is five, assuming only the exhaustion package. -/
theorem openOddCount_genusSix_eq_five' {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification 2 request) :
    GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5 :=
  CaterpillarBallot.openOddCount_genusSix_eq_five
    (ballotClassification' 2 hRequest classification)

/-- **Genus six, with the `diagonal` field replaced by single-column rows**:
`RowSingleColumn` on every stable row of every open odd member. -/
theorem openOddCount_genusSix_eq_five_of_rowSingleColumn {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (hS4 : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      ∃ σ : Fin (6 * 2 + 3) → Fin (6 * 2 + 3), ∀ sourceRow,
        SpineOffDiagonal.RowSingleColumn mem.fullDim.labelling sourceRow (σ sourceRow))
    (hextract : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s)
    (hrigid : ∀ first second : FibreMember (catCore 2) request (2 + 2),
      first.Open → first.HasOddMult → first.Diagonal →
        second.Open → second.HasOddMult → second.Diagonal →
          first.coreDiag = second.coreDiag →
            GeometricFibre.cls first = GeometricFibre.cls second) :
    GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5 :=
  openOddCount_genusSix_eq_five' hRequest
    { diagonal := BallotSlopes.diagonalRepresentatives_of_rowSingleColumn hS4
      extract := hextract
      rigid := hrigid }

end DraismaVargas.Count.BallotCoreIdentification
