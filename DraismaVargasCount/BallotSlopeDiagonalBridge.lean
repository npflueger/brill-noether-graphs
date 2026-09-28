import DraismaVargasCount.BallotSlopeSeparation
import DraismaVargasCount.BallotDiagonal

/-!
# Distinct slope sequences give distinct classes, for members with the ballot matrix

**Source.**  Vargas, Part II (arXiv:2609.09109), `prop-caterpillar-ballot`(2): a
slope sequence uniquely determines its morphism.  This module proves the injective
half over the labelled fibre: distinct slope sequences give distinct classes.

This module is **glue, and deliberately nothing else**.  `BallotSlopes`
reduces `BallotFamily.member_injective` to
`(member s).coreDiag = ballotCoreDiag m s`; `BallotDiagonal` computes the
diagonal of `(ballotLabelling m s).presentation` and gets, independently,
**the same three values** -- `2` on a leaf row, `1 / s_i` on the spine row `h_i`,
`1/2` on a stem.  One `rfl`-level identification joins them, and the injectivity
obligation then costs nothing for any member built on the ballot length matrix.

## What is proved

* `matrix_ballotLabelling_diag` -- `BallotDiagonal.bMatrix_diag` read as a
  statement about `ballotCoreDiag`.  That the two right-hand sides agree is
  definitional: the two formulas are the same term.
* `diagonal_of_matrix_eq` -- a member of the labelled fibre whose length matrix
  *is* the ballot length matrix is `Diagonal`, from `ballotDiagonalPattern`.
* `coreDiag_eq_of_matrix_eq` -- such a member, if it also labels its stable rows
  by the core's own slots, has `coreDiag = ballotCoreDiag m s`.
* `ballotFamilyOfBallotMatrix` -- **the family interface.**  A `BallotFamily` from a
  family of members that are open, of odd multiplicity, carry the ballot length
  matrix, and label their rows by the core slots.  No injectivity obligation
  survives.
* `catalan_le_openOddCount_of_ballotMatrix`,
  `five_le_openOddCount_genusSix_of_ballotMatrix` -- the lower bound and its
  genus-six instance from that interface.

## What is NOT proved here (every hypothesis, explicitly)

* **No member is constructed here.**  `hmatrix` and `hslot` are hypotheses about a
  given family of members; the ballot members themselves, with their core
  identifications, are constructed in `BallotCoreIdentification`.  Nothing below is
  an existence statement.
* `hslot : ∀ r, (member s).slotMap r = r` is a *normalisation* hypothesis, not a
  triviality: it says the member's `ident.row` is its own `labelling.row`, which
  is how `FibreCaterpillar.catIdent` is built but is not forced by the
  definition of `FibreMember`.  A member that labelled its rows by some other
  bijection with the core slots would need the general
  `BallotSlopes.member_injective_of_coreDiag` instead, with its `coreDiag`
  hypothesis checked by hand.
* `member_open` and `member_hasOddMult` are hypotheses here; surjectivity (the
  exhaustion half of the classification) is untouched, so only the lower bound
  follows.
-/

namespace DraismaVargas.Count.BallotSlopes

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.BallotValency (ballotLabelling ballotDiagonalPattern)
open DraismaVargas.Count.CaterpillarBallot (BallotFamily)

/-- **The diagonal of the ballot length matrix is `ballotCoreDiag`.**  The two
formulas are the same term, so this is `BallotDiagonal.bMatrix_diag` with the name
of the right-hand side changed. -/
theorem matrix_ballotLabelling_diag (m : ℕ) (s : Slopes (2 * (m + 1)))
    (slot : Fin (6 * m + 3)) :
    GluingDatum.LengthMatrixPresentation.matrix
        (ballotLabelling m s).presentation slot slot = ballotCoreDiag m s slot :=
  BallotDiagonal.bMatrix_diag s slot

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- A member carrying the ballot length matrix is diagonal. -/
theorem diagonal_of_matrix_eq (s : Slopes (2 * (m + 1)))
    {member : FibreMember (catCore m) request (m + 2)}
    (hmatrix : member.matrix = GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation) : member.Diagonal :=
  FibreMember.Diagonal.of_matrix_eq hmatrix
    fun _ _ hne ↦ (ballotDiagonalPattern m s).matrix_apply_eq_zero hne

/-- A member carrying the ballot length matrix and labelling its rows by the
core's own slots has the ballot diagonal, read on core slots. -/
theorem coreDiag_eq_of_matrix_eq (s : Slopes (2 * (m + 1)))
    {member : FibreMember (catCore m) request (m + 2)}
    (hmatrix : member.matrix = GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation)
    (hslot : ∀ r, member.slotMap r = r) :
    member.coreDiag = ballotCoreDiag m s := by
  funext slot
  rw [FibreMember.coreDiag_of_slotMap_id hslot, hmatrix, matrix_ballotLabelling_diag]

/-- **The family interface.**  Members that are open, of odd multiplicity, carry the
ballot length matrix and label their rows by the core slots assemble into a
`BallotFamily` with **no injectivity obligation left to discharge**. -/
noncomputable def ballotFamilyOfBallotMatrix
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hmatrix : ∀ s, (member s).matrix = GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation)
    (hslot : ∀ s r, (member s).slotMap r = r)
    (hrequest : ∀ slot, request slot ≠ 0) :
    BallotFamily m request :=
  ballotFamilyOfDiagonal member hOpen hOdd
    (fun s ↦ diagonal_of_matrix_eq s (hmatrix s))
    (fun s ↦ coreDiag_eq_of_matrix_eq s (hmatrix s) (hslot s)) hrequest

/-- The lower bound `catalan (m + 1)` through that interface. -/
theorem catalan_le_openOddCount_of_ballotMatrix
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hmatrix : ∀ s, (member s).matrix = GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation)
    (hslot : ∀ s r, (member s).slotMap r = r)
    (hrequest : ∀ slot, request slot ≠ 0) :
    catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) :=
  CaterpillarBallot.catalan_le_openOddCount
    (ballotFamilyOfBallotMatrix member hOpen hOdd hmatrix hslot hrequest)

/-- **Genus six.**  Five open classes of odd multiplicity over the caterpillar of
loops of genus six, from five members carrying the ballot length matrices. -/
theorem five_le_openOddCount_genusSix_of_ballotMatrix
    {request : Fin (6 * 2 + 3) → ℚ}
    (member : Slopes (2 * (2 + 1)) → FibreMember (catCore 2) request (2 + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hmatrix : ∀ s, (member s).matrix = GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling 2 s).presentation)
    (hslot : ∀ s r, (member s).slotMap r = r)
    (hrequest : ∀ slot, request slot ≠ 0) :
    5 ≤ GeometricFibre.openOddCount (catCore 2) request (2 + 2) :=
  CaterpillarBallot.five_le_openOddCount_genusSix
    (ballotFamilyOfBallotMatrix member hOpen hOdd hmatrix hslot hrequest)

end DraismaVargas.Count.BallotSlopes
