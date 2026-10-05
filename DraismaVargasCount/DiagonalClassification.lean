module

public import DraismaVargasCount.MemberColumnTwist

@[expose] public section

/-!
# The exhaustion package over diagonal representatives: `DiagonalClassification`

`DiagonalClassification m request` says that the open odd part of the fibre over the
caterpillar of loops is exhausted by ballot members, stated on diagonal representatives.
Its three fields are:

* `diagonal` -- every open odd **class** has a diagonal representative.  Diagonality of
  every member cannot be asked for: a member carries its column labelling as data, and
  permuting it produces another open member of odd multiplicity, in the same geometric
  class, whose matrix is the old one with its columns permuted (`MemberColumnTwist`,
  `ColumnTwist.not_forall_diagonal_of_openOdd`).  The field is what the spine argument
  delivers, see `diagonalRepresentatives_of_rowSingleColumn`;
* `extract` -- a diagonal member's core diagonal is the ballot diagonal of a slope
  sequence (`prop-caterpillar-ballot`(1) in Vargas, Part II, arXiv:2609.09109);
* `rigid` -- among diagonal members, the core diagonal determines the class
  (`prop-caterpillar-ballot`(2)).

`extract` and `rigid` quantify over **diagonal** members only, which is the only place
`FibreMember.coreDiag` is a meaningful invariant (`slotMap_column` in `CoreSlotCoords`
needs both members diagonal).  For `extract` the restriction is **necessary**, not
cosmetic: the unrestricted statement fails at the caterpillar
(`ColumnTwist.not_forall_extract`).

At genus six the package holds at every request
(`CaterpillarAllMembers.diagonalClassification_genusSix`); this is part of the base count,
step 1 of `Assembly`.

## What is proved

* `DiagonalClassification` -- the three-field package.
* `DiagonalClassification.diagonal_twistColumns` -- the `diagonal` field is
  stable under the column twist.
* `diagonalRepresentatives_of_rowSingleColumn` -- if every stable row of every
  open odd member lies above a single target edge (`SpineOffDiagonal.RowSingleColumn`),
  the `diagonal` field holds.
* `ballotClassificationOfDiagonal'` -- a family of diagonal ballot members, together
  with the package, is a `CaterpillarBallot.BallotClassification`.

## What is NOT proved here (every hypothesis, explicitly)

* **`DiagonalClassification m request` is not inhabited in this file**, for any `m`;
  the genus-six inhabitant is in `CaterpillarAllMembers`.
* `diagonalRepresentatives_of_rowSingleColumn` takes `RowSingleColumn` for
  **every** open odd member, existentially in the column map, and nothing here
  proves it for a single row (that is `SpineSingleColumn`).
* `hrequest : ∀ slot, request slot ≠ 0` is a genuine hypothesis of
  `ballotClassificationOfDiagonal'`, inherited from `ballotFamilyOfDiagonal`.
* Nothing here is about parity.
-/

namespace DraismaVargas.Count.BallotSlopes

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.CaterpillarBallot (BallotFamily BallotClassification)

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  The package -/

/-- **The exhaustion obligation, over diagonal representatives.**

`diagonal` asks for a diagonal member in each open odd class rather than
diagonality of every member -- the latter fails whenever an open odd member exists
(`ColumnTwist.not_forall_diagonal_of_openOdd`) -- and `extract` and `rigid`
are restricted to diagonal members, which is where `FibreMember.coreDiag` is a
class invariant.

At genus six it holds at every request
(`CaterpillarAllMembers.diagonalClassification_genusSix`). -/
structure DiagonalClassification (m : ℕ) (request : Fin (6 * m + 3) → ℚ) : Prop where
  /-- Every open odd class has a diagonal representative. -/
  diagonal : ∀ mem : FibreMember (catCore m) request (m + 2),
    mem.Open → mem.HasOddMult →
      ∃ rep : FibreMember (catCore m) request (m + 2),
        rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
          GeometricFibre.cls rep = GeometricFibre.cls mem
  /-- A diagonal member's core diagonal is a ballot diagonal (Part II,
  `prop-caterpillar-ballot`(1)). -/
  extract : ∀ mem : FibreMember (catCore m) request (m + 2),
    mem.Open → mem.HasOddMult → mem.Diagonal →
      ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = ballotCoreDiag m s
  /-- The core diagonal determines the class, among diagonal members (Part II,
  `prop-caterpillar-ballot`(2)). -/
  rigid : ∀ first second : FibreMember (catCore m) request (m + 2),
    first.Open → first.HasOddMult → first.Diagonal →
      second.Open → second.HasOddMult → second.Diagonal →
        first.coreDiag = second.coreDiag →
          GeometricFibre.cls first = GeometricFibre.cls second

/-! ## 2.  Stability under the column twist -/

/-- **The `diagonal` field is stable under the column twist**: it is a statement
about geometric classes, and `ColumnTwist.twistColumns_cls` says the twist does not
move the class. -/
theorem DiagonalClassification.diagonal_twistColumns
    (classification : DiagonalClassification m request) (σ : Equiv.Perm (Fin (6 * m + 3)))
    (mem : FibreMember (catCore m) request (m + 2)) (hOpen : mem.Open) (hOdd : mem.HasOddMult) :
    ∃ rep : FibreMember (catCore m) request (m + 2),
      rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
        GeometricFibre.cls rep = GeometricFibre.cls (ColumnTwist.twistColumns σ mem) := by
  obtain ⟨rep, hrO, hrM, hrD, hrcls⟩ := classification.diagonal mem hOpen hOdd
  exact ⟨rep, hrO, hrM, hrD, by rw [ColumnTwist.twistColumns_cls, hrcls]⟩

/-! ## 3.  Single-column rows give the `diagonal` field -/

/-- **Single-column rows supply the `diagonal` field.**  `RowSingleColumn` on every
stable row of every open odd member (`SpineOffDiagonal`) makes the length matrix
monomial, and the column twist of `MemberColumnTwist` turns a monomial member into a
genuinely diagonal member of the same class. -/
theorem diagonalRepresentatives_of_rowSingleColumn
    (hS4 : ∀ mem : FibreMember (catCore m) request (m + 2), mem.Open → mem.HasOddMult →
      ∃ σ : Fin (6 * m + 3) → Fin (6 * m + 3), ∀ sourceRow,
        SpineOffDiagonal.RowSingleColumn mem.fullDim.labelling sourceRow (σ sourceRow))
    (mem : FibreMember (catCore m) request (m + 2)) (hOpen : mem.Open) (hOdd : mem.HasOddMult) :
    ∃ rep : FibreMember (catCore m) request (m + 2),
      rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
        GeometricFibre.cls rep = GeometricFibre.cls mem := by
  obtain ⟨σ, hσ⟩ := hS4 mem hOpen hOdd
  exact ColumnTwist.exists_diagonal_cls_eq_of_rowSingleColumn mem hOpen hOdd hσ

/-! ## 4.  Packaging as a `BallotClassification` -/

/-- **`member_surjective`, derived from the package.**  A family of open odd
diagonal members realising every ballot diagonal, together with
`DiagonalClassification`, is a `BallotClassification`. -/
noncomputable def ballotClassificationOfDiagonal'
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hdiag : ∀ s, (member s).Diagonal)
    (hvalue : ∀ s, (member s).coreDiag = ballotCoreDiag m s)
    (hrequest : ∀ slot, request slot ≠ 0)
    (classification : DiagonalClassification m request) :
    BallotClassification m request where
  toBallotFamily := ballotFamilyOfDiagonal member hOpen hOdd hdiag hvalue hrequest
  member_surjective := by
    intro mem hmemOpen hmemOdd
    obtain ⟨rep, hrO, hrM, hrD, hrcls⟩ := classification.diagonal mem hmemOpen hmemOdd
    obtain ⟨s, hs⟩ := classification.extract rep hrO hrM hrD
    exact ⟨s, (classification.rigid (member s) rep (hOpen s) (hOdd s) (hdiag s) hrO hrM hrD
      (by rw [hvalue s, hs])).trans hrcls⟩

end DraismaVargas.Count.BallotSlopes
