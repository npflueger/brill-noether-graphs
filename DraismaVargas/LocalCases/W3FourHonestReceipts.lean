module

public import DraismaVargas.LocalCases.W3FourArbitraryExit

@[expose] public section

/-!
# Figure 28's honest family at an arbitrary stable labelling

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a=k4)}, Figure 28 and
Equation (2).  Part I works with isomorphism classes of gluing datums
(`definition-gd-iso`).  For a fixed gluing datum value, as here, Figure 28's
members `M⁽¹⁾` (Position I) and `M⁽²⁾` (Position II.b) cannot both be regrown --
the first needs `e₂` and `e₃` to tile `A₀`, the second needs them to meet -- so
they live over branch-swapped copies of the wall datum, which have the same
length matrices.

## What this file settles

The original-coordinate exit of this case is naturally stated with two
coordinate hypotheses,

* `hOrder : fullDim.labelling.targetEdge.symm contracted = none`, and
* `hHonest : memberMatrix certified incoming =
   GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation`,

because `W3FourHonestBalance.HonestFigure28`'s four presented matrices live at
**one fixed** coordinate order -- columns `Option target.edges`, wall column
`none`, rows the limit's own stable rows through
`W3FourLimitRows.limitRowsOfInput`.  Here Equation (2)'s family is restated at
an **arbitrary** `W4StableSource.StableLengthMatrixLabelling` of one member,
which is the analogue for Figure 28 of `W3ShiftHonestBalance.limitRows`:

* `labelling start initial start = initial` (`labelling_start`) -- the chosen
  member is presented at the chosen labelling, on the nose;
* `honestLabelling_matrix` is `rfl` -- the family's presented matrix of every
  member **is** that member's own honest stable-length matrix at the induced
  labelling, not merely equal to it;
* `gaugeFamily.wallColumn` is whatever coordinate the supplied labelling puts
  the regrown occurrence in, so **`hOrder` disappears at the source**: no
  hypothesis is placed on the incoming cover's column order.

## The route, and why it is four lemmas rather than seven hundred

Figure 29 has to redo its determinant computation at the new coordinates
(`W3ShiftHonestBalance`, some 720 lines) because `W3ShiftLimitRows.limitRows`
is a *total function* of the case data and its `det` field is proved there.
Figure 28 does not: `W3FourStableGraph.Figure28Receipts.det_eq_figure28` and
`Figure28Receipts.gaugeFamily` already prove the four displayed determinants
and Equation (2)'s `PositiveBalance` at the fixed order, and
`W3FourRegrownColumn.ColumnData.presented_matrix_eq` -- the
`W4OutgoingLimitMatrix.presented_matrix_eq` analogue, which Figure 29 does not
have -- already identifies each presented matrix with the member's own.  What
is added here is therefore only the **change of coordinates**, and a change of
coordinates does exactly one thing to a determinant:

`det (M.submatrix e f) = sign (f.trans e.symm) • det M`

for equivalences `e` (rows) and `f` (columns), the *same* pair for all four
members.  `reorderSign` is that `±1`, `det_squareMatrix` the identity, and
`BalancingValencyTwo.PositiveBalance` is a weighted sum set to zero, so it is
invariant under multiplying every determinant by one nonzero constant.  Nothing
about Figure 28's geometry is re-derived and nothing new is assumed.

## What is proved

`rowCoordinates`, `targetCoordinates`, `labelling`, `labelling_start`,
`squareMatrix`, `squareMatrix_eq`, `wallColumn`, `matrices_agree`,
`reorderSign`, `det_squareMatrix`, `reorderSign_ne_zero`; **`gaugeFamily`**, a
`W3FourClosure.GaugeFamily 4 data wall` at the arbitrary coordinate with
`honestLabelling_matrix` by `rfl`, `gaugeFamily_presentation_start` and
`det_ne_zero_iff`; `outgoingVelocity` and its system; `wallColumn_eq`.  Then
`FamilyMatching`, `exists_transported` and `familyMatching_of_position`:
`FamilyMatching` names the one remaining matching hypothesis, and
`familyMatching_of_position` reduces it to a single index.

## What replaces `hHonest`

At the arbitrary labelling the exit takes the incoming cover's identification
with a member of Equation (2)'s family in the shape the incoming matching
(`W3FourIncomingMatching`) produces it: a `FullDimensionalSourcePresentation`
of that member's datum whose matrix is the incoming cover's (`hIncomingMatrix`)
and whose regrown column is the original contracted one (`hIncomingWall`).
That is strictly weaker than `hHonest`, which additionally fixes the coordinate
order, and it is coordinate free; but it is not *nothing*, and the reason is
the branch swap described above, not a gap in this file.  The incoming
matching identifies the incoming cover with a member of the **incoming** family
`W3FourIncomingCensus.WallMember`, three members over
`contractDatum data hc hab hOne` itself; Equation (2)'s family is four members,
two of which (`M⁽¹⁾` and `M⁽²⁾`) live over *branch-swapped copies*
(`W3FourRegrownColumnSeam.exists_memberCertificates`, through
`W3FourClosure.exists_member_one`/`exists_member_two`).  For the two Position
II.a members the two families' candidates are the same object; for the `t₄`
member they are not, and matching them is the branch-swap transport.  See the
note at §3.

## What is not claimed

No incoming-member identification is redone here (that is
`W3FourIncomingMatching`), no selected-block census is discharged (`hCensus` is
carried verbatim), no requested `Spec`, no terminal refinement and no
metric-length dictionary: the cleared pencil is on the outgoing member's
literal source subdivision, exactly as in nd2, nd3, M11 and Figure 29.  No
FourStar theorem is applied to this ThreeStar case.
-/

namespace DraismaVargas.LocalCases.W3FourHonestReceipts

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open StableSourceMatrix
open FullDimensionalSource WallDegeneration
open W3R1SourceProfile
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3FourClosure (FourStarGeometry)
open W3FourHonestBalance (HonestFigure28)
open W3FourIncomingCensus (WallMember)
open W3FourRegrownColumnSeam (MemberCertificates)
open W3FourArbitraryExit (memberMatrix)
open W3ShiftIncomingMatching (SelectedCensus)

/-! ## §1  Equation (2)'s family at an arbitrary labelling of one member -/

section Family

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {geometry : FourStarGeometry data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (certified : MemberCertificates data wall geometry) (start : Fin 4)
  (initial : StableLengthMatrixLabelling
    (certified.receipts.candidate start).datum coordinate)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The row order the chosen labelling installs, read against the fixed
coordinate order of `W3FourHonestBalance.HonestFigure28.labelling`. -/
noncomputable def rowCoordinates : coordinate ≃ Option target.edges :=
  initial.row.symm.trans (certified.receipts.labelling start).row

/-- and the column order, read against the chosen member's own occurrence
dictionary. -/
noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans
    (occurrenceEquiv target wall (certified.receipts.candidate start).right).symm

/-- **The induced honest labelling of each of Figure 28's four members.**  A
single member's labelling supplies only the finite coordinate order; the other
three are labelled through their own honest labellings at the fixed order. -/
noncomputable def labelling (i : Fin 4) :
    StableLengthMatrixLabelling (certified.receipts.candidate i).datum coordinate where
  row := (certified.receipts.labelling i).row.trans
    (rowCoordinates certified start initial).symm
  targetEdge := (targetCoordinates certified start initial).trans
    (occurrenceEquiv target wall (certified.receipts.candidate i).right)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **At the chosen member it is the chosen labelling itself.**  This is what
removes `hHonest`'s coordinate half and `hOrder` entirely: the family is
presented in the incoming cover's own order because the incoming cover's own
order is what was fed in. -/
theorem labelling_start : labelling certified start initial start = initial := by
  cases initial with
  | mk te r =>
    refine congrArg₂ StableLengthMatrixLabelling.mk ?_ ?_ <;> ext x <;>
      simp [rowCoordinates, targetCoordinates]

/-- The honest square length matrix of one member, at the chosen order. -/
noncomputable def squareMatrix (i : Fin 4) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (labelling certified start initial i).presentation

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem memberMatrix_eq (i : Fin 4) :
    memberMatrix certified i =
      GluingDatum.LengthMatrixPresentation.matrix
        (certified.receipts.gaugeFamily.presentation i) := rfl

/-- **It is Equation (2)'s own matrix, with its rows and columns relabelled.**
Both relabellings are independent of the member. -/
theorem squareMatrix_eq (i : Fin 4) :
    squareMatrix certified start initial i =
      (memberMatrix certified i).submatrix (rowCoordinates certified start initial)
        (targetCoordinates certified start initial) := by
  ext row column
  show GluingDatum.LengthMatrixPresentation.matrix
      (labelling certified start initial i).presentation row column =
    GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation i)
      (rowCoordinates certified start initial row)
      (targetCoordinates certified start initial column)
  rw [labelling_matrix_eq, ← certified.receipts.labelling_matrix i, labelling_matrix_eq]
  rfl

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  (targetCoordinates certified start initial).symm none

/-- The four members agree away from the regrown wall column: this is
`W3FourStableGraph.MemberColumn.presentation_agreeOffWall` relabelled. -/
theorem matrices_agree (i j : Fin 4) :
    AgreeOffColumn (squareMatrix certified start initial i)
      (squareMatrix certified start initial j) (wallColumn certified start initial) := by
  intro row column hColumn
  rw [squareMatrix_eq, squareMatrix_eq, Matrix.submatrix_apply, Matrix.submatrix_apply]
  refine certified.receipts.gaugeFamily.agreeOffWall i j _ _ ?_
  intro hEq
  exact hColumn ((Equiv.eq_symm_apply _).mpr hEq)

/-- The sign of the coordinate change: `±1`, the same for all four members. -/
noncomputable def reorderSign : ℚ :=
  ((Equiv.Perm.sign ((targetCoordinates certified start initial).trans
    (rowCoordinates certified start initial).symm) : ℤ) : ℚ)

/-- **The one thing a change of coordinates does to a determinant.** -/
theorem det_squareMatrix (i : Fin 4) :
    (squareMatrix certified start initial i).det =
      reorderSign certified start initial * (memberMatrix certified i).det := by
  rw [squareMatrix_eq]
  have h1 : (memberMatrix certified i).submatrix (rowCoordinates certified start initial)
        (targetCoordinates certified start initial) =
      ((memberMatrix certified i).submatrix (rowCoordinates certified start initial)
        (rowCoordinates certified start initial)).submatrix id
        ((targetCoordinates certified start initial).trans
          (rowCoordinates certified start initial).symm) := by
    ext r c
    simp [Matrix.submatrix]
  rw [h1, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  rfl

theorem reorderSign_ne_zero : reorderSign certified start initial ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    ((targetCoordinates certified start initial).trans
      (rowCoordinates certified start initial).symm)) with h | h <;> simp [reorderSign, h]

/-- **Equation (2) at the arbitrary labelling.**  The four members, the four
gauge copies and Figure 28's weights `![1, k₂+k₃-1, k₂+1, k₃+1]` are
`W3FourHonestBalance.HonestFigure28.gaugeFamily`'s, unchanged; the four
presentations are the members' own honest labellings at the chosen order, and
`positiveBalance` is the fixed order's scaled by `reorderSign`. -/
noncomputable def gaugeFamily :
    W3FourClosure.GaugeFamily (coordinate := coordinate) 4 data wall where
  base := certified.receipts.base
  valid_of_old := certified.receipts.gaugeFamily.valid_of_old
  candidate := certified.receipts.candidate
  presentation := fun i ↦ (labelling certified start initial i).presentation
  wallColumn := wallColumn certified start initial
  weight := certified.receipts.gaugeFamily.weight
  positiveBalance := by
    refine ⟨certified.receipts.gaugeFamily.positiveBalance.1, ?_⟩
    have h : ∀ i : Fin 4, certified.receipts.gaugeFamily.weight i *
        (GluingDatum.LengthMatrixPresentation.matrix
          (labelling certified start initial i).presentation).det =
        reorderSign certified start initial *
          (certified.receipts.gaugeFamily.weight i *
            (GluingDatum.LengthMatrixPresentation.matrix
              (certified.receipts.gaugeFamily.presentation i)).det) := by
      intro i
      show certified.receipts.gaugeFamily.weight i *
        (squareMatrix certified start initial i).det = _
      rw [det_squareMatrix, memberMatrix_eq]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ h i), ← Finset.mul_sum,
      certified.receipts.gaugeFamily.positiveBalance.2, mul_zero]
  agreeOffWall := matrices_agree certified start initial

@[simp] theorem gaugeFamily_wallColumn :
    (gaugeFamily certified start initial).wallColumn =
      wallColumn certified start initial := rfl

@[simp] theorem gaugeFamily_candidate (i : Fin 4) :
    (gaugeFamily certified start initial).candidate i =
      certified.receipts.candidate i := rfl

@[simp] theorem gaugeFamily_base (i : Fin 4) :
    (gaugeFamily certified start initial).base i =
      certified.receipts.base i := rfl

@[simp] theorem gaugeFamily_weight :
    (gaugeFamily certified start initial).weight =
      certified.receipts.gaugeFamily.weight := rfl

/-- **The honesty identity, by `rfl`.**  The family's presented matrix of
member `i` *is* the length matrix of `i`'s own induced stable labelling, so a
determinant gate on the family is a gate on the member's own matrix and
conversely, with nothing to transport. -/
theorem honestLabelling_matrix (i : Fin 4) :
    GluingDatum.LengthMatrixPresentation.matrix
        (labelling certified start initial i).presentation =
      GluingDatum.LengthMatrixPresentation.matrix
        ((gaugeFamily certified start initial).presentation i) := rfl

@[simp] theorem gaugeFamily_presentation_start :
    (gaugeFamily certified start initial).presentation start = initial.presentation := by
  show (labelling certified start initial start).presentation = _
  rw [labelling_start]

/-- Equation (2)'s determinant gate at the new coordinates is the old one. -/
theorem det_ne_zero_iff (i : Fin 4) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((gaugeFamily certified start initial).presentation i)).det ≠ 0 ↔
      (memberMatrix certified i).det ≠ 0 := by
  show (squareMatrix certified start initial i).det ≠ 0 ↔ _
  rw [det_squareMatrix]
  exact mul_ne_zero_iff.trans
    ⟨fun h ↦ h.2, fun h ↦ ⟨reorderSign_ne_zero certified start initial, h⟩⟩

/-- The canonical outgoing chart velocity at a nonsingular member. -/
noncomputable def outgoingVelocity (incoming : Fin 4)
    (incomingVelocity : coordinate → ℚ) (outgoing : Fin 4) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates (squareMatrix certified start initial outgoing)
    ((squareMatrix certified start initial incoming).mulVec incomingVelocity)

/-- It discharges the exit's `hSystems` hypothesis at any nonsingular member. -/
theorem outgoingVelocity_system (incoming : Fin 4)
    (incomingVelocity : coordinate → ℚ) (outgoing : Fin 4)
    (hDet : (squareMatrix certified start initial outgoing).det ≠ 0) :
    (squareMatrix certified start initial incoming).mulVec incomingVelocity =
      (squareMatrix certified start initial outgoing).mulVec
        (outgoingVelocity certified start initial incoming incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

end Family

/-! ## §2  The exit in the incoming cover's own coordinates -/

section Exit

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (members : Fin 3 → WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
    input.distinguishedBlock.1)
  {geometry : FourStarGeometry (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (certified : MemberCertificates (contractDatum data hc hab hOne) ⟨a, hab⟩ geometry)
  (incoming : Fin 4)
  (incomingFD : FullDimensionalSourcePresentation
    (certified.receipts.candidate incoming).datum coordinate)

include hForest

omit hForest in
/-- The family's wall column, spelled out: the coordinate the identified
member's own labelling puts its regrown occurrence in. -/
theorem wallColumn_eq :
    wallColumn certified incoming incomingFD.labelling =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (certified.receipts.candidate incoming).right none) := rfl

end Exit

/-! ## §3  The one remaining matching, named

The incoming matching (`W3FourIncomingMatching`) identifies the incoming cover
with a member of the **incoming** family `W3FourIncomingCensus.WallMember` --
three members over `contractDatum data hc hab hOne` itself, with no branch swap
(`W3FourIncomingCensus.exists_positionMember`).  Equation (2)'s family is four
members, and `M⁽¹⁾`, `M⁽²⁾` live over *branch-swapped copies*
(`W3FourRegrownColumnSeam.exists_memberCertificates`, through
`W3FourClosure.exists_member_one` / `exists_member_two`), because exactly one of
the two exists over any datum of the case while Equation (2) needs both.  For
the two Position II.a members the two families' candidates are literally the
same object -- `W3FourIncomingMatching.figure28Members … 1` is
`W3FourIncomingCensus.growMember (growProfileFirst …)`, whose candidate is
`(growProfileFirst …).growCandidate`, and that is
`W3FourSourceCandidates.thirdCandidate …` by `rfl`, which
`exists_memberCertificates` returns as `certified.receipts.candidate 2` over
`certified.receipts.base 2 = data`.  For the `t₄` member they are not, and
matching them is the branch-swap transport.

`FamilyMatching` is exactly that matching, at the level of what the exit
consumes, and nothing else is left. -/

section Residue

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (members : Fin 3 → WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
    input.distinguishedBlock.1)
  {geometry : FourStarGeometry (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (certified : MemberCertificates (contractDatum data hc hab hOne) ⟨a, hab⟩ geometry)

/-- **The identified incoming Figure 28 member is one of Equation (2)'s four**,
in the shape the exit uses it: an original-coordinate presentation of that
member's datum with the incoming cover's own matrix and the original contracted
column.  This is the single hypothesis beyond the arbitrary-labelling family;
see the section note for why it involves the branch swap and for the two
indices at which it is `rfl`. -/
def FamilyMatching : Prop :=
  ∀ (index : Fin 3)
    (fd : FullDimensionalSourcePresentation (members index).candidate.datum coordinate),
    GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation →
      fd.labelling.targetEdge.symm
          (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
            (members index).candidate.right none) =
        fullDim.labelling.targetEdge.symm contracted →
      ∃ incoming : Fin 4,
        ∃ incomingFD : FullDimensionalSourcePresentation
            (certified.receipts.candidate incoming).datum coordinate,
          GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
              GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
            incomingFD.labelling.targetEdge.symm
                (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                  (certified.receipts.candidate incoming).right none) =
              fullDim.labelling.targetEdge.symm contracted

/-- Transport the identification's two clauses along an equality of candidates.
`subst` does the whole work; the `HEq` is what
`W3FourRegrownColumnSeam.exists_memberCertificates` returns, beside the
equality of bases that makes it an equality. -/
theorem exists_transported {B : GluingDatum (contract target hab hOne) degree}
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree B ⟨a, hab⟩)
    (index : Fin 3) (hBase : B = contractDatum data hc hab hOne)
    (hCand : HEq C (members index).candidate)
    (fd : FullDimensionalSourcePresentation (members index).candidate.datum coordinate)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
    (hWall : fd.labelling.targetEdge.symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (members index).candidate.right none) =
      fullDim.labelling.targetEdge.symm contracted) :
    ∃ incomingFD : FullDimensionalSourcePresentation C.datum coordinate,
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
        incomingFD.labelling.targetEdge.symm
            (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ C.right none) =
          fullDim.labelling.targetEdge.symm contracted := by
  subst hBase
  cases eq_of_heq hCand
  exact ⟨fd, hMatrix, hWall⟩

/-- **`FamilyMatching` is a statement about the `t₄` member alone.**  At the two
Position II.a indices the incoming family's member and Equation (2)'s member are
the same object: `W3FourIncomingMatching.figure28Members … 1` is
`W3FourIncomingCensus.growMember (W3FourSourceCandidates.growProfileFirst …)`,
whose candidate is `W3FourSourceCandidates.thirdCandidate …` by `rfl`, and
`W3FourRegrownColumnSeam.exists_memberCertificates` returns
`certified.receipts.base 2 = data`, `HEq (certified.receipts.candidate 2)
(thirdCandidate …)` -- likewise for `3` and `fourthCandidate`.  So those two
hypotheses are discharged by that theorem's own output, and what is left is the
`t₄` index, where the incoming member lives over `contractDatum data hc hab hOne`
and Equation (2)'s `M⁽¹⁾`, `M⁽²⁾` live over branch-swapped copies. -/
theorem familyMatching_of_position
    (hBaseThree : certified.receipts.base 2 = contractDatum data hc hab hOne)
    (hCandThree : HEq (certified.receipts.candidate 2) (members 1).candidate)
    (hBaseFour : certified.receipts.base 3 = contractDatum data hc hab hOne)
    (hCandFour : HEq (certified.receipts.candidate 3) (members 2).candidate)
    (hPosition : ∀ fd : FullDimensionalSourcePresentation
        (members 0).candidate.datum coordinate,
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation →
        fd.labelling.targetEdge.symm
            (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (members 0).candidate.right none) =
          fullDim.labelling.targetEdge.symm contracted →
        ∃ incoming : Fin 4,
          ∃ incomingFD : FullDimensionalSourcePresentation
              (certified.receipts.candidate incoming).datum coordinate,
            GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
                GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
              incomingFD.labelling.targetEdge.symm
                  (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                    (certified.receipts.candidate incoming).right none) =
                fullDim.labelling.targetEdge.symm contracted) :
    FamilyMatching data hc hab hOne fullDim star input members certified := by
  intro index fd hMatrix hWall
  match index with
  | 0 => exact hPosition fd hMatrix hWall
  | 1 =>
    obtain ⟨incomingFD, h1, h2⟩ :=
      exists_transported data hc hab hOne fullDim star input members
        (certified.receipts.candidate 2) 1 hBaseThree hCandThree fd hMatrix hWall
    exact ⟨2, incomingFD, h1, h2⟩
  | 2 =>
    obtain ⟨incomingFD, h1, h2⟩ :=
      exists_transported data hc hab hOne fullDim star input members
        (certified.receipts.candidate 3) 2 hBaseFour hCandFour fd hMatrix hWall
    exact ⟨3, incomingFD, h1, h2⟩

end Residue


end DraismaVargas.LocalCases.W3FourHonestReceipts
