module

public import DraismaVargasCount.W3ShiftSixMemberBalance

@[expose] public section

/-!
# Honest matrices for all six Equation (3) members

Equation (3) of Draisma--Vargas Part I (arXiv:1909.12924) is the balance in case
`{w3-r1-nd3-t2-(a>k4)}`: three shrink/grow pairs, one for each source direction (Figure 29 of
that paper shows one of them).
Every pair is constructed on its own sheet-relabelled base. The matrix identity
retained in `PairPackage` identifies its old columns with the original wall
datum, in the very same row dictionary as its stable-incidence equivalence.

A labelling of any one selected member supplies the common row and column
orders. All six honest length matrices then agree away from the regrown wall
column. This module constructs matrices; `W3ShiftSixMemberMultiplicity` uses
them to transport full-dimensional presentations and prove the final signed sum.
-/

namespace DraismaVargas.Count.W3ShiftSixMemberMatrices

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open W4Assembly W4StableSource ThirdEquation
open W3ShiftSourceCandidates W3ShiftLimitRows W3ShiftSixMemberBalance

private theorem cancelTarget {α β γ δ : Type*}
    (e : α ≃ β) (a : β ≃ γ) (b : β ≃ δ) :
    ((e.trans a).trans a.symm).trans b = e.trans b := by
  ext x
  simp

private theorem cancelRow {α β γ δ ε : Type*}
    (c : α ≃ β) (a : β ≃ γ) (b : β ≃ δ) (e : α ≃ ε) :
    b.symm.trans (a.trans ((c.trans a).symm.trans e)) =
      (c.trans b).symm.trans e := by
  ext x
  simp

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}
  {shifts : Fin 3 → ShiftProfile input}
  (pairs : ∀ direction, PairPackage (shifts direction))

/-- Three directions, with shrink/grow in each direction. -/
abbrev MemberIndex := Fin 3 × Fin 2

/-- The actual member over its own gauge base, not a surrogate matrix. -/
noncomputable def member (i : MemberIndex) :
    BalancedGlobal.Candidate target degree (pairs i.1).base wall :=
  shiftMembers (pairs i.1).shrink i.2

/-- Common wall rows transported through the actual gauge and member maps. -/
noncomputable def rowEquiv (i : MemberIndex) :
    StablePath data ≃ StablePath (member pairs i).datum :=
  (pairs i.1).incidence.row.trans
    (W3ShiftGraphData.rowEquiv (pairs i.1).shrink (pairs i.1).gaugeInput.valid i.2)

/-- The same dictionary retains branch incidence, for later FD transport. -/
noncomputable def memberIncidence (i : MemberIndex) :
    StableGraphIncidence.Equivalence data (member pairs i).datum :=
  (pairs i.1).incidence.trans
    (W3ShiftGraphData.memberEquivalence
      (pairs i.1).shrink (pairs i.1).gaugeInput.valid i.2)

theorem memberIncidence_row (i : MemberIndex) :
    (memberIncidence pairs i).row = rowEquiv pairs i := by
  change (pairs i.1).incidence.row.trans
    (W3ShiftGraphData.memberEquivalence _ _ i.2).row = _
  rw [W3ShiftGraphData.memberEquivalence_row]
  rfl

/-- All six matrices in the original wall's natural row/occurrence coordinates. -/
noncomputable def commonMatrix (i : MemberIndex) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ W3ShiftGraphData.commonMatrix
    (pairs i.1).shrink (pairs i.1).gaugeInput.valid i.2
    ((pairs i.1).incidence.row path) place

/-- Gauge preservation and retained-occurrence preservation compose exactly. -/
theorem commonMatrix_retained (i : MemberIndex) (path : StablePath data)
    (place : target.edges) :
    commonMatrix pairs i path (some place) = StableSourceMatrix.matrix data path place := by
  unfold commonMatrix
  rw [W3ShiftGraphData.commonMatrix_retained, (pairs i.1).matrix_map]

section Coordinates

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (selected : MemberIndex)
  (initial : StableLengthMatrixLabelling (member pairs selected).datum coordinate)

/-- The selected member's row labels pulled back to the common wall. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (rowEquiv pairs selected).trans initial.row

/-- The selected member's column order, with `none` naming the new occurrence. -/
noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans
    (TargetExpansion.occurrenceEquiv target wall (member pairs selected).right).symm

/-- Honest labellings of all six actual members in one coordinate system. -/
noncomputable def labelling (i : MemberIndex) :
    StableLengthMatrixLabelling (member pairs i).datum coordinate where
  row := (rowEquiv pairs i).symm.trans (sourceCoordinates pairs selected initial)
  targetEdge := (targetCoordinates pairs selected initial).trans
    (TargetExpansion.occurrenceEquiv target wall (member pairs i).right)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The selected member keeps its given labelling exactly. -/
theorem labelling_selected : labelling pairs selected initial selected = initial := by
  cases initial with
  | mk targetEdge row =>
    unfold labelling
    congr 1 <;> ext x <;>
      simp [sourceCoordinates, targetCoordinates]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Restricting to a direction gives exactly the existing honest pair labelling.
Thus pair results can be reused without an independent coordinate convention. -/
theorem pair_labelling_eq (direction : Fin 3) (position : Fin 2) :
    W3ShiftHonestBalance.labelling (pairs direction).shrink
      (pairs direction).gaugeInput.valid
      (labelling pairs selected initial (direction, 0)) position =
        labelling pairs selected initial (direction, position) := by
  unfold W3ShiftHonestBalance.labelling labelling
  congr 1
  · exact cancelTarget (targetCoordinates pairs selected initial)
      (TargetExpansion.occurrenceEquiv target wall (member pairs (direction, 0)).right)
      (TargetExpansion.occurrenceEquiv target wall (member pairs (direction, position)).right)
  · exact cancelRow (pairs direction).incidence.row
      (W3ShiftGraphData.rowEquiv (pairs direction).shrink (pairs direction).gaugeInput.valid 0)
      (W3ShiftGraphData.rowEquiv (pairs direction).shrink (pairs direction).gaugeInput.valid position)
      (sourceCoordinates pairs selected initial)

/-- These are the literal length matrices of the six labelled gluing data. -/
noncomputable def squareMatrix (i : MemberIndex) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (labelling pairs selected initial i).presentation

omit [Fintype coordinate] in
/-- The selected member's original matrix is unchanged, not just its determinant. -/
theorem squareMatrix_selected :
    squareMatrix pairs selected initial selected = initial.presentation.matrix := by
  rw [squareMatrix, labelling_selected]

omit [Fintype coordinate] in
/-- Each previously proved pair matrix is literally its six-member matrix. -/
theorem pair_squareMatrix_eq (direction : Fin 3) (position : Fin 2) :
    W3ShiftHonestBalance.squareMatrix (pairs direction).shrink
      (pairs direction).gaugeInput.valid
      (labelling pairs selected initial (direction, 0)) position =
        squareMatrix pairs selected initial (direction, position) := by
  change (W3ShiftHonestBalance.labelling (pairs direction).shrink
    (pairs direction).gaugeInput.valid
    (labelling pairs selected initial (direction, 0)) position).presentation.matrix = _
  rw [pair_labelling_eq]
  rfl

/-- The one column that may differ among the six matrices. -/
noncomputable def wallColumn : coordinate :=
  (targetCoordinates pairs selected initial).symm none

theorem squareMatrix_common (i : MemberIndex) (row column : coordinate) :
    squareMatrix pairs selected initial i row column =
      commonMatrix pairs i ((sourceCoordinates pairs selected initial).symm row)
        (targetCoordinates pairs selected initial column) := by
  rw [squareMatrix, StableSourceMatrix.labelling_matrix_eq]
  rfl

/-- Every old column equals the same original-wall column, including across gauges. -/
theorem squareMatrix_retained (i : MemberIndex) (row : coordinate) (place : target.edges) :
    squareMatrix pairs selected initial i row
        ((targetCoordinates pairs selected initial).symm (some place)) =
      StableSourceMatrix.matrix data
        ((sourceCoordinates pairs selected initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

/-- The remaining column is the actual pair's regrown-occurrence column. -/
theorem squareMatrix_wall (i : MemberIndex) (row : coordinate) :
    squareMatrix pairs selected initial i row (wallColumn pairs selected initial) =
      commonMatrix pairs i ((sourceCoordinates pairs selected initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- All six actual matrices agree off their common wall column. -/
theorem matrices_agree (first second : MemberIndex) :
    AgreeOffColumn (squareMatrix pairs selected initial first)
      (squareMatrix pairs selected initial second) (wallColumn pairs selected initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates pairs selected initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

end Coordinates

end DraismaVargas.Count.W3ShiftSixMemberMatrices
