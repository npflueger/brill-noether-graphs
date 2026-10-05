module

public import DraismaVargas.LocalCases.W3ShiftHonestBalance
public import DraismaVargas.LocalCases.StableGraphFullDimensional

@[expose] public section

/-!
# Figure 29's pair: the outgoing presentation, and the exit in the identified member's coordinates

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

## What this file proves

The exit for Figure 29's `(k-1, k+1)` pair, stated in the identified member's
own coordinates, with an outgoing full-dimensional presentation and without
any column-order, honesty or nonsingularity hypothesis:

* **No column-order hypothesis.**  The pair is presented at the *identified
  member's own* honest labelling (`initialLabelling`), so its wall column is
  `fd.labelling.targetEdge.symm (occurrenceEquiv … none)`, which the
  incoming-member identification identifies with the original contracted
  column.  Nothing is asked of the incoming cover's column order.
* **No honesty hypothesis.**  `outgoingLabelling_self` says that transporting to
  the identified member and back is the identity on its labelling, so the
  pair's derived matrix of that member is literally the incoming cover's own.
* **The outgoing `FullDimensionalSourcePresentation` clause is supplied**, by
  `StableGraphFullDimensional.presentationOfEquivalence` along
  `W3ShiftGraphData.between` -- a member-to-member dictionary over the same
  expanded wall.  The incoming datum is never the transport source: it lives
  over `target`, the members over `contract target hab hOne`'s expansion, and
  `targetEdgeCard` would be off by one.  The incoming cover's own stable graph
  reaches the outgoing member by composition,
  `hGraph.trans (W3ShiftGraphData.between …)`.
* **No nonsingularity gate.**  The condition `wallContribution shrink ≠ 0` is
  derived: the incoming cover's own
  `FullDimensionalSourcePresentation.det_ne_zero`, transported through
  `outgoingLabelling_self`, gives it (`wallContribution_ne_zero`).

## The transport inputs

`candidate_targetConnected`, `candidate_targetGenus`, `candidate_targetEdgeCard`
and `candidate_sourceGenus` are the four numerical receipts
`presentationOfEquivalence` asks for; all four are read off the expansion and
`W3ShiftSourceCandidates`' genus theorems, and none is assumed.  Only the
**selected** outgoing matrix is ever required nonsingular, and that is derived
from Equation (3) through `W3ShiftHonestBalance.det_mul_neg`.

## What is not claimed

No requested `Spec`, no terminal refinement and no metric-length dictionary: the
cleared pencil is on the outgoing member's literal source subdivision, exactly
as in nd2, nd3 and M11.  The selected-block census
`W3ShiftIncomingMatching.SelectedCensus` is not produced here
(`W3ShiftSelectedCensus` produces it), and the `ShrinkData` of the pair is a
parameter (the branch-swap gauge of `W3ShiftShrinkExistence` supplies it).  No
FourStar theorem is applied to this ThreeStar case.
-/

namespace DraismaVargas.LocalCases.W3ShiftStableIncidence

/-! ## Two coordinate cancellations, at abstract types -/

section Cancellation

variable {α β γ δ ε : Type*}

private theorem trans_cancel_target (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) :
    ((e.trans (A.symm.trans B)).trans B.symm).trans A = e := by
  ext x
  simp

private theorem symm_trans_cancel (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) (x : γ) :
    ((e.trans (A.symm.trans B)).trans B.symm).symm x = e.symm (A x) := by
  simp

private theorem trans_cancel_row (R : α ≃ β) (S : α ≃ γ) (T : β ≃ γ)
    (hT : T = R.symm.trans S) (r : γ ≃ ε) :
    S.symm.trans (R.trans (T.trans r)) = r := by
  subst hT
  ext x
  simp

end Cancellation

section Fields

open DraismaVargas.Infrastructure W4StableSource

variable {target : CFGraph} {degree : ℕ} {datum : GluingDatum target degree}
  {coordinate : Type*}

private theorem labelling_eq_of_fields
    {first second : StableLengthMatrixLabelling datum coordinate}
    (hTarget : first.targetEdge = second.targetEdge) (hRow : first.row = second.row) :
    first = second := by
  cases first
  cases second
  cases hTarget
  cases hRow
  rfl

end Fields

/-! ## Transporting a full-dimensional presentation between the pair's members -/

section Member

open DraismaVargas.Infrastructure TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource ThirdEquation FullDimensionalSource
open W3R1SourceProfile W3ShiftSourceCandidates
open W3ShiftLimitRows (shiftMembers)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}
  (shrink : ShrinkData shift) (hValid : data.Valid)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem candidate_targetConnected (hConnected : graph_connected target) (i : Fin 2) :
    graph_connected
      (TargetExpansion.graph target wall (shiftMembers shrink i).right) :=
  TargetExpansion.graph_connected target wall _ hConnected

theorem candidate_targetGenus (hGenus : genus target = 0) (i : Fin 2) :
    genus (TargetExpansion.graph target wall (shiftMembers shrink i).right) = 0 := by
  simpa using hGenus

theorem candidate_targetEdgeCard (i : Fin 2) :
    (TargetExpansion.graph target wall (shiftMembers shrink i).right).edges.card =
      target.edges.card + 1 := by
  simp

theorem candidate_sourceGenus (i : Fin 2) :
    genus (shiftMembers shrink i).datum.sourceGraph = genus data.sourceGraph := by
  fin_cases i
  · exact shrink.shrinkCandidate_sourceGenus
  · exact shift.growCandidate_sourceGenus

theorem candidate_valid (hValid : data.Valid) (i : Fin 2) :
    (shiftMembers shrink i).datum.Valid :=
  (shiftMembers shrink i).datum_valid hValid

/-- One identified member's honest labelling, read back on the shrink member:
this is the only source of the pair's common square coordinate order. -/
noncomputable def initialLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate) :
    StableLengthMatrixLabelling (shiftMembers shrink 0).datum coordinate where
  row := (W3ShiftGraphData.between shrink hValid 0 incoming).row.trans
    incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((occurrenceEquiv target wall (shiftMembers shrink incoming).right).symm.trans
      (occurrenceEquiv target wall (shiftMembers shrink 0).right))

/-- The induced honest labelling of an arbitrary member of the pair. -/
noncomputable def outgoingLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate) (outgoing : Fin 2) :
    StableLengthMatrixLabelling (shiftMembers shrink outgoing).datum coordinate :=
  W3ShiftHonestBalance.labelling shrink hValid
    (initialLabelling shrink hValid incoming incomingFD) outgoing

/-- **Transport to the identified member and back is the identity on its own
labelling.** -/
theorem outgoingLabelling_self (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate) :
    outgoingLabelling shrink hValid incoming incomingFD incoming =
      incomingFD.labelling := by
  have hBetween : (W3ShiftGraphData.between shrink hValid 0 incoming).row =
      (W3ShiftGraphData.rowEquiv shrink hValid 0).symm.trans
        (W3ShiftGraphData.rowEquiv shrink hValid incoming) :=
    W3ShiftGraphData.between_row shrink hValid 0 incoming
  exact labelling_eq_of_fields (trans_cancel_target _ _ _)
    (trans_cancel_row _ _ _ hBetween _)

/-- **The outgoing member's full-dimensional presentation**, transported along
the member-to-member stable-incidence dictionary.  The transport source is the
*identified member*, never the incoming datum. -/
noncomputable def outgoingPresentation (hConnected : graph_connected target)
    (hGenus : genus target = 0) (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling shrink hValid incoming incomingFD outgoing).presentation).det
        ≠ 0) :
    FullDimensionalSourcePresentation (shiftMembers shrink outgoing).datum
      coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (W3ShiftGraphData.between shrink hValid incoming outgoing)
    (candidate_valid shrink hValid outgoing)
    (candidate_targetConnected shrink hConnected outgoing)
    (candidate_targetGenus shrink hGenus outgoing)
    ((candidate_targetEdgeCard shrink outgoing).trans
      (candidate_targetEdgeCard shrink incoming).symm)
    ((candidate_sourceGenus shrink outgoing).trans
      (candidate_sourceGenus shrink incoming).symm)
    (outgoingLabelling shrink hValid incoming incomingFD outgoing)
    outgoingDet

@[simp] theorem outgoingPresentation_labelling (hConnected : graph_connected target)
    (hGenus : genus target = 0) (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling shrink hValid incoming incomingFD outgoing).presentation).det
        ≠ 0) :
    (outgoingPresentation shrink hValid hConnected hGenus incoming outgoing
      incomingFD outgoingDet).labelling =
      outgoingLabelling shrink hValid incoming incomingFD outgoing := rfl

theorem incomingDet_ne_zero (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate) :
    (W3ShiftHonestBalance.squareMatrix shrink hValid
      (initialLabelling shrink hValid incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling shrink hValid incoming incomingFD incoming).presentation).det
      ≠ 0
  rw [outgoingLabelling_self shrink hValid incoming incomingFD]
  exact incomingFD.det_ne_zero

end Member


/-! ## The identified-member exit, with a full-dimensional outgoing source -/

section MemberExit

open DraismaVargas.Infrastructure TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource ThirdEquation FullDimensionalSource
open W3R1SourceProfile W3ShiftSourceCandidates
open W3ShiftLimitRows (shiftMembers)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}
  (shrink : ShrinkData shift) (hValid : data.Valid)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (shiftMembers shrink incoming).datum coordinate)

/-- The pair's two matrices in the identified member's own coordinate order. -/
noncomputable def memberMatrix (outgoing : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling shrink hValid incoming incomingFD outgoing).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  W3ShiftHonestBalance.wallColumn shrink
    (initialLabelling shrink hValid incoming incomingFD)

/-- The canonical outgoing chart velocity at a nonsingular member. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix shrink hValid incoming incomingFD outgoing)
    ((memberMatrix shrink hValid incoming incomingFD incoming).mulVec incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ) (outgoing : Fin 2)
    (hDet : (memberMatrix shrink hValid incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix shrink hValid incoming incomingFD incoming).mulVec incomingVelocity =
      (memberMatrix shrink hValid incoming incomingFD outgoing).mulVec
        (outgoingVelocity shrink hValid incoming incomingFD incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

theorem wallContribution_ne_zero :
    W3ShiftHonestBalance.wallContribution shrink hValid
      (initialLabelling shrink hValid incoming incomingFD) ≠ 0 := by
  intro hZero
  exact incomingDet_ne_zero shrink hValid incoming incomingFD
    ((W3ShiftHonestBalance.det_eq_zero_iff shrink hValid
      (initialLabelling shrink hValid incoming incomingFD) incoming).mpr hZero)

/-- **Equation (3)'s identified-member continuation, with a full-dimensional
outgoing source.**  The outgoing member is the *other* member of the pair, it is
nonsingular of strictly opposite determinant sign, it carries a genuine
`FullDimensionalSourcePresentation` transported along the member-to-member
stable-incidence dictionary, and the segment onto it stays in the positive cone
and carries a cleared rank-one pencil on the member's literal source
subdivision.  No nonsingularity gate is assumed: the incoming member's own
presentation supplies it. -/
theorem exists_member_positive_exit_with_pencil (hConnected : graph_connected target)
    (hGenus : genus target = 0) (root : target.V)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn shrink hValid incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn shrink hValid incoming incomingFD → 0 < z i)
    (hIncomingDirection :
      incomingVelocity (wallColumn shrink hValid incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2, outgoing ≠ incoming ∧
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (shiftMembers shrink outgoing).datum coordinate,
        outgoingFD.labelling =
            outgoingLabelling shrink hValid incoming incomingFD outgoing ∧
          (memberMatrix shrink hValid incoming incomingFD incoming).det *
              (memberMatrix shrink hValid incoming incomingFD outgoing).det < 0 ∧
            ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
              (∀ i, 0 < (z + t • outgoingVelocity shrink hValid incoming incomingFD
                incomingVelocity outgoing) i) ∧
              (memberMatrix shrink hValid incoming incomingFD outgoing).mulVec
                  (z + t • outgoingVelocity shrink hValid incoming incomingFD
                    incomingVelocity outgoing) =
                (memberMatrix shrink hValid incoming incomingFD incoming).mulVec z +
                  t • (memberMatrix shrink hValid incoming incomingFD
                    incoming).mulVec incomingVelocity ∧
              ∃ realization :
                  (shiftMembers shrink outgoing).datum.IntegralRealization,
                ∃ scale : ℕ, 0 < scale ∧
                  (∀ column,
                    (realization.targetLength
                      (outgoingFD.labelling.targetEdge column) : ℚ) =
                      (scale : ℚ) * (z + t • outgoingVelocity shrink hValid incoming
                        incomingFD incomingVelocity outgoing) column) ∧
                  Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, hNe, _hValidOut, hSign, δ, hδ, hStep⟩ :=
    W3ShiftHonestBalance.exists_positive_exit_other shrink hValid
      (initialLabelling shrink hValid incoming incomingFD) hConnected hGenus root
      incoming (wallContribution_ne_zero shrink hValid incoming incomingFD)
      z incomingVelocity
      (outgoingVelocity shrink hValid incoming incomingFD incomingVelocity) hz hzpos
      (fun out hDet ↦ outgoingVelocity_system shrink hValid incoming incomingFD
        incomingVelocity out hDet)
      hIncomingDirection
  have hOutDet : (memberMatrix shrink hValid incoming incomingFD outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  refine ⟨outgoing, hNe,
    outgoingPresentation shrink hValid hConnected hGenus incoming outgoing incomingFD
      hOutDet,
    rfl, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
    pencil.targetLength_eq, pencil.bnExists⟩

end MemberExit


end DraismaVargas.LocalCases.W3ShiftStableIncidence
