module

public import DraismaVargas.LocalCases.W3InteriorGraphTracking
public import DraismaVargas.LocalCases.W3ShiftClosureFinal

@[expose] public section

/-!
# Same-candidate tracking for Figure 29's pair

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and Equation (3). The pair already has
literal geometric row equivalences; cancellation in its labelling definitions
proves the exact member-to-member row equation. The existing real positive
exit supplies the outgoing full-dimensional presentation and pencil, and
tracking is attached to that same binder. Incoming normalization reuses the
checked natural-matrix recovery lemma, not a matrix-only graph existential.

The source-local census/dichotomy remain explicit at the arbitrary-pair
consumer, as in the existing producer. The companion `W3ShiftTrackedFinal`
derives the census from classification and carries the Position II.a incoming
branch swaps. Neither module changes the global march state.
-/

namespace DraismaVargas.LocalCases.W3ShiftGraphTracking

open DraismaVargas.Infrastructure
open W4StableSource ThirdEquation W3R1SourceProfile FullDimensionalSource InteriorGraphTracking
open W3ShiftSourceCandidates W3ShiftLimitRows W3ShiftStableIncidence
open GraphContraction GluingContraction ContractionRamification WallDegeneration TargetExpansion
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3ShiftIncomingMatching

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

section Member
variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}
  (shrink : ShrinkData shift) (hValid : data.Valid)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation (shiftMembers shrink incoming).datum coordinate)

theorem outgoingLabelling_row (outgoing : Fin 2) :
    (outgoingLabelling shrink hValid incoming incomingFD outgoing).row =
      (W3ShiftGraphData.between shrink hValid incoming outgoing).row.symm.trans
        incomingFD.labelling.row := by
  rw [W3ShiftGraphData.between_row]
  ext r
  simp [outgoingLabelling, W3ShiftHonestBalance.labelling,
    W3ShiftHonestBalance.sourceCoordinates, initialLabelling,
    W3ShiftGraphData.between_row]

theorem exists_tracked_member_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hConnected : graph_connected target)
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
          Nonempty (Tracks outgoingFD graph label) ∧
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
  obtain ⟨outgoing, hNe, outgoingFD, hLabelling, hSign, hStep⟩ :=
    W3ShiftStableIncidence.exists_member_positive_exit_with_pencil shrink hValid incoming incomingFD
      hConnected hGenus root z incomingVelocity hz hzpos hIncomingDirection
  refine ⟨outgoing, hNe, outgoingFD, hLabelling, ⟨throughIncidence current outgoingFD
    (W3ShiftGraphData.between shrink hValid incoming outgoing) ?_⟩, hSign, hStep⟩
  rw [hLabelling]
  exact outgoingLabelling_row shrink hValid incoming incomingFD outgoing

end Member

section Arbitrary
variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
  (shrink : ShrinkData shift)
  (selectedLeft selectedRight selectedNew : SheetPartition degree)

include hForest hMoving

theorem exists_matched_tracking
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft selectedRight
      selectedNew)
    (hDichotomy : ∃ index : Fin 2,
      (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index) :
    ∃ index : Fin 2,
      (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index ∧
      ∃ fd : FullDimensionalSourcePresentation (shiftMembers shrink index).datum
          coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (shiftMembers shrink index).right none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence data (shiftMembers shrink index).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  obtain ⟨index, hIndex, hColumns, hNorm⟩ :=
    W3ShiftIncomingMatching.exists_member_normalization data hc hab hOne fullDim hForest star
      input shift hMoving shrink selectedLeft selectedRight selectedNew hCensus hDichotomy
  obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
    W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
  refine ⟨index, hIndex, fd, hMatrix, ?_, _, hRows, hTrack⟩
  rw [hEdge, ← hColumns none, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

theorem exists_tracked_exit_in_original_coordinates
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft selectedRight
      selectedNew)
    (hDichotomy : ∃ index : Fin 2,
      (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    ∃ incoming outgoing : Fin 2, outgoing ≠ incoming ∧
      (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink incoming ∧
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (shiftMembers shrink outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence data
          (shiftMembers shrink outgoing).datum) ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).det *
            (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).det < 0 ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧
          ∀ t : ℚ, 0 < t → t ≤ δ →
            (∀ i, 0 < (z + t • velocity) i) ∧
            (GluingDatum.LengthMatrixPresentation.matrix
                outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
              (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec z +
                t • (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec incomingVelocity ∧
            ∃ realization : (shiftMembers shrink outgoing).datum.IntegralRealization,
              ∃ scale : ℕ, 0 < scale ∧
                (∀ column,
                  (realization.targetLength
                    (outgoingFD.labelling.targetEdge column) : ℚ) =
                    (scale : ℚ) * (z + t • velocity) column) ∧
                Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨incoming, hIndex, fd, hMatrix, hWall, hGraph, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking data hc hab hOne fullDim hForest
      star input shift hMoving shrink selectedLeft selectedRight selectedNew current hCensus
      hDichotomy
  have hWall' : wallColumn shrink input.valid incoming fd =
      fullDim.labelling.targetEdge.symm contracted :=
    by
      simpa [wallColumn, W3ShiftHonestBalance.wallColumn,
        W3ShiftHonestBalance.targetCoordinates, initialLabelling] using hWall
  have hSelf : memberMatrix shrink input.valid incoming fd incoming =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
    unfold memberMatrix
    rw [outgoingLabelling_self shrink input.valid incoming fd]
    exact hMatrix
  obtain ⟨outgoing, hNe, outgoingFD, hLabelling, hOutTrack, hSign, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit shrink input.valid incoming fd hTrack
      (graph_connected_contract target hab hOne fullDim.targetConnected)
      ((genus_contract target hab hOne).trans fullDim.targetGenus) ⟨a, hab⟩
      z incomingVelocity (hWall' ▸ hz) (hWall' ▸ hzpos) (hWall' ▸ hDirection)
  have hOutMatrix : memberMatrix shrink input.valid incoming fd outgoing =
      GluingDatum.LengthMatrixPresentation.matrix
        outgoingFD.labelling.presentation := by
    unfold memberMatrix
    rw [hLabelling]
  refine ⟨incoming, outgoing, hNe, hIndex, outgoingFD,
    ⟨hGraph.trans (W3ShiftGraphData.between shrink input.valid incoming outgoing)⟩, hOutTrack,
    ?_, outgoingVelocity shrink input.valid incoming fd incomingVelocity outgoing,
    δ, hδ, ?_⟩
  · simpa only [hSelf, hOutMatrix] using hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by simpa only [hSelf, hOutMatrix] using hMetric, hPencil⟩


end Arbitrary

section Shrink
universe u
variable {target : CFGraph.{u}} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-- The source-facing exit package retains the actual resolution Candidate
and its valid connected genus-zero base stage. Tracking, metric data and
pencil remain under that SAME Candidate/full-dimensional-presentation binder.
It defines required outputs, not their existence. -/
def TrackedCertifiedExit {data : GluingDatum target degree}
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (graph : CubicDarts.CubicDartGraph D V) (label : D → coordinate)
    (z incomingVelocity : coordinate → ℚ) : Prop :=
  ∃ (baseTarget : CFGraph.{u}) (base : GluingDatum baseTarget degree) (wall : baseTarget.V),
    ∃ candidate : BalancedGlobal.Candidate baseTarget degree base wall,
    base.Valid ∧ graph_connected baseTarget ∧ genus baseTarget = 0 ∧
    candidate.datum.Valid ∧
    Nonempty (StableGraphIncidence.Equivalence data candidate.datum) ∧
    ∃ outgoingFD : FullDimensionalSourcePresentation candidate.datum coordinate,
      Nonempty (Tracks outgoingFD graph label) ∧
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
      ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • velocity) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
          (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).mulVec incomingVelocity ∧
        ∃ realization : candidate.datum.IntegralRealization, ∃ scale : ℕ, 0 < scale ∧
          (∀ column,
            (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
              (scale : ℚ) * (z + t • velocity) column) ∧
          Utilities.BNExists realization.sourceSpec.graph 1 degree


variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
  (shrink : ShrinkData shift)

include hForest hMoving in
/-- Actual Position II.b exit. Its selected census is precisely the branch
returned by the existing source-facing census theorem; the pair dictionary,
incoming normalization, outgoing graph/row map and nonsingularity are derived. -/
theorem exists_tracked_exit_of_shrinkPosition
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (hCensus : SelectedCensus data hc hab hOne star input (shiftClasses shrink 0).1
      (shiftClasses shrink 0).2.1 (shiftClasses shrink 0).2.2)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  obtain ⟨incoming, outgoing, _hNe, _hIndex, outgoingFD, hGraph, hTrack, hSign,
    velocity, δ, hδ, hStep⟩ :=
    exists_tracked_exit_in_original_coordinates data hc hab hOne fullDim hForest star
      input shift hMoving shrink _ _ _ current hCensus
      (W3ShiftClosureUnconditional.dichotomy_zero shrink) z incomingVelocity hz hzpos hDirection
  exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, shiftMembers shrink outgoing,
    input.valid, graph_connected_contract target hab hOne fullDim.targetConnected,
    (genus_contract target hab hOne).trans fullDim.targetGenus,
    outgoingFD.valid, hGraph, outgoingFD,
    hTrack, hSign, velocity, δ, hδ, hStep⟩

end Shrink

end DraismaVargas.LocalCases.W3ShiftGraphTracking
