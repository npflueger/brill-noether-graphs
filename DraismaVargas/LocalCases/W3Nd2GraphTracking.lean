import DraismaVargas.LocalCases.W3InteriorGraphTracking
import DraismaVargas.LocalCases.W3ShiftGraphTracking
import DraismaVargas.LocalCases.W3Nd2PositiveExit

/-!
# Same-candidate graph and row tracking for Figure 31

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd2}`, Figure 31 and Equation (5). The coarse/fine
pair uses literal stable-row equivalences. Their row formula is read directly
from the outgoing labelling definitions. The same selected member receives its
full-dimensional presentation, Tracks witness, metric segment and pencil.

The incoming cover is normalized through its actual coarse/fine target
placement and partition census. Generic natural-matrix recovery supplies the
exact row equation; no graph/row compatibility or family membership is assumed
at the final source-facing producer. The classified endpoint returns the
actual Candidate, its valid connected genus-zero base stage, and all outgoing
witnesses under that Candidate. This does not modify the march state.
-/

namespace DraismaVargas.LocalCases.W3Nd2GraphTracking

open DraismaVargas.Infrastructure
open W4StableSource ThirdEquation W3R1SourceProfile FullDimensionalSource InteriorGraphTracking
open W3Nd2PositiveExit W3Nd2SourceCandidates W3Nd2FineCandidates
open W3Nd2IncomingMemberMatching W3Nd2IncomingDirection
open GraphContraction GluingContraction ContractionRamification WallDegeneration TargetExpansion

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

section Member
variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star) (profile : Nd2Profile data input.distinguishedBlock)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)

theorem outgoingLabelling_row (outgoing : Fin 2) :
    (outgoingLabelling input profile incoming incomingFD outgoing).row =
      (between input profile incoming outgoing).row.symm.trans incomingFD.labelling.row := by
  ext r
  simp [outgoingLabelling, W3Nd2CommonBalance.labelling,
    W3Nd2CommonBalance.sourceCoordinates, initialLabelling, between,
    StableGraphIncidence.Equivalence.symm, StableGraphIncidence.Equivalence.trans,
    equivalence_row]

theorem exists_tracked_member_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input profile incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity
      (wallColumn input profile incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate,
        outgoingFD.labelling = outgoingLabelling input profile incoming incomingFD outgoing ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (memberMatrix input profile incoming incomingFD incoming).det *
            (memberMatrix input profile incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input profile incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input profile incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input profile incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input profile incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input profile incoming incomingFD incoming).mulVec
                incomingVelocity ∧
          ∃ realization :
              (W3Nd2CommonBalance.candidates input profile outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity input profile incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, hStep⟩ :=
    W3Nd2PositiveExit.exists_positive_exit_with_pencil input profile incoming incomingFD
      hConnected hGenus z incomingVelocity hz hzpos hIncomingDirection
  refine ⟨outgoing, outgoingFD, hLabelling, ⟨throughIncidence current outgoingFD
    (between input profile incoming outgoing) ?_⟩, hSign, hStep⟩
  rw [hLabelling]
  exact outgoingLabelling_row input profile incoming incomingFD outgoing

end Member

section Arbitrary
-- The source-facing certified-family and march interfaces use small graphs.
variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat
theorem exists_matched_tracking
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ position : Fin 2,
      ∃ fd : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile position).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (W3Nd2CommonBalance.columnEquiv input profile position none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence data
            (W3Nd2CommonBalance.candidates input profile position).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  rcases exists_member_normalization data hc hab hOne fullDim hForest hCompat star
      input profile with ⟨hSmall, hColumns, hNorm⟩ | ⟨hLarge, hColumns, hNorm⟩
  · obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
      W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
    refine ⟨0, fd, hMatrix, ?_, _, hRows, hTrack⟩
    rw [hEdge]
    change fullDim.labelling.targetEdge.symm
      ((GluingTransport.edgeEquiv
          (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)).symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (coarseCandidate input profile).right none)) = _
    rw [← hColumns none, Equiv.symm_apply_apply]
    rfl
  · obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
      W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
    refine ⟨1, fd, hMatrix, ?_, _, hRows, hTrack⟩
    rw [hEdge]
    change fullDim.labelling.targetEdge.symm
      ((GluingTransport.edgeEquiv
          (fineTargetIso data hc hab hOne fullDim star input profile hLarge)).symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (fineCandidate input profile).right none)) = _
    rw [← hColumns none, Equiv.symm_apply_apply]
    rfl


theorem exists_tracked_exit_with_pencil
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence data
          (W3Nd2CommonBalance.candidates input profile outgoing).datum) ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).det *
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
            ∃ realization :
                (W3Nd2CommonBalance.candidates input profile outgoing).datum.IntegralRealization,
              ∃ scale : ℕ, 0 < scale ∧
                (∀ column,
                  (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                    (scale : ℚ) * (z + t • velocity) column) ∧
                Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨position, fd, hMatrix, hWall, hGraph, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking data hc hab hOne fullDim hForest hCompat star input profile current
  have hWall' : W3Nd2PositiveExit.wallColumn input profile position fd =
      fullDim.labelling.targetEdge.symm contracted := by
    simpa [W3Nd2PositiveExit.wallColumn, W3Nd2CommonBalance.wallColumn,
      W3Nd2CommonBalance.targetCoordinates, W3Nd2PositiveExit.initialLabelling] using hWall
  have hSelf : W3Nd2PositiveExit.memberMatrix input profile position fd position =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
    unfold W3Nd2PositiveExit.memberMatrix
    rw [W3Nd2PositiveExit.outgoingLabelling_self input profile position fd]
    exact hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hOutTrack, hSign, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit input profile position fd hTrack
      (graph_connected_contract target hab hOne fullDim.targetConnected)
      ((genus_contract target hab hOne).trans fullDim.targetGenus)
      z incomingVelocity (hWall' ▸ hz) (hWall' ▸ hzpos) (hWall' ▸ hDirection)
  have hOutMatrix : W3Nd2PositiveExit.memberMatrix input profile position fd outgoing =
      GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation := by
    unfold W3Nd2PositiveExit.memberMatrix
    rw [hLabelling]
  refine ⟨outgoing, outgoingFD,
    ⟨hGraph.trans (W3Nd2PositiveExit.between input profile position outgoing)⟩, hOutTrack,
    ?_, W3Nd2PositiveExit.outgoingVelocity input profile position fd incomingVelocity outgoing,
    δ, hδ, ?_⟩
  · simpa only [hSelf, hOutMatrix] using hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by simpa only [hSelf, hOutMatrix] using hMetric, hPencil⟩

/-! ## Retaining the actual Candidate and its base stage -/

include star input profile in
/-- The finite coarse/fine member names identify the actual Candidate before
forgetting the family index. Its valid connected genus-zero base stage, full
presentation, tracking and pencil stay together in the march-facing package. -/
theorem exists_tracked_certified_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  have hExit :=
    exists_tracked_exit_with_pencil data hc hab hOne fullDim hForest hCompat star input profile
      (graph := graph) (label := label) current z incomingVelocity hz hzpos hDirection
  obtain ⟨outgoing, outgoingFD, hGraph, hTrack, hSign, velocity, δ, hδ, hStep⟩ := hExit
  have hConnected := graph_connected_contract target hab hOne fullDim.targetConnected
  have hGenus := (genus_contract target hab hOne).trans fullDim.targetGenus
  fin_cases outgoing
  · exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, coarseCandidate input profile,
      input.valid, hConnected, hGenus, outgoingFD.valid, hGraph, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, fineCandidate input profile,
      input.valid, hConnected, hGenus, outgoingFD.valid, hGraph, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩

/-- The actual nd2 classification supplies the profile. No profile, family
membership, or outgoing graph/row compatibility is assumed here. -/
theorem exists_tracked_exit_of_classification
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (classification : W3IncomingClassification.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w3Nd2CoarseFine)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  cases classification with
  | four => cases hTag
  | shift => cases hTag
  | nd3CoarseFine => cases hTag
  | nd2CoarseFine profile =>
    exact exists_tracked_certified_exit data hc hab hOne fullDim hForest hCompat star input
      profile current z incomingVelocity hz hzpos hDirection

end Arbitrary
end DraismaVargas.LocalCases.W3Nd2GraphTracking
