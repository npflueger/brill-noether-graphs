import DraismaVargas.LocalCases.W3TrackedAnchoring

/-! # Tracked selection of the actual Figure 28 gauge member

The internal family consumer below uses the literal row compatibility proved
by the concrete anchored producer. The source-facing consumers
(`W3TrackedAnchoring`, `TrackedWallProgressMore`) construct that compatibility
rather than assume it.
-/

namespace DraismaVargas.LocalCases.W3TrackedExit

open DraismaVargas.Infrastructure
open W4StableSource FullDimensionalSource InteriorGraphTracking W3TrackedAnchoring
open W3FourClosure W3FourRegrownColumnSeam W3FourHonestReceipts

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {geometry : FourStarGeometry data wall}
  {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The two selected nonsingular members have the exact incoming-coordinate
row dictionary induced by the actual stable-incidence certificates. -/
theorem outgoingLabelling_row
    (certified : MemberCertificates data wall geometry)
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation (certified.receipts.candidate incoming).datum
      coordinate)
    (outgoing : Fin 4)
    (hOutDet : (squareMatrix certified incoming incomingFD.labelling outgoing).det ≠ 0) :
    (labelling certified incoming incomingFD.labelling outgoing).row =
      (certified.certificate incoming outgoing).row.symm.trans incomingFD.labelling.row := by
  have hIn : (GluingDatum.LengthMatrixPresentation.matrix
      ((gaugeFamily certified incoming incomingFD.labelling).presentation incoming)).det ≠ 0 := by
    rw [gaugeFamily_presentation_start]
    exact incomingFD.det_ne_zero
  have hInFixed := (det_ne_zero_iff certified incoming incomingFD.labelling incoming).mp hIn
  have hOutFixed := (det_ne_zero_iff certified incoming incomingFD.labelling outgoing).mp hOutDet
  have hStart := hRows incoming hInFixed
  have hEnd := hRows outgoing hOutFixed
  ext r
  simp [labelling, rowCoordinates, hStart, hEnd, MemberCertificates.certificate,
    StableGraphIncidence.Equivalence.symm, StableGraphIncidence.Equivalence.trans]

/-- The real positive gauge exit with graph tracking on the SAME selected
full-dimensional candidate, metric segment, and cleared pencil. -/
theorem exists_tracked_member_exit
    (certified : MemberCertificates data wall geometry)
    (wallLabelling : StablePathLabelling data)
    (hRows : RowsCompatible certified wallLabelling)
    (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation (certified.receipts.candidate incoming).datum
      coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root : target.V) (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn certified incoming incomingFD.labelling) = 0)
    (hzpos : ∀ i, i ≠ wallColumn certified incoming incomingFD.labelling → 0 < z i)
    (hDirection : incomingVelocity (wallColumn certified incoming incomingFD.labelling) < 0) :
    ∃ outgoing : Fin 4,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (certified.receipts.candidate outgoing).datum coordinate,
        outgoingFD.labelling = labelling certified incoming incomingFD.labelling outgoing ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation).det *
            (squareMatrix certified incoming incomingFD.labelling outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity certified incoming incomingFD.labelling incoming
            incomingVelocity outgoing) i) ∧
          (squareMatrix certified incoming incomingFD.labelling outgoing).mulVec
              (z + t • outgoingVelocity certified incoming incomingFD.labelling incoming
                incomingVelocity outgoing) =
            (GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation).mulVec z +
              t • (GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation).mulVec
                incomingVelocity ∧
          ∃ realization : (certified.receipts.candidate outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column, (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                (scale : ℚ) * (z + t • outgoingVelocity certified incoming incomingFD.labelling
                  incoming incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  classical
  have hIn : (GluingDatum.LengthMatrixPresentation.matrix
      ((gaugeFamily certified incoming incomingFD.labelling).presentation incoming)).det ≠ 0 := by
    rw [gaugeFamily_presentation_start]
    exact incomingFD.det_ne_zero
  obtain ⟨outgoing, hValidOut, hSign, δ, hδ, hStep⟩ :=
    (gaugeFamily certified incoming incomingFD.labelling).exists_valid_positive_exit_with_pencil
      hValid hConnected hGenus root incoming hIn z incomingVelocity
      (outgoingVelocity certified incoming incomingFD.labelling incoming incomingVelocity)
      hz hzpos
      (fun out hDet ↦ outgoingVelocity_system certified incoming incomingFD.labelling incoming
        incomingVelocity out hDet) hDirection
  have hOutDet : (squareMatrix certified incoming incomingFD.labelling outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  let outFD := W3FourStableIncidence.outgoingPresentation (data := data)
    (certified.certificate incoming outgoing) hValidOut hConnected hGenus
    (certified.memberGenus incoming) (certified.memberGenus outgoing) incomingFD
    (labelling certified incoming incomingFD.labelling outgoing) hOutDet
  have hTrack : Tracks outFD graph label := throughIncidence current outFD
    (certified.certificate incoming outgoing)
    (outgoingLabelling_row certified wallLabelling hRows incoming incomingFD outgoing hOutDet)
  refine ⟨outgoing, outFD, rfl, ⟨hTrack⟩, ?_, δ, hδ, ?_⟩
  · change (GluingDatum.LengthMatrixPresentation.matrix
        ((gaugeFamily certified incoming incomingFD.labelling).presentation incoming)).det *
        (squareMatrix certified incoming incomingFD.labelling outgoing).det < 0 at hSign
    rw [gaugeFamily_presentation_start] at hSign
    exact hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
    rw [gaugeFamily_presentation_start] at hMetric
    exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
      pencil.targetLength_eq, pencil.bnExists⟩

open ThirdEquation W3R1SourceProfile W3FourFamilyMatching
open W3FourSourceCandidates W3FourIncomingMatching TargetExpansion

/-- Actual candidate equality transports the very presentation and Tracks
witness; it does not choose another graph realizing the same matrix. -/
theorem exists_tracks_of_candidate_heq
    {base₁ base₂ : GluingDatum target degree}
    (first : BalancedGlobal.Candidate target degree base₁ wall)
    (second : BalancedGlobal.Candidate target degree base₂ wall)
    (hBase : base₁ = base₂) (hCandidate : HEq first second)
    (fd : FullDimensionalSourcePresentation first.datum coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label) :
    ∃ outFD : FullDimensionalSourcePresentation second.datum coordinate,
      GluingDatum.LengthMatrixPresentation.matrix outFD.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
      outFD.labelling.targetEdge.symm (occurrenceEquiv target wall second.right none) =
        fd.labelling.targetEdge.symm (occurrenceEquiv target wall first.right none) ∧
      Nonempty (Tracks outFD graph label) := by
  subst hBase
  cases eq_of_heq hCandidate
  exact ⟨fd, rfl, rfl, ⟨current⟩⟩

/-- The actual anchored family's three incoming alternatives are literal
members of its four-member outgoing family; the named candidate casts retain
tracking and the incoming coordinate dictionaries. -/
theorem exists_family_matched_tracking
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extraFirst)
    (extraFirst_separate : ¬(data.edgePartition profile.first.1.1.1).Rel
      profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extraSecond)
    (extraSecond_separate : ¬(data.edgePartition profile.second.1.1.1).Rel
      profile.second.1.1.2 extraSecond)
    (plan : PositionPlan data wall
      (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
        extraFirst extraFirst_wall extraFirst_separate)))
    (ac : AnchoredCertificatesWithExtra data wall input profile directions largest_index
      extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
      extraSecond_separate plan)
    (index : Fin 3)
    (fd : FullDimensionalSourcePresentation
      (figure28MembersWithExtra profile directions largest_index extraFirst extraFirst_wall
        extraFirst_separate extraSecond extraSecond_wall extraSecond_separate
        ac.positionMember index).candidate.datum coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label) :
    ∃ incoming : Fin 4,
      ∃ incomingFD : FullDimensionalSourcePresentation
          (ac.certified.receipts.candidate incoming).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
        incomingFD.labelling.targetEdge.symm
            (occurrenceEquiv target wall (ac.certified.receipts.candidate incoming).right none) =
          fd.labelling.targetEdge.symm (occurrenceEquiv target wall
            (figure28MembersWithExtra profile directions largest_index extraFirst extraFirst_wall
              extraFirst_separate extraSecond extraSecond_wall extraSecond_separate
              ac.positionMember index).candidate.right none) ∧
        Nonempty (Tracks incomingFD graph label) := by
  fin_cases index
  · exact ⟨ac.index, exists_tracks_of_candidate_heq _ _ ac.base_index.symm
      ac.candidate_index.symm fd current⟩
  · exact ⟨2, exists_tracks_of_candidate_heq _ _ ac.base_three.symm
      ac.candidate_three.symm fd current⟩
  · exact ⟨3, exists_tracks_of_candidate_heq _ _ ac.base_four.symm
      ac.candidate_four.symm fd current⟩

end DraismaVargas.LocalCases.W3TrackedExit
