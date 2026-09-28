import DraismaVargas.LocalCases.W3InteriorGraphTracking
import DraismaVargas.LocalCases.W3Nd3ArbitraryExit
import DraismaVargas.LocalCases.W3ShiftGraphTracking

/-!
# Same-candidate graph and row tracking for Figure 30

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t3}, Figure 30 and Equation
(4), together with the source/row isomorphism discussion of the subsection on
inherited properties. Figure 30 and the prose of the case attach the two
members to `α = 3` and `α = 4` in opposite ways; like every module of the nd3
chain, this one follows the figure.

## What is proved

The Figure 30 coarse/fine pair already carries literal geometric stable-row
equivalences (`W3Nd3ArbitraryExit.equivalence`, `equivalence_row`, `between`).
Their row formula is therefore read directly off the outgoing labelling
definitions rather than recovered from a matrix identity, and the SAME selected
member that receives the full-dimensional presentation, the metric segment and
the cleared rank-one pencil also receives the `InteriorGraphTracking.Tracks`
witness.

An arbitrary incoming nd3 cover enters through the actual incoming
normalization `W3Nd3IncomingMatching.exists_member_normalization`, whose
orientation dichotomy names the member; the row dictionary is recovered by
`W3InteriorGraphTracking.matched_tracking_of_normalized`, i.e. through actual
natural matrices, the literal target-occurrence map and nonsingularity. Matrix
equality alone is never used to identify a graph or a row choice.

Full-dimensionality of an outgoing member is gated on `det ≠ 0`: only the
member selected by Equation (4)'s opposite-sign balance is required (and
proved) nonsingular, through
`W3Nd3CommonBalance.exists_valid_positive_exit_with_pencil` and
`BalancedGlobal.det_ne_zero_of_mul_det_neg`. Nothing is assumed of the
unselected member.

The classified endpoint `exists_tracked_exit_of_classification` consumes the
`nd3CoarseFine` constructor of `W3IncomingClassification.Classification`
(tag `ClassifiedContinuation.SourceCase.w3Nd3CoarseFine`), which supplies both
the Figure 30 profile and the doubled-direction hypothesis `hSame`. It returns
`W3ShiftGraphTracking.TrackedCertifiedExit`, which retains the base target,
base datum, wall, the actual `BalancedGlobal.Candidate`, the base
Valid/connected/genus-zero stage, outgoing validity, the stable-incidence
dictionary, the full-dimensional presentation, `Tracks`, the metric segment and
the cleared pencil under the SAME binders.

## What is NOT proved

No profile, family membership, outgoing graph/row compatibility, `NoReturn`, or
matrix identity is hypothesised at the source-facing producers; each is proved
upstream. What remains explicit is exactly the bundle the nd3 chain already
consumes: an honest full-dimensional incoming presentation, the single edge
between `a` and `b` whose contraction is a forest with dangling compatibility,
a genuine trivalent star at the contracted wall, a `W3SourceInput` for it, and
the three standard wall data (the wall coordinate vanishes, all other
coordinates are positive, and the incoming velocity points inward there). The
march state (`State`, `CarriesClearedPencil`, `PresentedProgress`) is not
extended, and no march invariant is asserted.

Consumers: the family-by-family tracked-exit table alongside
`W3TrackedExit` (Figure 28),
`W3ShiftTrackedFinal.trackedExit_of_classification` (Figure 29) and
`W3Nd2GraphTracking.exists_tracked_exit_of_classification` (Figure 31); this
module supplies the Figure 30 row of that table.
-/

namespace DraismaVargas.LocalCases.W3Nd3GraphTracking

open DraismaVargas.Infrastructure
open W4StableSource ThirdEquation W3R1SourceProfile FullDimensionalSource InteriorGraphTracking
open W3Nd3ArbitraryExit W3Nd3SourceCandidates
open GraphContraction GluingContraction ContractionRamification WallDegeneration TargetExpansion

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-! ## One abstract coordinate cancellation

`W3Nd3ArbitraryExit` proves the same cancellation privately; it is restated
here at abstract types, where nothing has to be unfolded, so that the member
wall column can be recognized as the original contracted column. -/

section Cancellation

variable {α β γ δ : Type*}

/-- Going out through one occurrence dictionary and back through another
cancels, read at the wall column: the common coordinate order's `none` is the
identified member's own wall occurrence. -/
private theorem symm_trans_cancel (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) (x : γ) :
    ((e.trans (A.symm.trans B)).trans B.symm).symm x = e.symm (A x) := by
  simp

/-- The row half: transporting to the common first member and out to another
member is the same as the direct member-to-member comparison. -/
private theorem trans_cancel_between {ε : Type*} (P : α ≃ β) (Q : α ≃ γ) (R : α ≃ δ)
    (S : δ ≃ ε) :
    P.symm.trans (Q.trans ((Q.symm.trans R).trans S)) = (R.symm.trans P).symm.trans S := by
  ext x
  simp

end Cancellation

section Member
variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)

/-- Every member-to-member comparison of the actual Figure 30 pair has exactly
the row map used in Equation (4)'s matrix calculation. -/
theorem between_row (first second : Fin 2) :
    (between input profile hSame first second).row =
      (W3Nd3CommonBalance.rowEquiv input profile hSame first).symm.trans
        (W3Nd3CommonBalance.rowEquiv input profile hSame second) := by
  have h : ∀ position : Fin 2, (equivalence input profile hSame position).row =
      W3Nd3CommonBalance.rowEquiv input profile hSame position :=
    equivalence_row input profile hSame
  change (equivalence input profile hSame first).row.symm.trans
      (equivalence input profile hSame second).row = _
  rw [h first, h second]
  rfl

/-- The actual Figure 30 outgoing row labels are the incoming labels read
through the actual member-to-member incidence map. This is proved from the
geometric labelling definitions, not from a matrix identity. -/
theorem outgoingLabelling_row (outgoing : Fin 2) :
    (outgoingLabelling input profile hSame incoming incomingFD outgoing).row =
      (between input profile hSame incoming outgoing).row.symm.trans
        incomingFD.labelling.row := by
  have hIn := between_row input profile hSame 0 incoming
  have hOut := between_row input profile hSame incoming outgoing
  change (W3Nd3CommonBalance.rowEquiv input profile hSame outgoing).symm.trans
      ((W3Nd3CommonBalance.rowEquiv input profile hSame 0).trans
        ((between input profile hSame 0 incoming).row.trans incomingFD.labelling.row)) = _
  rw [hIn, hOut]
  exact trans_cancel_between _ _ _ _

/-- **The tracked identified-member Figure 30 continuation.** The selected
outgoing member carrying the full-dimensional presentation, the opposite
determinant sign, the positive metric segment and the cleared pencil is the
very member that carries the row-labelled graph. -/
theorem exists_tracked_member_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input profile hSame incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile hSame incoming incomingFD → 0 < z i)
    (hIncomingDirection :
      incomingVelocity (wallColumn input profile hSame incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum coordinate,
        outgoingFD.labelling =
            outgoingLabelling input profile hSame incoming incomingFD outgoing ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (memberMatrix input profile hSame incoming incomingFD incoming).det *
            (memberMatrix input profile hSame incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input profile hSame incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input profile hSame incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input profile hSame incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input profile hSame incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input profile hSame incoming incomingFD
                incoming).mulVec incomingVelocity ∧
          ∃ realization :
              (W3Nd3CommonBalance.candidates input profile hSame
                outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity input profile hSame incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    exists_member_positive_exit_with_pencil input profile hSame incoming incomingFD
      hConnected hGenus z incomingVelocity hz hzpos hIncomingDirection
  refine ⟨outgoing, outgoingFD, hLabelling, ⟨throughIncidence current outgoingFD
    (between input profile hSame incoming outgoing) ?_⟩, hSign, δ, hδ, hStep⟩
  rw [hLabelling]
  exact outgoingLabelling_row input profile hSame incoming incomingFD outgoing

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
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

include hForest hCompat

/-- An arbitrary incoming W3 nd3 cover is a named Figure 30 member carrying an
honest presentation in the ORIGINAL coordinates, together with the actual
stable-incidence dictionary, its recovered row equation and the transported
graph tracking. The orientation dichotomy of
`W3Nd3IncomingMatching.exists_member_normalization` names the member; the row
equation comes from the natural matrices and the literal occurrence map
through `W3InteriorGraphTracking.matched_tracking_of_normalized`. -/
theorem exists_matched_tracking
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ position : Fin 2,
      ∃ fd : FullDimensionalSourcePresentation
          (W3Nd3CommonBalance.candidates input profile hSame position).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (W3Nd3CommonBalance.columnEquiv input profile hSame position none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence data
            (W3Nd3CommonBalance.candidates input profile hSame position).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  rcases W3Nd3IncomingMatching.exists_member_normalization data hc hab hOne fullDim hForest
      hCompat star input profile hSame with
    ⟨hShared, hColumns, hNorm⟩ | ⟨hLargest, hColumns, hNorm⟩
  · obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
      W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
    refine ⟨0, fd, hMatrix, ?_, _, hRows, hTrack⟩
    rw [hEdge]
    change fullDim.labelling.targetEdge.symm
      ((GluingTransport.edgeEquiv
          (W3Nd3IncomingMatching.coarseTargetIso data hc hab hOne fullDim star input profile
            hSame hShared)).symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (coarseCandidate input profile hSame).right none)) = _
    rw [← hColumns none, Equiv.symm_apply_apply]
    rfl
  · obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
      W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
    refine ⟨1, fd, hMatrix, ?_, _, hRows, hTrack⟩
    rw [hEdge]
    change fullDim.labelling.targetEdge.symm
      ((GluingTransport.edgeEquiv
          (W3Nd3IncomingMatching.fineTargetIso data hc hab hOne fullDim star input profile
            hSame hLargest)).symm
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
          (fineCandidate input profile hSame).right none)) = _
    rw [← hColumns none, Equiv.symm_apply_apply]
    rfl

/-- **The tracked Figure 30 exit, in the incoming cover's own coordinates.**
The wall coordinate is the original contracted column, and both determinants
and the affine metric equation are taken against the original incoming length
matrix on its own retained rows. The selected outgoing member is
full-dimensional with strictly opposite determinant sign, carries the actual
stable-incidence dictionary and the row-labelled graph, the whole segment stays
positive, and the cleared rank-one pencil is on that member's literal source
subdivision. -/
theorem exists_tracked_exit_with_pencil
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence data
          (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum) ∧
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
                (W3Nd3CommonBalance.candidates input profile hSame
                  outgoing).datum.IntegralRealization,
              ∃ scale : ℕ, 0 < scale ∧
                (∀ column,
                  (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                    (scale : ℚ) * (z + t • velocity) column) ∧
                Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨position, fd, hMatrix, hWall, hGraph, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking data hc hab hOne fullDim hForest hCompat star input profile hSame
      current
  have hWall' : W3Nd3ArbitraryExit.wallColumn input profile hSame position fd =
      fullDim.labelling.targetEdge.symm contracted :=
    (symm_trans_cancel _ _ _ none).trans hWall
  have hSelf : W3Nd3ArbitraryExit.memberMatrix input profile hSame position fd position =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
    unfold W3Nd3ArbitraryExit.memberMatrix
    rw [W3Nd3ArbitraryExit.outgoingLabelling_self input profile hSame position fd]
    exact hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hOutTrack, hSign, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit input profile hSame position fd hTrack
      (graph_connected_contract target hab hOne fullDim.targetConnected)
      ((genus_contract target hab hOne).trans fullDim.targetGenus)
      z incomingVelocity (hWall' ▸ hz) (hWall' ▸ hzpos) (hWall' ▸ hDirection)
  have hOutMatrix : W3Nd3ArbitraryExit.memberMatrix input profile hSame position fd outgoing =
      GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation := by
    unfold W3Nd3ArbitraryExit.memberMatrix
    rw [hLabelling]
  refine ⟨outgoing, outgoingFD,
    ⟨hGraph.trans (W3Nd3ArbitraryExit.between input profile hSame position outgoing)⟩,
    hOutTrack,
    ?_,
    W3Nd3ArbitraryExit.outgoingVelocity input profile hSame position fd
      incomingVelocity outgoing,
    δ, hδ, ?_⟩
  · simpa only [hSelf, hOutMatrix] using hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by simpa only [hSelf, hOutMatrix] using hMetric, hPencil⟩

/-! ## Retaining the actual Candidate and its base stage -/

include star input profile hSame in
/-- The finite coarse/fine member names identify the actual Figure 30
Candidate before forgetting the family index. Its valid connected genus-zero
base stage, full presentation, tracking and pencil stay together in the
march-facing package. -/
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
      hSame (graph := graph) (label := label) current z incomingVelocity hz hzpos hDirection
  obtain ⟨outgoing, outgoingFD, hGraph, hTrack, hSign, velocity, δ, hδ, hStep⟩ := hExit
  have hConnected := graph_connected_contract target hab hOne fullDim.targetConnected
  have hGenus := (genus_contract target hab hOne).trans fullDim.targetGenus
  fin_cases outgoing
  · exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, coarseCandidate input profile hSame,
      input.valid, hConnected, hGenus, outgoingFD.valid, hGraph, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, fineCandidate input profile hSame,
      input.valid, hConnected, hGenus, outgoingFD.valid, hGraph, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩

/-- The actual nd3 classification supplies both the Figure 30 profile and the
doubled direction. No profile, family membership, or outgoing graph/row
compatibility is assumed here. -/
theorem exists_tracked_exit_of_classification
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (classification : W3IncomingClassification.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w3Nd3CoarseFine)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  cases classification with
  | four => cases hTag
  | shift => cases hTag
  | nd2CoarseFine => cases hTag
  | nd3CoarseFine profile hSame _pair _largest =>
    exact exists_tracked_certified_exit data hc hab hOne fullDim hForest hCompat star input
      profile hSame current z incomingVelocity hz hzpos hDirection

end Arbitrary
end DraismaVargas.LocalCases.W3Nd3GraphTracking
