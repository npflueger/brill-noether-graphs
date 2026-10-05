module

public import DraismaVargasCount.M11MultiplicityBalance
public import DraismaVargasCount.W2M1kTransitionSiting
public import DraismaVargas.LocalCases.M11FullDimensional

@[expose] public section

/-!
# The incoming M11 third row has denominator one

In a nonsingular joined member, the new index-two occurrence lies at the end
of the row containing the retained index-one third occurrence.  Its unique
transition makes every other index on that row one.  Retention transports
every incoming occurrence onto this row, so its incoming denominator is one.

This discharges the oddness hypothesis of
`M11MultiplicityBalance.sum_signedMult_eq_zero_of_conditional_odd`, and so proves the
balancing identity of Draisma–Vargas Part I, Equation (6) (Case `{w2-r2-nd3-M-11}`,
Figure 32) on the three members of the family (`sum_signedMult_eq_zero`).  It enters the
star parity at `M11` walls, part of the trivalent wall step of
`DraismaVargasCount.Assembly`.
-/

namespace DraismaVargas.Count.M11IncomingDenominator

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open StableLocalProperties FullDimensionalSource
open M11SourceCandidates M11JoinedGeometry M11JoinedSurvival
open M11JoinedBranch M11JoinedBranchClassification
open LimitChainCore
open TrivalentWeight RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- Every old third-row occurrence retains its index and row and avoids the
new occurrence.  The proof uses the geometric quotient lift
`M11JoinedStableLift.stablePathLift`. -/
theorem transport_thirdRow :
    ∀ edge ∈ incomingRowEdges data
        (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩),
      ∃ image : (joinedPattern data star block hCard).candidate.datum.SourceEdge,
        OnRow (joinedPattern data star block hCard).candidate.datum
          (joined_retainedSingle input profile hCard).stablePath image ∧
        image ≠ (joinedPattern data star block hCard).candidate.newSourceEdge block.1 ∧
        (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex image =
          data.sourceEdgeIndex edge := by
  intro edge hEdge
  obtain ⟨hSurvives, hRow⟩ := (onRow_iff_mem_incomingRowEdges _ _).mpr hEdge
  refine ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge edge,
    ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hSurvives, ?_⟩,
    oldEnd_ne_thirdEnd input profile hCard edge,
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _⟩
  exact congrArg (M11JoinedStableLift.stablePathLift input profile hCard) hRow

include input in
/-- The opposite endpoint branches, so the new occurrence has only the
selected single-direction endpoint in the interior of the stable row. -/
theorem newSourceEdge_terminal :
    ∀ u, Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge block.1) u →
      nonDanglingValency (joinedPattern data star block hCard).candidate.datum u = 2 →
      u = singleVertex profile hCard := by
  intro u hIncident hValency
  have hEnds := W2M1kTransitionSiting.incident_newSourceEdge_endpoints
    (joinedPattern data star block hCard).candidate block.1 hIncident
  have hBranch := branchVertex_valency input profile hCard
  have hLabels := profile.labels_ne
  by_cases hSingle : profile.singleLabel = 0
  · have hDouble : profile.doubleLabel = 1 := by omega
    rcases hEnds with hOld | hFresh
    · simpa [singleVertex, endpoint, hSingle, wallSide] using hOld
    · simp only [branchVertex, endpoint, hDouble, show (1 : Fin 2) ≠ 0 by decide,
        ↓reduceIte] at hBranch
      have hEq : u = (joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (freshVertex target) block.1 := hFresh
      rw [hEq, hBranch] at hValency
      omega
  · have hSingleOne : profile.singleLabel = 1 := by omega
    have hDouble : profile.doubleLabel = 0 := by omega
    rcases hEnds with hOld | hFresh
    · simp only [branchVertex, endpoint, hDouble, ↓reduceIte] at hBranch
      have hEq : u = (joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (oldVertex target wall) block.1 := hOld
      rw [hEq, hBranch] at hValency
      omega
    · simpa [singleVertex, endpoint, hSingleOne, wallSide] using hFresh

include input in
/-- The sharp incoming denominator, from the joined member's presentation.
The row-calculus witness is the new edge of index two, not the retained edge
of index one. -/
theorem incomingRowDenominator_third_eq_one
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      (joinedPattern data star block hCard).candidate.datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) = 1 := by
  have hNew := joined_distinguished_survives input profile hCard
  have hPartner : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge profile.third.1) :=
    (joined_retainedSingle input profile hCard).2
  have hNewRow : OnRow (joinedPattern data star block hCard).candidate.datum
      (joined_retainedSingle input profile hCard).stablePath
      ((joinedPattern data star block hCard).candidate.newSourceEdge block.1) :=
    ⟨hNew, joined_distinguished_stablePath_eq input profile hCard⟩
  have hNewIndex : (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex
      ((joinedPattern data star block hCard).candidate.newSourceEdge block.1) = 2 := by
    rw [joined_newSourceEdge_index, hCard]
  have hPartnerIndex : (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex
      ((joinedPattern data star block hCard).candidate.oldSourceEdge profile.third.1) = 1 := by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
    exact index_eq_one_of_blockCard_eq_two profile hCard profile.third
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hNewRow
    (by rw [hNewIndex]; decide)
  have hPartnerIncident := joined_third_incident profile hCard
  have hNewIncident := newSourceEdge_incident_endpoint data star block hCard
    profile.singleLabel block.1
  have hNe := oldEnd_ne_thirdEnd input profile hCard profile.third.1
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    (singleVertex_valency input profile hCard) hNewRow hNewIncident hPartner
    hPartnerIncident (Ne.symm hNe) (by rw [hNewIndex, hPartnerIndex]; decide)
  exact Nat.dvd_one.mp (RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hPartner hPartnerIncident hNe
    (newSourceEdge_terminal input profile hCard) hPartnerIndex
    (transport_thirdRow input profile hCard))

open M11CommonBalance

/-- Rebuild a joined presentation in any chosen common coordinates from a
full-dimensional incoming member and a nonzero joined determinant. -/
noncomputable def joinedPresentation
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate)
    (hDet : (squareMatrix input profile hCard initial 2).det ≠ 0) :
    FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard 2).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (M11StableGraphs.between input profile hCard incoming 2)
    (M11RemoteCandidates.candidates_valid input profile hCard 2)
    (M11FullDimensional.candidate_targetConnected input profile hCard hConnected 2)
    (M11FullDimensional.candidate_targetGenus input profile hCard hGenus 2)
    ((M11FullDimensional.candidate_targetEdgeCard input profile hCard 2).trans
      (M11FullDimensional.candidate_targetEdgeCard input profile hCard incoming).symm)
    ((M11SourceGenus.candidates_sourceGenus input profile hCard 2).trans
      (M11SourceGenus.candidates_sourceGenus input profile hCard incoming).symm)
    (labelling input profile hCard initial 2) hDet

/-- Part I, Equation (6), on the three members of the family: their signed
multiplicities sum to zero.  Beyond a full-dimensional incoming member, no
hypothesis on denominators or on the geometry of the members remains. -/
theorem sum_signedMult_eq_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate) :
    ∑ position : Fin 3,
      signedMult (labelling input profile hCard initial position).presentation = 0 := by
  apply M11MultiplicityBalance.sum_signedMult_eq_zero_of_conditional_odd
    input profile hCard initial hConnected hGenus
  intro hDet
  rw [incomingRowDenominator_third_eq_one input profile hCard
    (joinedPresentation input profile hCard hConnected hGenus incoming initial incomingFD hDet)]
  simp

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The same balance in canonical coordinates. -/
theorem sum_signedMult_canonical_eq_zero
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum
      (Option target.edges)) :
    ∑ position : Fin 3, signedMult
      (labelling input profile hCard (canonicalInitialLabelling input profile hCard)
        position).presentation = 0 :=
  sum_signedMult_eq_zero input profile hCard hConnected hGenus incoming
    (canonicalInitialLabelling input profile hCard) incomingFD

end DraismaVargas.Count.M11IncomingDenominator
