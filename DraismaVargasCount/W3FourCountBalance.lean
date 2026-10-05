module

public import DraismaVargasCount.W3FourMultiplicityBalance
public import DraismaVargasCount.W3FourIncomingDenominator
public import DraismaVargasCount.W3FourReversedDenominator

@[expose] public section

/-!
# Completion of Equation (2) on the actual four-member family

This module connects the arithmetic assembly to the exact Figure 28 members
(Draisma--Vargas Part I, arXiv:1909.12924, Equation (2)).
One selected full-dimensional chart is transported to every nonsingular member;
those members then supply precisely the denominator receipts they need.
-/

namespace DraismaVargas.Count.W3FourCountBalance

open DraismaVargas.Infrastructure GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource FullDimensionalSource ThirdEquation
open W3FourClosure W3FourSourceCandidates W3FourStableGraph W3FourSurvival
open W3FourRegrownColumnSeam UnitWeightBalance
open W3FourMultiplicityBalance TrivalentWeight
open W3Nd2SourceCandidates (rightOf)

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

theorem stablePath_eq_sourceEdge {edge : data.SourceEdge}
    (hEdge : ¬IsDangling data edge)
    (hSource : ¬IsDangling data (data.sourceEdge edge.1.1 edge.1.2)) :
    NonDanglingEdge.stablePath ⟨edge, hEdge⟩ =
      NonDanglingEdge.stablePath ⟨data.sourceEdge edge.1.1 edge.1.2, hSource⟩ := by
  apply congrArg NonDanglingEdge.stablePath
  apply Subtype.ext
  exact (GluingDatum.sourceEdge_self data edge).symm

theorem rowDen_eq_incoming (grown : GrowProfile input)
    (receipts : Figure28Receipts data wall (ofGrowProfile grown))
    (hRows : receipts.rows = W3FourLimitRows.limitRowsOfInput grown)
    (row : Option target.edges) :
    rowDen receipts row =
      incomingRowDenominator data
        ((StablePathLabelling.ofCardEq data input.stablePath_card).row.symm row) := by
  unfold rowDen incomingRowDenominator oldEntry
  congr 1
  funext column
  rw [hRows]
  change W3FourStableGraph.columnSum
      ((W3FourLimitRows.limitRows (StablePathLabelling.ofCardEq data input.stablePath_card)
        grown).oldPath row) column = _
  exact W3FourLimitRows.limitRows_columnSum
    (StablePathLabelling.ofCardEq data input.stablePath_card) grown row column

theorem rowDen_grow (grown : GrowProfile input)
    (receipts : Figure28Receipts data wall (ofGrowProfile grown))
    (hRows : receipts.rows = W3FourLimitRows.limitRowsOfInput grown) :
    rowDen receipts receipts.rows.rowGrow =
      incomingRowDenominator data (W3FourIncomingDenominator.growEdge grown).stablePath := by
  rw [rowDen_eq_incoming grown receipts hRows]
  congr 1
  rw [hRows]
  simp [W3FourLimitRows.limitRowsOfInput, W3FourLimitRows.limitRows]
  exact stablePath_eq_sourceEdge _ _

theorem rowDen_other (grown : GrowProfile input)
    (receipts : Figure28Receipts data wall (ofGrowProfile grown))
    (hRows : receipts.rows = W3FourLimitRows.limitRowsOfInput grown) :
    rowDen receipts receipts.rows.rowOther =
      incomingRowDenominator data
        (NonDanglingEdge.stablePath ⟨data.sourceEdge grown.otherTarget grown.otherAnchor,
          (SelectedSurvival.ofGrowProfile grown).other_survives⟩) := by
  rw [rowDen_eq_incoming grown receipts hRows]
  congr 1
  rw [hRows]
  simp [W3FourLimitRows.limitRowsOfInput, W3FourLimitRows.limitRows]

theorem rowDen_largest (grown : GrowProfile input)
    (receipts : Figure28Receipts data wall (ofGrowProfile grown))
    (hRows : receipts.rows = W3FourLimitRows.limitRowsOfInput grown) :
    rowDen receipts receipts.rows.rowLargest =
      incomingRowDenominator data
        (NonDanglingEdge.stablePath ⟨data.sourceEdge grown.largestTarget grown.largestAnchor,
          (SelectedSurvival.ofGrowProfile grown).largest_survives⟩) := by
  rw [rowDen_eq_incoming grown receipts hRows]
  congr 1
  rw [hRows]
  simp [W3FourLimitRows.limitRowsOfInput, W3FourLimitRows.limitRows]

/-- Any actual Figure 28 orientation has an old wall occurrence on each side. -/
theorem leafCount_of_rightOf {base : GluingDatum target degree}
    (candidate : BalancedGlobal.Candidate target degree base wall)
    (isolated other : target.edges)
    (hIsolated : isolated ∈ incidentEdges wall) (hOther : other ∈ incidentEdges wall)
    (hNe : other ≠ isolated) (hRight : candidate.right = rightOf isolated) :
    leafCount (graph target wall candidate.right) = leafCount target := by
  have hIsolated' : isolated.fst.1 = wall ∨ isolated.fst.2 = wall :=
    (GluingContraction.mem_incidentEdges_iff wall isolated).mp hIsolated
  have hOther' : other.fst.1 = wall ∨ other.fst.2 = wall :=
    (GluingContraction.mem_incidentEdges_iff wall other).mp hOther
  apply leafCount_graph_candidate wall candidate
  · refine ⟨isolated, ?_⟩
    simp [wallEdgesAssigned, hIsolated', hRight, rightOf]
  · refine ⟨other, ?_⟩
    simp [wallEdgesAssigned, hOther', hRight, rightOf, hNe]

/-- Transport a full-dimensional presentation across a base equality and
literal heterogeneous identity of candidates. -/
noncomputable def fullDimensional_of_candidate_heq
    {firstBase secondBase : GluingDatum target degree}
    {first : BalancedGlobal.Candidate target degree firstBase wall}
    {second : BalancedGlobal.Candidate target degree secondBase wall}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hBase : firstBase = secondBase) (h : HEq first second)
    (fd : FullDimensionalSourcePresentation first.datum coordinate) :
    FullDimensionalSourcePresentation second.datum coordinate := by
  subst secondBase
  have hc : first = second := eq_of_heq h
  rw [← hc]
  exact fd

theorem leafCount_of_candidate_heq
    {firstBase secondBase : GluingDatum target degree}
    {first : BalancedGlobal.Candidate target degree firstBase wall}
    {second : BalancedGlobal.Candidate target degree secondBase wall}
    (hBase : firstBase = secondBase) (h : HEq first second)
    (hleaf : leafCount (graph target wall second.right) = leafCount target) :
    leafCount (graph target wall first.right) = leafCount target := by
  subst secondBase
  have hc : first = second := eq_of_heq h
  simpa [hc] using hleaf

/-- **Equation (2), on the actual Figure 28 family.** The witness
contains the four honest members and the balance holds from any one selected
full-dimensional member chart. -/
theorem exists_sum_signedMult_eq_zero
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed : TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (geometry : FourStarGeometry data wall)
      (certified : MemberCertificates data wall geometry),
      ∀ (incoming : Fin 4),
        FullDimensionalSourcePresentation
            (certified.receipts.candidate incoming).datum (Option target.edges) →
        ∑ position : Fin 4,
          signedMult (certified.receipts.receipts.presentation position) = 0 := by
  let first := growProfileFirst profile directions largest_index
  let second := growProfileSecond profile directions largest_index
  let grownFirst := first.withExtra first.extraSheet first.extraSheet_wall_rel
    first.extraSheet_separate
  let grownSecond := second.withExtra second.extraSheet second.extraSheet_wall_rel
    second.extraSheet_separate
  obtain ⟨certified, hRows, hBaseThree, hBaseFour, hThree, hFour,
      ⟨permOne, hFixOne, positionOne, hGeometryOne, hBaseOne, hOne⟩,
      ⟨permTwo, hFixTwo, positionTwo, hGeometryTwo, hBaseTwo, hTwo⟩⟩ :=
    exists_memberCertificates_withExtra_origins input.valid profile directions largest_index
      first.extraSheet first.extraSheet_wall_rel first.extraSheet_separate
      second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
      root hRoot hGrowFixed hLargestFixed hOtherMoved
  refine ⟨ofGrowProfile grownFirst, certified, ?_⟩
  intro incoming incomingFD
  let receipts := certified.receipts.receipts
  have fdAt (position : Fin 4) (hDet :
      (W3FourMultiplicityBalance.memberMatrix receipts position).det ≠ 0) :
      FullDimensionalSourcePresentation
        (certified.receipts.candidate position).datum (Option target.edges) := by
    exact W3FourStableIncidence.HonestFigure28Exit.presentationAt certified.receipts
      incoming position (certified.certificate incoming position) input.valid hConnected hGenus
      (certified.memberGenus incoming) (certified.memberGenus position) incomingFD hDet
  apply W3FourMultiplicityBalance.sum_signedMult_eq_zero_of_receipts receipts
  · intro position
    fin_cases position
    · exact leafCount_of_candidate_heq hBaseOne hOne (leafCount_of_rightOf positionOne.candidate
        positionOne.toFourStarGeometry.largestTarget positionOne.toFourStarGeometry.growTarget
        positionOne.toFourStarGeometry.largestTarget_mem
        positionOne.toFourStarGeometry.growTarget_mem
        positionOne.toFourStarGeometry.grow_ne_largest rfl)
    · exact leafCount_of_candidate_heq hBaseTwo hTwo (leafCount_of_rightOf positionTwo.candidate
        positionTwo.toFourStarGeometry.largestTarget positionTwo.toFourStarGeometry.growTarget
        positionTwo.toFourStarGeometry.largestTarget_mem
        positionTwo.toFourStarGeometry.growTarget_mem
        positionTwo.toFourStarGeometry.grow_ne_largest rfl)
    · exact leafCount_of_candidate_heq hBaseThree hThree
        (leafCount_of_rightOf grownFirst.growCandidate grownFirst.growTarget
        grownFirst.otherTarget grownFirst.growTarget_mem grownFirst.otherTarget_mem
        grownFirst.grow_target_ne_other.symm rfl)
    · exact leafCount_of_candidate_heq hBaseFour hFour
        (leafCount_of_rightOf grownSecond.growCandidate grownSecond.growTarget
        grownSecond.otherTarget grownSecond.growTarget_mem grownSecond.otherTarget_mem
        grownSecond.grow_target_ne_other.symm rfl)
  · intro hDet
    have fd := fdAt 0 hDet
    let fd' := fullDimensional_of_candidate_heq hBaseOne hOne fd
    constructor
    · rw [rowDen_grow grownFirst receipts hRows]
      change data.sourceEdgeIndex grownFirst.grow.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        grownFirst root hRoot permOne hFixOne hGrowFixed hLargestFixed hOtherMoved
        positionOne hGeometryOne fd'
      exact ⟨W3FourLimitRows.grow_survives grownFirst, stablePath_eq_sourceEdge _ _⟩
    constructor
    · rw [rowDen_other grownFirst receipts hRows]
      change data.sourceEdgeIndex grownFirst.other.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        grownFirst root hRoot permOne hFixOne hGrowFixed hLargestFixed hOtherMoved
        positionOne hGeometryOne fd'
      exact ⟨W3FourLimitRows.other_survives grownFirst, stablePath_eq_sourceEdge _ _⟩
    · rw [rowDen_largest grownFirst receipts hRows]
      change data.sourceEdgeIndex grownFirst.largest.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        grownFirst root hRoot permOne hFixOne hGrowFixed hLargestFixed hOtherMoved
        positionOne hGeometryOne fd'
      exact ⟨W3FourLimitRows.largest_survives grownFirst, stablePath_eq_sourceEdge _ _⟩
  · intro position hDet
    fin_cases position
    · have fd := fdAt 1 hDet
      let fd' := fullDimensional_of_candidate_heq hBaseTwo hTwo fd
      change rowDen receipts receipts.rows.rowLargest = indexLargest (ofGrowProfile grownFirst)
      rw [rowDen_largest grownFirst receipts hRows]
      change incomingRowDenominator data _ = data.sourceEdgeIndex grownFirst.largest.1
      exact W3FourReversedDenominator.incomingRowDenominator_positionTwo_swapped
        grownFirst root hRoot permTwo hFixTwo hGrowFixed hLargestFixed hOtherMoved
        positionTwo hGeometryTwo fd'
    · have fd := fdAt 2 hDet
      let fd' := fullDimensional_of_candidate_heq hBaseThree hThree fd
      change rowDen receipts receipts.rows.rowGrow = indexGrow (ofGrowProfile grownFirst)
      rw [rowDen_grow grownFirst receipts hRows]
      change incomingRowDenominator data _ = data.sourceEdgeIndex grownFirst.grow.1
      simpa only [W3FourIncomingDenominator.growEdge] using
        W3FourIncomingDenominator.incomingRowDenominator_grow_eq grownFirst fd'
    · have fd := fdAt 3 hDet
      let fd' := fullDimensional_of_candidate_heq hBaseFour hFour fd
      change rowDen receipts receipts.rows.rowOther = indexOther (ofGrowProfile grownFirst)
      rw [rowDen_other grownFirst receipts hRows]
      have hGrow : grownSecond.grow.1 = grownFirst.other.1 := by
        rfl
      have hTarget : grownSecond.growTarget = grownFirst.otherTarget :=
        congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hGrow
      have hAnchor : grownSecond.growAnchor = grownFirst.otherAnchor :=
        congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hGrow
      change incomingRowDenominator data _ = data.sourceEdgeIndex grownFirst.other.1
      have result := W3FourIncomingDenominator.incomingRowDenominator_grow_eq grownSecond fd'
      have hPath : NonDanglingEdge.stablePath
          ⟨data.sourceEdge grownFirst.otherTarget grownFirst.otherAnchor,
            (SelectedSurvival.ofGrowProfile grownFirst).other_survives⟩ =
          (W3FourIncomingDenominator.growEdge grownSecond).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg₂ data.sourceEdge hTarget.symm hAnchor.symm
      rw [hPath]
      exact result.trans (congrArg data.sourceEdgeIndex hGrow)

end DraismaVargas.Count.W3FourCountBalance
