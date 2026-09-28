import DraismaVargasCount.W2MkkIncomingDenominator
import DraismaVargas.LocalCases.W3FourRowDescent

/-!
# Incoming row denominators for Figure 28's reversed members

This file concerns the two reversed members of Draisma–Vargas Part I, Figure 28 (Case
`{w3-r1-nd3-t2-(a=k4)}`, Equation (2)).
The first reversed member only repeats old indices. The second changes the
largest index k₄ to k₄-1 at a terminal transition, forcing the incoming
largest-row denominator to equal k₄. The branch-swapped producers
below construct the selected survival census themselves; it is not a hypothesis
supplied by the caller.  These divisibility facts are used for the balance of
Equation (2) in `DraismaVargasCount.W3FourCountBalance` and for the star census in
`DraismaVargasCount.W3FourStarCensusProof`.
-/

namespace DraismaVargas.Count.W3FourReversedDenominator

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open ThirdEquation W3FourSourceCandidates W3FourSurvival LimitChainCore
open W3FourClosure W3FourDisjointness RowWalk TrivalentWeight
open ResolutionM11

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

theorem index_dvd_positionOne (position : W3FourClosure.PositionOne data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry) (hValid : data.Valid)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]; exact one_dvd _
  exact W2MkkIncomingDenominator.index_dvd_incomingRowDenominator_of_retained
    (W3FourRowDescent.PositionOne.rowData position survival hValid).toLiftData fd hEdge hOne

theorem index_dvd_positionTwo (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry) (hValid : data.Valid)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  by_cases hOne : data.sourceEdgeIndex edge = 1
  · rw [hOne]; exact one_dvd _
  exact W2MkkIncomingDenominator.index_dvd_incomingRowDenominator_of_retained
    (W3FourRowDescent.PositionTwo.rowData position survival hValid).toLiftData fd hEdge hOne

theorem positionTwo_new_index (position : W3FourClosure.PositionTwo data wall) :
    position.candidate.datum.sourceEdgeIndex
      (position.candidate.newSourceEdge position.growAnchor) + 1 =
    data.sourceEdgeIndex (data.sourceEdge position.largestTarget position.largestAnchor) := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, position.largest_index,
    ← position.index_sum]
  change ((position.toFourStarGeometry.reversedCandidate position.fine position.fine_refines
    position.grow_refines_fine position.other_refines_fine position.rightCounts).resolution
      ((data.vertexPartition wall).repr position.growAnchor)).newEdge.blockCard
        position.growAnchor + 1 = _
  rw [FourStarGeometry.reversedCandidate_newEdge _ _ _ _ _ _
    ((data.vertexPartition wall).rel_repr_right position.growAnchor)]
  exact position.fine_blockCard_growAnchor

theorem incomingRowDenominator_positionTwo (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry) (hValid : data.Valid)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨data.sourceEdge position.largestTarget position.largestAnchor,
        survival.largest_survives⟩) =
    data.sourceEdgeIndex (data.sourceEdge position.largestTarget position.largestAnchor) := by
  let edge := data.sourceEdge position.largestTarget position.largestAnchor
  let member := W3FourSurvival.PositionTwo.toReversedMember position
  have hOld := member.largest_survives_out survival hValid
  have hNew := W3FourSurvival.PositionTwo.new_grow_survives position survival hValid
  have hOldIndex : position.candidate.datum.sourceEdgeIndex
      (position.candidate.oldSourceEdge edge) = data.sourceEdgeIndex edge :=
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _
  have hOldRow : OnRow position.candidate.datum
      (NonDanglingEdge.stablePath ⟨position.candidate.oldSourceEdge edge, hOld⟩)
      (position.candidate.oldSourceEdge edge) := ⟨hOld, rfl⟩
  have hCalculus := OutgoingRowCalculus.rowCalculus_of_index_ne_one fd hOldRow
    (by
      rw [hOldIndex]
      have hNewPos := position.candidate.datum.sourceEdgeIndex_pos
        (position.candidate.newSourceEdge position.growAnchor)
      have hIndex := positionTwo_new_index position
      change data.sourceEdgeIndex
        (data.sourceEdge position.largestTarget position.largestAnchor) ≠ 1
      omega)
  have hNewRow : OnRow position.candidate.datum
      (NonDanglingEdge.stablePath ⟨position.candidate.oldSourceEdge edge, hOld⟩)
      (position.candidate.newSourceEdge position.growAnchor) :=
    ⟨hNew, W3FourSurvival.PositionTwo.new_grow_stablePath position survival hValid⟩
  have hNewIncident := newSourceEdge_incident_old
    (candidate := position.candidate) position.growAnchor
  have hOldIncident := member.largest_incident_old_of_wall_rel (sheet := position.growAnchor) rfl
  have hNe := oldSourceEdge_ne_newSourceEdge
    (candidate := position.candidate) edge position.growAnchor
  have hTransition := W2M1kTransitionSiting.transition_of_unequal_indices fd hCalculus.1
    (W3FourSurvival.PositionTwo.old_nonDanglingValency_eq_two position survival hValid)
    hNewRow hNewIncident hOld hOldIncident (Ne.symm hNe)
    (by
      change position.candidate.datum.sourceEdgeIndex
        (position.candidate.newSourceEdge position.growAnchor) ≠
        position.candidate.datum.sourceEdgeIndex (position.candidate.oldSourceEdge edge)
      rw [hOldIndex]
      have := positionTwo_new_index position
      change position.candidate.datum.sourceEdgeIndex
        (position.candidate.newSourceEdge position.growAnchor) ≠
        data.sourceEdgeIndex (data.sourceEdge position.largestTarget position.largestAnchor)
      omega)
  have hUpper := RowRegrowth.incomingRowDenominator_dvd_of_transport
    fd.danglingEdgeNoGlue fd.pathEnds hCalculus.1 hCalculus.2 hTransition
    hNew hNewIncident hOld hOldIncident hNe
    (W2M1kTransitionSiting.terminal_of_opposite_branch position.candidate
      position.growAnchor false true (by decide)
      (W3FourSurvival.PositionTwo.fresh_grow_nonDanglingValency_eq_three
        position survival hValid))
    hOldIndex
    (W2M1kRowTransport.transport
      (W3FourRowDescent.PositionTwo.rowData position survival hValid).toLiftData
      (NonDanglingEdge.stablePath ⟨edge, survival.largest_survives⟩) position.growAnchor)
  exact Nat.dvd_antisymm hUpper
    (index_dvd_positionTwo position survival hValid fd ⟨survival.largest_survives, rfl⟩)


/-- Compatible sheet relabelling preserves the rectangular row denominator. -/
theorem incomingRowDenominator_relabel (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (path : StablePath data) :
    incomingRowDenominator relabeling.apply
      (SheetRelabelStable.stablePathEquiv relabeling hConnected path) =
    incomingRowDenominator data path := by
  unfold incomingRowDenominator
  congr 1
  exact funext (SheetRelabelStable.matrix_map relabeling hConnected path)

/-- Literal occurrence transport into the branch-swapped row. -/
theorem onRow_relabel (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    OnRow relabeling.apply (SheetRelabelStable.stablePathEquiv relabeling hConnected path)
      (relabeling.sourceEdgeEquiv edge) := by
  have hSurvives : ¬ IsDangling relabeling.apply (relabeling.sourceEdgeEquiv edge) :=
    fun h ↦ hEdge.1 ((SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff
      relabeling hConnected edge).mp h)
  refine ⟨hSurvives, ?_⟩
  exact (SheetRelabelStable.stablePathEquiv_mk relabeling hConnected ⟨edge, hEdge.1⟩).symm.trans
    (congrArg (SheetRelabelStable.stablePathEquiv relabeling hConnected) hEdge.2)

section ActualSwap

variable (grown : GrowProfile input) (root : target.V) (hRoot : root ≠ wall)
  (permutation : Equiv.Perm (Fin degree))
  (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
  (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.growTarget = false)
  (hLargestFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.largestTarget = false)
  (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot grown.otherTarget = true)

/-- The first reversed member, after the branch swap, supplies all original-row lower
divisors.  The only hypothesis identifying the position is `hGeometry`, the geometry
returned by `W3FourClosure.exists_member_one`; the survival census and validity are
constructed here. -/
theorem index_dvd_positionOne_swapped
    (position : W3FourClosure.PositionOne
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall)
    (hGeometry : position.toFourStarGeometry =
      (ofGrowProfile grown).swap root hRoot permutation hFix
        hGrowFixed hLargestFixed hOtherMoved)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  let relabeling := branchSwapOfPerm data wall root hRoot permutation hFix
  have hSurvival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry := by
    rw [hGeometry]
    exact SelectedSurvival.swap (ofGrowProfile grown) root hRoot permutation hFix
      (SelectedSurvival.ofGrowProfile grown) input.valid.1 hGrowFixed hLargestFixed hOtherMoved
  have hValid := (branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix).valid input.valid
  have h := index_dvd_positionOne position hSurvival hValid fd
    (onRow_relabel relabeling input.valid.1 hEdge)
  rw [SheetRelabelStable.sourceEdgeIndex_map, incomingRowDenominator_relabel] at h
  exact h

/-- The second reversed member, after the branch swap, supplies all original-row lower
divisors. -/
theorem index_dvd_positionTwo_swapped
    (position : W3FourClosure.PositionTwo
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall)
    (hGeometry : position.toFourStarGeometry =
      (ofGrowProfile grown).swap root hRoot permutation hFix
        hGrowFixed hLargestFixed hOtherMoved)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  let relabeling := branchSwapOfPerm data wall root hRoot permutation hFix
  have hSurvival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry := by
    rw [hGeometry]
    exact SelectedSurvival.swap (ofGrowProfile grown) root hRoot permutation hFix
      (SelectedSurvival.ofGrowProfile grown) input.valid.1 hGrowFixed hLargestFixed hOtherMoved
  have hValid := (branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix).valid input.valid
  have h := index_dvd_positionTwo position hSurvival hValid fd
    (onRow_relabel relabeling input.valid.1 hEdge)
  rw [SheetRelabelStable.sourceEdgeIndex_map, incomingRowDenominator_relabel] at h
  exact h

/-- The second reversed member supplies the exact original largest-row
denominator k₄, after the branch swap. -/
theorem incomingRowDenominator_positionTwo_swapped
    (position : W3FourClosure.PositionTwo
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall)
    (hGeometry : position.toFourStarGeometry =
      (ofGrowProfile grown).swap root hRoot permutation hFix
        hGrowFixed hLargestFixed hOtherMoved)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation position.candidate.datum coordinate) :
    incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨data.sourceEdge grown.largestTarget grown.largestAnchor,
        (SelectedSurvival.ofGrowProfile grown).largest_survives⟩) =
      data.sourceEdgeIndex grown.largest.1 := by
  let relabeling := branchSwapOfPerm data wall root hRoot permutation hFix
  have hSurvival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry := by
    rw [hGeometry]
    exact SelectedSurvival.swap (ofGrowProfile grown) root hRoot permutation hFix
      (SelectedSurvival.ofGrowProfile grown) input.valid.1 hGrowFixed hLargestFixed hOtherMoved
  have hValid := (branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix).valid input.valid
  have h := incomingRowDenominator_positionTwo position hSurvival hValid fd
  have hTarget : position.largestTarget = grown.largestTarget :=
    congrArg FourStarGeometry.largestTarget hGeometry
  have hAnchor : position.largestAnchor = grown.largestAnchor :=
    congrArg FourStarGeometry.largestAnchor hGeometry
  have hEdge : relabeling.apply.sourceEdge position.largestTarget position.largestAnchor =
      relabeling.sourceEdgeEquiv (data.sourceEdge grown.largestTarget grown.largestAnchor) := by
    rw [hTarget, hAnchor]
    exact branchSwap_sourceEdge_of_fixed root hRoot permutation hFix
      grown.largestTarget hLargestFixed grown.largestAnchor
  have hRow : NonDanglingEdge.stablePath
      ⟨relabeling.apply.sourceEdge position.largestTarget position.largestAnchor,
        hSurvival.largest_survives⟩ =
      SheetRelabelStable.stablePathEquiv relabeling input.valid.1
        (NonDanglingEdge.stablePath ⟨data.sourceEdge grown.largestTarget grown.largestAnchor,
          (SelectedSurvival.ofGrowProfile grown).largest_survives⟩) := by
    apply Eq.trans _ (SheetRelabelStable.stablePathEquiv_mk relabeling input.valid.1
      ⟨data.sourceEdge grown.largestTarget grown.largestAnchor,
        (SelectedSurvival.ofGrowProfile grown).largest_survives⟩).symm
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext hEdge)
  rw [hRow, incomingRowDenominator_relabel, hEdge, SheetRelabelStable.sourceEdgeIndex_map] at h
  simpa only [GluingDatum.sourceEdge_self] using h

end ActualSwap


/-- The member M1 exists after a branch swap at `root`, with its original-row
divisibility facts.  The disjointness choice and branch gauge come from the Figure 28
construction `W3FourClosure.exists_member_one`, not from additional assumptions of the
caller. -/
theorem exists_positionOne_receipts (grown : GrowProfile input)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.growTarget = false)
    (hLargestFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.largestTarget = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot grown.otherTarget = true)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate] :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
      (position : W3FourClosure.PositionOne
        (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
      BranchGauge data wall root hRoot (branchSwapOfPerm data wall root hRoot permutation hFix) ∧
      position.toFourStarGeometry = (ofGrowProfile grown).swap root hRoot permutation hFix
        hGrowFixed hLargestFixed hOtherMoved ∧
      ∀ (_fd : FullDimensionalSourcePresentation position.candidate.datum coordinate)
        (path : StablePath data) (edge : data.SourceEdge),
        OnRow data path edge → data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  obtain ⟨permutation, hFix, position, hGauge, hGeometry, _, _, _, _⟩ :=
    W3FourClosure.exists_member_one (ofGrowProfile grown) root hRoot
      hGrowFixed hLargestFixed hOtherMoved
  refine ⟨permutation, hFix, position, hGauge, hGeometry, ?_⟩
  intro fd path edge hEdge
  exact index_dvd_positionOne_swapped grown root hRoot permutation hFix
    hGrowFixed hLargestFixed hOtherMoved position hGeometry fd hEdge

/-- The member M2 exists after a branch swap at `root`, with the sharp original
largest-row denominator and every retained-row lower divisor. -/
theorem exists_positionTwo_receipts (grown : GrowProfile input)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.growTarget = false)
    (hLargestFixed : TargetBranchRegion.edgeMoved wall root hRoot grown.largestTarget = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot grown.otherTarget = true)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate] :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
      (position : W3FourClosure.PositionTwo
        (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
      BranchGauge data wall root hRoot (branchSwapOfPerm data wall root hRoot permutation hFix) ∧
      position.toFourStarGeometry = (ofGrowProfile grown).swap root hRoot permutation hFix
        hGrowFixed hLargestFixed hOtherMoved ∧
      ∀ (_fd : FullDimensionalSourcePresentation position.candidate.datum coordinate),
        (∀ (path : StablePath data) (edge : data.SourceEdge), OnRow data path edge →
          data.sourceEdgeIndex edge ∣ incomingRowDenominator data path) ∧
        incomingRowDenominator data
          (NonDanglingEdge.stablePath ⟨data.sourceEdge grown.largestTarget grown.largestAnchor,
            (SelectedSurvival.ofGrowProfile grown).largest_survives⟩) =
          data.sourceEdgeIndex grown.largest.1 := by
  obtain ⟨permutation, hFix, position, hGauge, hGeometry, _, _, _⟩ :=
    W3FourClosure.exists_member_two (ofGrowProfile grown) root hRoot
      hGrowFixed hLargestFixed hOtherMoved
  refine ⟨permutation, hFix, position, hGauge, hGeometry, ?_⟩
  intro fd
  constructor
  · intro path edge hEdge
    exact index_dvd_positionTwo_swapped grown root hRoot permutation hFix
      hGrowFixed hLargestFixed hOtherMoved position hGeometry fd hEdge
  · exact incomingRowDenominator_positionTwo_swapped grown root hRoot permutation hFix
      hGrowFixed hLargestFixed hOtherMoved position hGeometry fd

end DraismaVargas.Count.W3FourReversedDenominator

