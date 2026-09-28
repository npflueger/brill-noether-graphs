import DraismaVargas.LocalCases.M11IncomingPartitions
import DraismaVargas.LocalCases.IncomingW2TargetPlacement
import DraismaVargas.LocalCases.M11SourceCandidates
import DraismaVargas.LocalCases.FullDimensionalSource

/-!
# Incoming M11 selected-block cases

The selected two-sheet forest census is aligned here with the three actual
valency splits at the endpoints of the contracted target occurrence.  All
conclusions concern restrictions of literal incoming partitions to the
selected merged block; no representative functions are identified.
-/

namespace DraismaVargas.LocalCases.M11IncomingSelectedCases

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W2R1Target SecondEquation
open M11IncomingPartitions IncomingW2TargetPlacement
open FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-- Every retained wall direction is discrete on the selected two-sheet
block, expressed as the exact induced count for its original occurrence. -/
theorem external_blockCount_eq_two
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2) (label : Fin 2) :
    (incoming.edgePartition (unfoldEdge hc hab hOne (star.edge label))).blockCountWithin
        (mergedPartition incoming a b) block.1 = 2 := by
  have hRefines := M11SourceCandidates.exterior_refines_splitBlock profile hCard
    (star.edge label) (star.edge_mem_incidentEdges label)
  have hCount := SheetPartition.blockCountWithin_eq_blockCard_of_refines_splitBlock
    ((contractDatum incoming hc hab hOne).edgePartition (star.edge label))
    ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩)
    block.1 block.1 hRefines rfl
  rw [hCard] at hCount
  simpa only [contractDatum_edgePartition,
    contractDatum_vertexPartition_merge] using hCount

private theorem exists_left_label_of_both_divalent
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    ∃ label : Fin 2,
      IncomingTargetExpansion.right hc hab hOne (star.edge label) = false := by
  have hNe := right_star_ne_of_divalent hc hab hOne star hLeft hRight
  cases hZero : IncomingTargetExpansion.right hc hab hOne (star.edge 0) with
  | false => exact ⟨0, hZero⟩
  | true =>
      cases hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) with
      | false => exact ⟨1, hOneEdge⟩
      | true => exact False.elim (hNe (hZero.trans hOneEdge.symm))

private theorem exists_right_label_of_both_divalent
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    ∃ label : Fin 2,
      IncomingTargetExpansion.right hc hab hOne (star.edge label) = true := by
  have hNe := right_star_ne_of_divalent hc hab hOne star hLeft hRight
  cases hZero : IncomingTargetExpansion.right hc hab hOne (star.edge 0) with
  | true => exact ⟨0, hZero⟩
  | false =>
      cases hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) with
      | true => exact ⟨1, hOneEdge⟩
      | false => exact False.elim (hNe (hZero.trans hOneEdge.symm))

/-- At two divalent target endpoints, a joined selected left endpoint cannot
have two selected contracted-edge blocks: its one old wall direction already
has two selected blocks, forcing local ramification two while the entire
target change is only one. -/
theorem not_internal_two_of_left_joined_both_divalent
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (hLeftCount : (incoming.vertexPartition a).blockCountWithin
      (mergedPartition incoming a b) block.1 = 1) :
    (incoming.edgePartition contracted).blockCountWithin
      (mergedPartition incoming a b) block.1 ≠ 2 := by
  classical
  intro hInternalCount
  obtain ⟨label, hSide⟩ := exists_left_label_of_both_divalent
    hc hab hOne star hLeftDivalent hRightDivalent
  let external := unfoldEdge hc hab hOne (star.edge label)
  have hExternalAt : external ∈ GluingDatum.incidentEdges a := by
    exact (right_eq_false_iff_of_incident hc hab hOne (star.edge label)
      (star.edge_mem_incidentEdges label)).mp hSide
  have hExternalNe : external ≠ contracted :=
    unfoldEdge_ne_contracted hc hab hOne (star.edge label)
  have hIncidentPair : GluingDatum.incidentEdges a = {contracted, external} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact contracted_mem_incidentEdges_left hc
      · exact hExternalAt
    · rw [Finset.card_pair hExternalNe.symm, hLeftDivalent]
  let mergedBlock := selectedMergedBlock incoming hc hab hOne block
  have hSum := sum_localRamification_blocksWithin incoming a
    (mergedPartition incoming a b)
    (vertexPartition_refines_mergedPartition incoming a b) mergedBlock
  have hExternalCount : (incoming.edgePartition external).blockCountWithin
      (mergedPartition incoming a b) block.1 = 2 := by
    exact external_blockCount_eq_two incoming hc hab hOne profile hCard label
  have hMergedCard := selectedMergedBlock_card incoming hc hab hOne block hCard
  have hEndpointBlocks : (SheetPartition.blocksWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock).card = 1 := by
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b)]
    exact hLeftCount
  have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
      (mergedPartition incoming a b) mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hInternalCount
  have hExternalCount' : (incoming.edgePartition external).blockCountWithin
      (mergedPartition incoming a b) mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hExternalCount
  have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
  rw [hIncidentPair, Finset.sum_pair hExternalNe.symm,
    hInternalCount', hExternalCount',
    hEndpointBlocks, hMergedCard', Finset.card_pair hExternalNe.symm] at hSum
  have hBound := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun endpointBlock : (incoming.vertexPartition a).Blocks ↦
      incoming.localRamification a endpointBlock)
    (Finset.subset_univ (SheetPartition.blocksWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock))
    (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg a
      (fullDim.valid.2 a) endpointBlock)
  change _ ≤ incoming.targetChange a at hBound
  have hChange := fullDim.changeMinimal a
  unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hChange
  rw [hLeftDivalent] at hChange
  omega

/-- Right-endpoint version of
`not_internal_two_of_left_joined_both_divalent`. -/
theorem not_internal_two_of_right_joined_both_divalent
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (hRightCount : (incoming.vertexPartition b).blockCountWithin
      (mergedPartition incoming a b) block.1 = 1) :
    (incoming.edgePartition contracted).blockCountWithin
      (mergedPartition incoming a b) block.1 ≠ 2 := by
  classical
  intro hInternalCount
  obtain ⟨label, hSide⟩ := exists_right_label_of_both_divalent
    hc hab hOne star hLeftDivalent hRightDivalent
  let external := unfoldEdge hc hab hOne (star.edge label)
  have hExternalAt : external ∈ GluingDatum.incidentEdges b := by
    exact (right_eq_true_iff hc hab hOne (star.edge label)).mp hSide
  have hExternalNe : external ≠ contracted :=
    unfoldEdge_ne_contracted hc hab hOne (star.edge label)
  have hIncidentPair : GluingDatum.incidentEdges b = {contracted, external} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact contracted_mem_incidentEdges_right hc
      · exact hExternalAt
    · rw [Finset.card_pair hExternalNe.symm, hRightDivalent]
  let mergedBlock := selectedMergedBlock incoming hc hab hOne block
  have hSum := sum_localRamification_blocksWithin incoming b
    (mergedPartition incoming a b)
    (vertexPartition_refines_mergedPartition_right incoming a b) mergedBlock
  have hExternalCount : (incoming.edgePartition external).blockCountWithin
      (mergedPartition incoming a b) block.1 = 2 := by
    exact external_blockCount_eq_two incoming hc hab hOne profile hCard label
  have hMergedCard := selectedMergedBlock_card incoming hc hab hOne block hCard
  have hEndpointBlocks : (SheetPartition.blocksWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock).card = 1 := by
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b)]
    exact hRightCount
  have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
      (mergedPartition incoming a b) mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hInternalCount
  have hExternalCount' : (incoming.edgePartition external).blockCountWithin
      (mergedPartition incoming a b) mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hExternalCount
  have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
    simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
  rw [hIncidentPair, Finset.sum_pair hExternalNe.symm,
    hInternalCount', hExternalCount', hEndpointBlocks, hMergedCard',
    Finset.card_pair hExternalNe.symm] at hSum
  have hBound := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun endpointBlock : (incoming.vertexPartition b).Blocks ↦
      incoming.localRamification b endpointBlock)
    (Finset.subset_univ (SheetPartition.blocksWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock))
    (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg b
      (fullDim.valid.2 b) endpointBlock)
  change _ ≤ incoming.targetChange b at hBound
  have hChange := fullDim.changeMinimal b
  unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hChange
  rw [hRightDivalent] at hChange
  omega

/-- Exact selected-block census at the `(2,2)` target split: both endpoint
partitions and the contracted-occurrence partition join the two selected
sheets. -/
theorem selected_census_of_both_divalent
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2) :
    JoinedOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) block.1 ∧
      JoinedOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) block.1 ∧
      JoinedOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) block.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 := by
  rcases selected_blockCount_census incoming hc hab hOne hForest block hCard with
    hJoined | hRightSplit | hLeftSplit
  · have hLeftJoined := joinedOnBlock_of_blockCountWithin_eq_one
      (incoming.vertexPartition a) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition incoming a b) hJoined.1
    have hEdgeJoined := joinedOnBlock_of_blockCountWithin_eq_one
      (incoming.edgePartition contracted) (mergedPartition incoming a b) block.1
      (edgePartition_refines_mergedPartition incoming hc) hJoined.2.2
    have hRightJoined := joinedOnBlock_of_blockCountWithin_eq_one
      (incoming.vertexPartition b) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition_right incoming a b) hJoined.2.1
    exact ⟨hLeftJoined, hEdgeJoined, hRightJoined,
      hJoined.1, hJoined.2.2, hJoined.2.1⟩
  · exact False.elim
      ((not_internal_two_of_left_joined_both_divalent incoming hc hab hOne
        fullDim profile hCard hLeftDivalent hRightDivalent hRightSplit.1)
        hRightSplit.2.2)
  · exact False.elim
      ((not_internal_two_of_right_joined_both_divalent incoming hc hab hOne
        fullDim profile hCard hLeftDivalent hRightDivalent hLeftSplit.2.1)
        hLeftSplit.2.2)

private theorem right_trivalent_change_zero_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    (GluingDatum.incidentEdges b).card = 3 ∧ incoming.targetChange b = 0 := by
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid
      fullDim.changeMinimal star with hDivalent | hLeftLeaf | hRightLeaf
  · omega
  · exact ⟨hLeftLeaf.2.1, hLeftLeaf.2.2.2⟩
  · omega

private theorem left_trivalent_change_zero_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    (GluingDatum.incidentEdges a).card = 3 ∧ incoming.targetChange a = 0 := by
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid
      fullDim.changeMinimal star with hDivalent | hLeftLeaf | hRightLeaf
  · omega
  · omega
  · exact ⟨hRightLeaf.1, hRightLeaf.2.2.1⟩

/-- Exact selected-block census at the `(1,3)` target split.  The selected
leaf endpoint is joined; the contracted occurrence and the opposite
trivalent endpoint are discrete on the two selected sheets. -/
theorem selected_census_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    JoinedOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) block.1 ∧
      DiscreteOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) block.1 ∧
      DiscreteOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) block.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 := by
  classical
  obtain ⟨hRightTrivalent, hRightChange⟩ :=
    right_trivalent_change_zero_of_left_leaf incoming hc hab hOne fullDim star hLeaf
  have hMergedCard := selectedMergedBlock_card incoming hc hab hOne block hCard
  rcases selected_blockCount_census incoming hc hab hOne hForest block hCard with
    hAllJoined | hDesired | hWrongLeaf
  · let externalZero := unfoldEdge hc hab hOne (star.edge 0)
    let externalOne := unfoldEdge hc hab hOne (star.edge 1)
    have hZeroAt : externalZero ∈ GluingDatum.incidentEdges b := by
      exact (right_eq_true_iff hc hab hOne (star.edge 0)).mp
        (right_star_of_leaf_left hc hab hOne star hLeaf 0)
    have hOneAt : externalOne ∈ GluingDatum.incidentEdges b := by
      exact (right_eq_true_iff hc hab hOne (star.edge 1)).mp
        (right_star_of_leaf_left hc hab hOne star hLeaf 1)
    have hZeroNe : externalZero ≠ contracted :=
      unfoldEdge_ne_contracted hc hab hOne (star.edge 0)
    have hOneNe : externalOne ≠ contracted :=
      unfoldEdge_ne_contracted hc hab hOne (star.edge 1)
    have hZeroOne : externalZero ≠ externalOne := by
      intro hEqual
      have hSubtype : (foldEdgeEquiv hc hab hOne).symm (star.edge 0) =
          (foldEdgeEquiv hc hab hOne).symm (star.edge 1) := Subtype.ext hEqual
      have hLabels := star.edge_injective
        ((foldEdgeEquiv hc hab hOne).symm.injective hSubtype)
      exact (by decide : (0 : Fin 2) ≠ 1) hLabels
    have hContractedNotMem : contracted ∉
        ({externalZero, externalOne} : Finset target.edges) := by
      simp [hZeroNe.symm, hOneNe.symm]
    have hCardTriple : ({contracted, externalZero, externalOne} :
        Finset target.edges).card = 3 := by
      rw [Finset.card_insert_of_notMem hContractedNotMem,
        Finset.card_pair hZeroOne]
    have hIncidentTriple : GluingDatum.incidentEdges b =
        {contracted, externalZero, externalOne} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro edge hEdge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
        rcases hEdge with rfl | rfl | rfl
        · exact contracted_mem_incidentEdges_right hc
        · exact hZeroAt
        · exact hOneAt
      · rw [hRightTrivalent, hCardTriple]
    let mergedBlock := selectedMergedBlock incoming hc hab hOne block
    have hSum := sum_localRamification_blocksWithin incoming b
      (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b) mergedBlock
    have hZeroCount : (incoming.edgePartition externalZero).blockCountWithin
        (mergedPartition incoming a b) block.1 = 2 :=
      external_blockCount_eq_two incoming hc hab hOne profile hCard 0
    have hOneCount : (incoming.edgePartition externalOne).blockCountWithin
        (mergedPartition incoming a b) block.1 = 2 :=
      external_blockCount_eq_two incoming hc hab hOne profile hCard 1
    have hEndpointBlocks : (SheetPartition.blocksWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock).card = 1 := by
      rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b)
        (vertexPartition_refines_mergedPartition_right incoming a b)]
      exact hAllJoined.2.1
    have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 1 := by
      simpa only [mergedBlock, selectedMergedBlock] using hAllJoined.2.2
    have hZeroCount' : (incoming.edgePartition externalZero).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hZeroCount
    have hOneCount' : (incoming.edgePartition externalOne).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hOneCount
    have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
    rw [hIncidentTriple, Finset.sum_insert hContractedNotMem,
      Finset.sum_pair hZeroOne, hInternalCount', hZeroCount', hOneCount',
      hEndpointBlocks, hMergedCard', hCardTriple] at hSum
    have hBound := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun endpointBlock : (incoming.vertexPartition b).Blocks ↦
        incoming.localRamification b endpointBlock)
      (Finset.subset_univ (SheetPartition.blocksWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock))
      (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg b
        (fullDim.valid.2 b) endpointBlock)
    change _ ≤ incoming.targetChange b at hBound
    omega
  · have hLeftJoined := joinedOnBlock_of_blockCountWithin_eq_one
      (incoming.vertexPartition a) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition incoming a b) hDesired.1
    have hEdgeDiscrete := (joinedOnBlock_or_discreteOnBlock_of_card_two
      (incoming.edgePartition contracted) (mergedPartition incoming a b) block.1
      (edgePartition_refines_mergedPartition incoming hc) hMergedCard).resolve_left
      (fun hJoined ↦ by
        have hCount := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hJoined
        omega)
    have hRightDiscrete := (joinedOnBlock_or_discreteOnBlock_of_card_two
      (incoming.vertexPartition b) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition_right incoming a b) hMergedCard).resolve_left
      (fun hJoined ↦ by
        have hCount := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hJoined
        omega)
    exact ⟨hLeftJoined, hEdgeDiscrete, hRightDiscrete,
      hDesired.1, hDesired.2.2, hDesired.2.1⟩
  · let mergedBlock := selectedMergedBlock incoming hc hab hOne block
    have hLeftSum := sum_localRamification_blocksWithin incoming a
      (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b) mergedBlock
    have hIncidentSingleton : GluingDatum.incidentEdges a = {contracted} := by
      obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hLeaf
      have hContractedMem := contracted_mem_incidentEdges_left hc
      have hContracted : contracted = only := by
        rw [hOnly, Finset.mem_singleton] at hContractedMem
        exact hContractedMem
      simpa [hContracted] using hOnly
    have hEndpointBlocks : (SheetPartition.blocksWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock).card = 2 := by
      rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b)
        (vertexPartition_refines_mergedPartition incoming a b)]
      exact hWrongLeaf.1
    have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hWrongLeaf.2.2
    have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
    rw [hIncidentSingleton, Finset.sum_singleton, hInternalCount',
      hEndpointBlocks, hMergedCard', Finset.card_singleton] at hLeftSum
    have hAdd := localRamificationAt_contractDatum_merge incoming hc hab hOne
      hForest mergedBlock
    have hWallRamification : localRamificationAt
        (contractDatum incoming hc hab hOne) ⟨a, hab⟩ mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using
        (localRamificationAt_block (contractDatum incoming hc hab hOne)
          ⟨a, hab⟩ block).trans profile.ramification
    rw [hWallRamification] at hAdd
    have hRightBound := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun endpointBlock : (incoming.vertexPartition b).Blocks ↦
        incoming.localRamification b endpointBlock)
      (Finset.subset_univ (SheetPartition.blocksWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock))
      (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg b
        (fullDim.valid.2 b) endpointBlock)
    change _ ≤ incoming.targetChange b at hRightBound
    omega

/-- Exact selected-block census at the `(3,1)` target split, symmetric to
`selected_census_of_left_leaf`. -/
theorem selected_census_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    DiscreteOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) block.1 ∧
      DiscreteOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) block.1 ∧
      JoinedOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) block.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 := by
  classical
  obtain ⟨hLeftTrivalent, hLeftChange⟩ :=
    left_trivalent_change_zero_of_right_leaf incoming hc hab hOne fullDim star hLeaf
  have hMergedCard := selectedMergedBlock_card incoming hc hab hOne block hCard
  rcases selected_blockCount_census incoming hc hab hOne hForest block hCard with
    hAllJoined | hWrongLeaf | hDesired
  · let externalZero := unfoldEdge hc hab hOne (star.edge 0)
    let externalOne := unfoldEdge hc hab hOne (star.edge 1)
    have hZeroAt : externalZero ∈ GluingDatum.incidentEdges a := by
      exact (right_eq_false_iff_of_incident hc hab hOne (star.edge 0)
        (star.edge_mem_incidentEdges 0)).mp
          (right_star_of_leaf_right hc hab hOne star hLeaf 0)
    have hOneAt : externalOne ∈ GluingDatum.incidentEdges a := by
      exact (right_eq_false_iff_of_incident hc hab hOne (star.edge 1)
        (star.edge_mem_incidentEdges 1)).mp
          (right_star_of_leaf_right hc hab hOne star hLeaf 1)
    have hZeroNe : externalZero ≠ contracted :=
      unfoldEdge_ne_contracted hc hab hOne (star.edge 0)
    have hOneNe : externalOne ≠ contracted :=
      unfoldEdge_ne_contracted hc hab hOne (star.edge 1)
    have hZeroOne : externalZero ≠ externalOne := by
      intro hEqual
      have hSubtype : (foldEdgeEquiv hc hab hOne).symm (star.edge 0) =
          (foldEdgeEquiv hc hab hOne).symm (star.edge 1) := Subtype.ext hEqual
      have hLabels := star.edge_injective
        ((foldEdgeEquiv hc hab hOne).symm.injective hSubtype)
      exact (by decide : (0 : Fin 2) ≠ 1) hLabels
    have hContractedNotMem : contracted ∉
        ({externalZero, externalOne} : Finset target.edges) := by
      simp [hZeroNe.symm, hOneNe.symm]
    have hCardTriple : ({contracted, externalZero, externalOne} :
        Finset target.edges).card = 3 := by
      rw [Finset.card_insert_of_notMem hContractedNotMem,
        Finset.card_pair hZeroOne]
    have hIncidentTriple : GluingDatum.incidentEdges a =
        {contracted, externalZero, externalOne} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro edge hEdge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
        rcases hEdge with rfl | rfl | rfl
        · exact contracted_mem_incidentEdges_left hc
        · exact hZeroAt
        · exact hOneAt
      · rw [hLeftTrivalent, hCardTriple]
    let mergedBlock := selectedMergedBlock incoming hc hab hOne block
    have hSum := sum_localRamification_blocksWithin incoming a
      (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b) mergedBlock
    have hZeroCount : (incoming.edgePartition externalZero).blockCountWithin
        (mergedPartition incoming a b) block.1 = 2 :=
      external_blockCount_eq_two incoming hc hab hOne profile hCard 0
    have hOneCount : (incoming.edgePartition externalOne).blockCountWithin
        (mergedPartition incoming a b) block.1 = 2 :=
      external_blockCount_eq_two incoming hc hab hOne profile hCard 1
    have hEndpointBlocks : (SheetPartition.blocksWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock).card = 1 := by
      rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b)
        (vertexPartition_refines_mergedPartition incoming a b)]
      exact hAllJoined.1
    have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 1 := by
      simpa only [mergedBlock, selectedMergedBlock] using hAllJoined.2.2
    have hZeroCount' : (incoming.edgePartition externalZero).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hZeroCount
    have hOneCount' : (incoming.edgePartition externalOne).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hOneCount
    have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
    rw [hIncidentTriple, Finset.sum_insert hContractedNotMem,
      Finset.sum_pair hZeroOne, hInternalCount', hZeroCount', hOneCount',
      hEndpointBlocks, hMergedCard', hCardTriple] at hSum
    have hBound := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun endpointBlock : (incoming.vertexPartition a).Blocks ↦
        incoming.localRamification a endpointBlock)
      (Finset.subset_univ (SheetPartition.blocksWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock))
      (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg a
        (fullDim.valid.2 a) endpointBlock)
    change _ ≤ incoming.targetChange a at hBound
    omega
  · let mergedBlock := selectedMergedBlock incoming hc hab hOne block
    have hRightSum := sum_localRamification_blocksWithin incoming b
      (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b) mergedBlock
    have hIncidentSingleton : GluingDatum.incidentEdges b = {contracted} := by
      obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hLeaf
      have hContractedMem := contracted_mem_incidentEdges_right hc
      have hContracted : contracted = only := by
        rw [hOnly, Finset.mem_singleton] at hContractedMem
        exact hContractedMem
      simpa [hContracted] using hOnly
    have hEndpointBlocks : (SheetPartition.blocksWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b) mergedBlock).card = 2 := by
      rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
        (incoming.vertexPartition b) (mergedPartition incoming a b)
        (vertexPartition_refines_mergedPartition_right incoming a b)]
      exact hWrongLeaf.2.1
    have hInternalCount' : (incoming.edgePartition contracted).blockCountWithin
        (mergedPartition incoming a b) mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hWrongLeaf.2.2
    have hMergedCard' : (mergedPartition incoming a b).blockCard mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using hMergedCard
    rw [hIncidentSingleton, Finset.sum_singleton, hInternalCount',
      hEndpointBlocks, hMergedCard', Finset.card_singleton] at hRightSum
    have hAdd := localRamificationAt_contractDatum_merge incoming hc hab hOne
      hForest mergedBlock
    have hWallRamification : localRamificationAt
        (contractDatum incoming hc hab hOne) ⟨a, hab⟩ mergedBlock.1 = 2 := by
      simpa only [mergedBlock, selectedMergedBlock] using
        (localRamificationAt_block (contractDatum incoming hc hab hOne)
          ⟨a, hab⟩ block).trans profile.ramification
    rw [hWallRamification] at hAdd
    have hLeftBound := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun endpointBlock : (incoming.vertexPartition a).Blocks ↦
        incoming.localRamification a endpointBlock)
      (Finset.subset_univ (SheetPartition.blocksWithin
        (incoming.vertexPartition a) (mergedPartition incoming a b) mergedBlock))
      (fun endpointBlock _ _ ↦ incoming.localRamification_nonneg a
        (fullDim.valid.2 a) endpointBlock)
    change _ ≤ incoming.targetChange a at hLeftBound
    omega
  · have hLeftDiscrete := (joinedOnBlock_or_discreteOnBlock_of_card_two
      (incoming.vertexPartition a) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition incoming a b) hMergedCard).resolve_left
      (fun hJoined ↦ by
        have hCount := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hJoined
        omega)
    have hEdgeDiscrete := (joinedOnBlock_or_discreteOnBlock_of_card_two
      (incoming.edgePartition contracted) (mergedPartition incoming a b) block.1
      (edgePartition_refines_mergedPartition incoming hc) hMergedCard).resolve_left
      (fun hJoined ↦ by
        have hCount := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hJoined
        omega)
    have hRightJoined := joinedOnBlock_of_blockCountWithin_eq_one
      (incoming.vertexPartition b) (mergedPartition incoming a b) block.1
      (vertexPartition_refines_mergedPartition_right incoming a b) hDesired.2.1
    exact ⟨hLeftDiscrete, hEdgeDiscrete, hRightJoined,
      hDesired.1, hDesired.2.2, hDesired.2.1⟩

/-- The count-level selected census packaged against the actual three target
valency cases.  The three preceding theorems provide the corresponding
joined/discrete relation statements. -/
theorem selected_count_census_by_target
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2) :
    ((GluingDatum.incidentEdges a).card = 1 ∧
        (GluingDatum.incidentEdges b).card = 3 ∧
        (incoming.vertexPartition a).blockCountWithin
            (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.edgePartition contracted).blockCountWithin
            (mergedPartition incoming a b) block.1 = 2 ∧
        (incoming.vertexPartition b).blockCountWithin
            (mergedPartition incoming a b) block.1 = 2) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧
        (GluingDatum.incidentEdges b).card = 1 ∧
        (incoming.vertexPartition a).blockCountWithin
            (mergedPartition incoming a b) block.1 = 2 ∧
        (incoming.edgePartition contracted).blockCountWithin
            (mergedPartition incoming a b) block.1 = 2 ∧
        (incoming.vertexPartition b).blockCountWithin
            (mergedPartition incoming a b) block.1 = 1) ∨
      ((GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 2 ∧
        (incoming.vertexPartition a).blockCountWithin
            (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.edgePartition contracted).blockCountWithin
            (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.vertexPartition b).blockCountWithin
            (mergedPartition incoming a b) block.1 = 1) := by
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid
      fullDim.changeMinimal star with hDivalent | hLeftLeaf | hRightLeaf
  · have hCensus := selected_census_of_both_divalent incoming hc hab hOne
      fullDim hForest profile hCard hDivalent.1 hDivalent.2.1
    exact Or.inr (Or.inr ⟨hDivalent.1, hDivalent.2.1,
      hCensus.2.2.2.1, hCensus.2.2.2.2.1, hCensus.2.2.2.2.2⟩)
  · have hCensus := selected_census_of_left_leaf incoming hc hab hOne
      fullDim hForest profile hCard hLeftLeaf.1
    exact Or.inl ⟨hLeftLeaf.1, hLeftLeaf.2.1,
      hCensus.2.2.2.1, hCensus.2.2.2.2.1, hCensus.2.2.2.2.2⟩
  · have hCensus := selected_census_of_right_leaf incoming hc hab hOne
      fullDim hForest profile hCard hRightLeaf.2.1
    exact Or.inr (Or.inl ⟨hRightLeaf.1, hRightLeaf.2.1,
      hCensus.2.2.2.1, hCensus.2.2.2.2.1, hCensus.2.2.2.2.2⟩)

end DraismaVargas.LocalCases.M11IncomingSelectedCases
