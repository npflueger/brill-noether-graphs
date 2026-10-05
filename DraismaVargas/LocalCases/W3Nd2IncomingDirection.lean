module

public import DraismaVargas.LocalCases.W3Nd2IncomingTargetPlacement
public import DraismaVargas.LocalCases.DivalentSourceLocal
public import DraismaVargas.LocalCases.WallDegeneration
public import DraismaVargas.LocalCases.M11IncomingTargetNormalization

@[expose] public section

/-!
# Source-facing direction of the incoming W3 nd2 contraction

The positive old block over the divalent endpoint supplies a surviving
occurrence in its unique retained exterior direction.  Forest additivity
locates that block, while the inherited dangling compatibility carries the
survivor into the contracted distinguished block.  Thus the isolated target
direction is one of the two named Figure 31 survivors, never the residual
third direction.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingDirection

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion IncomingW2TargetPlacement
open TargetExpansion M11IncomingCoordinates M11IncomingTargetNormalization
open W3Nd2SourceCandidates W3Nd2FineRefinement W3Nd2FineCandidates
open W3Nd2IncomingTargetPlacement

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

private theorem exists_mem_eq_one_of_sum_eq_one
    {α : Type*} [DecidableEq α] (set : Finset α) (value : α → ℤ)
    (hNonneg : ∀ point ∈ set, 0 ≤ value point)
    (hSum : set.sum value = 1) :
    ∃ point ∈ set, value point = 1 := by
  by_contra hNone
  push Not at hNone
  have hZero : ∀ point ∈ set, value point = 0 := by
    intro point hPoint
    have hLe : value point ≤ set.sum value :=
      Finset.single_le_sum hNonneg hPoint
    have hPointNonneg := hNonneg point hPoint
    have hNotOne := hNone point hPoint
    rw [hSum] at hLe
    omega
  have : set.sum value = 0 := Finset.sum_eq_zero hZero
  omega

/-- At a positive ramification-one source block over a divalent target, every
target direction carries a surviving incident source occurrence.  This is the
paper's local no-return calculation, proved directly from harmonicity. -/
theorem exists_survivor_over_direction
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (hConnected : data.Connected)
    {wall : target.V} (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1)
    (hDivalent : (GluingDatum.incidentEdges wall).card = 2)
    (targetEdge : target.edges)
    (hTarget : targetEdge ∈ GluingDatum.incidentEdges wall) :
    ∃ edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
      ¬ IsDangling data edge.1 ∧ edge.1.1.1 = targetEdge := by
  classical
  let surviving := survivors data block
  let vertex := WallBlock.sourceVertex data wall block
  have hNonzero : nonDanglingValency data vertex ≠ 0 :=
    W3R1SourceProfile.nonDanglingValency_ne_zero hNoGlue block hR
  have hTwo : 2 ≤ nonDanglingValency data vertex :=
    (nonDanglingValency_eq_zero_or_two_le data hConnected vertex).resolve_left hNonzero
  by_contra hNone
  push Not at hNone
  obtain ⟨first, second, hNe, hIncidentEq⟩ := Finset.card_eq_two.mp hDivalent
  have hTargetCases : targetEdge = first ∨ targetEdge = second := by
    simpa only [hIncidentEq, Finset.mem_insert, Finset.mem_singleton] using hTarget
  have hOther : ∃ otherTarget : target.edges,
      otherTarget ∈ GluingDatum.incidentEdges wall ∧
        ∀ edge ∈ surviving, edge.1.1.1 = otherTarget := by
    rcases hTargetCases with hFirst | hSecond
    · refine ⟨second, ?_, ?_⟩
      · rw [hIncidentEq]
        simp
      · intro edge hEdge
        have hAt := (incident_iff_target_mem_and_rel data edge.1 vertex).mp edge.2 |>.1
        change edge.1.1.1 ∈ GluingDatum.incidentEdges wall at hAt
        rw [hIncidentEq, Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hAt | hAt
        · exact False.elim (hNone edge
            ((mem_survivors data block edge).mp hEdge) (hAt.trans hFirst.symm))
        · exact hAt
    · refine ⟨first, ?_, ?_⟩
      · rw [hIncidentEq]
        simp
      · intro edge hEdge
        have hAt := (incident_iff_target_mem_and_rel data edge.1 vertex).mp edge.2 |>.1
        change edge.1.1.1 ∈ GluingDatum.incidentEdges wall at hAt
        rw [hIncidentEq, Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hAt | hAt
        · exact hAt
        · exact False.elim (hNone edge
            ((mem_survivors data block edge).mp hEdge) (hAt.trans hSecond.symm))
  obtain ⟨otherTarget, hOtherAt, hAllOther⟩ := hOther
  have hSum := sum_survivor_index hNoGlue block hR
  have hUpper := sum_index_le_of_same_target data vertex surviving otherTarget
    hOtherAt hAllOther
  have hUpper' : (∑ edge ∈ surviving,
      (data.sourceEdgeIndex edge.1 : ℤ)) ≤
      ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
    simpa only [vertex, WallBlock.sourceVertex, GluingDatum.sourceEndpoint,
      block.2] using hUpper
  have hLower : (nonDanglingValency data vertex : ℤ) ≤
      ∑ edge ∈ surviving, (data.sourceEdgeIndex edge.1 : ℤ) := by
    rw [← card_survivors data block]
    calc
      ((surviving.card : ℕ) : ℤ) =
          ∑ _edge ∈ surviving, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun edge _ ↦ by
        exact_mod_cast sourceEdgeIndex_pos data edge.1
  have hCardPos := (data.vertexPartition wall).blockCard_pos block.1
  change (∑ edge ∈ surviving, (data.sourceEdgeIndex edge.1 : ℤ)) =
    (nonDanglingValency data vertex : ℤ) +
      2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) - 3 at hSum
  omega

/-- Forest ramification additivity places the contracted distinguished unit
on an old block over the divalent endpoint; every block over the trivalent
endpoint is unramified because its target change is zero. -/
theorem exists_ramified_block_at_divalent
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    ((GluingDatum.incidentEdges a).card = 2 ∧
      ∃ block ∈ SheetPartition.blocksWithin (data.vertexPartition a)
          (mergedPartition data a b)
          ((mergedPartition data a b).toBlock input.distinguishedBlock.1),
        data.localRamification a block = 1) ∨
    ((GluingDatum.incidentEdges b).card = 2 ∧
      ∃ block ∈ SheetPartition.blocksWithin (data.vertexPartition b)
          (mergedPartition data a b)
          ((mergedPartition data a b).toBlock input.distinguishedBlock.1),
        data.localRamification b block = 1) := by
  classical
  let mergedBlock :=
    (mergedPartition data a b).toBlock input.distinguishedBlock.1
  let leftBlocks := SheetPartition.blocksWithin (data.vertexPartition a)
    (mergedPartition data a b) mergedBlock
  let rightBlocks := SheetPartition.blocksWithin (data.vertexPartition b)
    (mergedPartition data a b) mergedBlock
  have hAdd := localRamification_contractDatum_merge data hc hab hOne hForest
    input.distinguishedBlock
  rw [input.localRamification_distinguishedBlock] at hAdd
  rcases endpoint_valencies data hc hab hOne fullDim star with hLeft | hRight
  · left
    refine ⟨hLeft.1, ?_⟩
    have hRightZero : ∀ block : (data.vertexPartition b).Blocks,
        data.localRamification b block = 0 := fun block ↦
      localRamification_eq_zero_of_targetChange_eq_zero data fullDim.valid b
        hLeft.2.2.2 block
    have hRightSum : rightBlocks.sum (data.localRamification b) = 0 := by
      apply Finset.sum_eq_zero
      intro block _
      exact hRightZero block
    have hLeftSum : leftBlocks.sum (data.localRamification a) = 1 := by
      change 1 = leftBlocks.sum (data.localRamification a) +
          rightBlocks.sum (data.localRamification b) at hAdd
      rw [hRightSum, add_zero] at hAdd
      exact hAdd.symm
    have hNonneg : ∀ block ∈ leftBlocks,
        0 ≤ data.localRamification a block := fun block _ ↦
      data.localRamification_nonneg a (fullDim.valid.2 a) block
    simpa only [leftBlocks, mergedBlock] using
      (exists_mem_eq_one_of_sum_eq_one leftBlocks
        (data.localRamification a) hNonneg hLeftSum)
  · right
    refine ⟨hRight.2.1, ?_⟩
    have hLeftZero : ∀ block : (data.vertexPartition a).Blocks,
        data.localRamification a block = 0 := fun block ↦
      localRamification_eq_zero_of_targetChange_eq_zero data fullDim.valid a
        hRight.2.2.1 block
    have hLeftSum : leftBlocks.sum (data.localRamification a) = 0 := by
      apply Finset.sum_eq_zero
      intro block _
      exact hLeftZero block
    have hRightSum : rightBlocks.sum (data.localRamification b) = 1 := by
      change 1 = leftBlocks.sum (data.localRamification a) +
          rightBlocks.sum (data.localRamification b) at hAdd
      rw [hLeftSum, zero_add] at hAdd
      exact hAdd.symm
    have hNonneg : ∀ block ∈ rightBlocks,
        0 ≤ data.localRamification b block := fun block _ ↦
      data.localRamification_nonneg b (fullDim.valid.2 b) block
    simpa only [rightBlocks, mergedBlock] using
      (exists_mem_eq_one_of_sum_eq_one rightBlocks
        (data.localRamification b) hNonneg hRightSum)

/-- An old left-endpoint block lying in a merged wall block maps to that
literal contracted source vertex. -/
theorem sourceVertexMap_left_eq_wallBlock
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (wallBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (block : (data.vertexPartition a).Blocks)
    (hBlock : block ∈ SheetPartition.blocksWithin (data.vertexPartition a)
      (mergedPartition data a b)
      ((mergedPartition data a b).toBlock wallBlock.1)) :
    sourceVertexMap data hc hab hOne
        (WallBlock.sourceVertex data a block) =
      WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ wallBlock := by
  have hMap : sourceVertexMap data hc hab hOne (data.sourceEndpoint a block.1) =
      (contractDatum data hc hab hOne).sourceEndpoint
        (fold target hab a) block.1 :=
    (sourceEndpoint_repr data hc hab hOne a block.1).symm
  rw [show WallBlock.sourceVertex data a block = data.sourceEndpoint a block.1 from rfl,
    hMap, GraphContraction.fold_a]
  apply ((contractDatum data hc hab hOne).sourceEndpoint_eq_iff
    ⟨a, hab⟩ block.1 _).mpr
  refine ⟨rfl, ?_⟩
  rw [contractDatum_vertexPartition_merge]
  have hCoarse := congrArg Subtype.val
    ((SheetPartition.mem_blocksWithin _ _ _ _).mp hBlock)
  change (mergedPartition data a b).repr block.1 =
    (mergedPartition data a b).repr wallBlock.1 at hCoarse
  have hSourceSheet :
    (WallBlock.sourceVertex (contractDatum data hc hab hOne)
        ⟨a, hab⟩ wallBlock).1.2 =
        (mergedPartition data a b).repr wallBlock.1 := by
    change (contractVertexPartition data a b ⟨a, hab⟩).repr wallBlock.1 = _
    rw [contractVertexPartition_merge]
    rfl
  unfold SheetPartition.Rel
  rw [hSourceSheet]
  exact hCoarse.trans ((mergedPartition data a b).repr_idem wallBlock.1).symm

/-- Right-endpoint version of `sourceVertexMap_left_eq_wallBlock`. -/
theorem sourceVertexMap_right_eq_wallBlock
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (wallBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (block : (data.vertexPartition b).Blocks)
    (hBlock : block ∈ SheetPartition.blocksWithin (data.vertexPartition b)
      (mergedPartition data a b)
      ((mergedPartition data a b).toBlock wallBlock.1)) :
    sourceVertexMap data hc hab hOne
        (WallBlock.sourceVertex data b block) =
      WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ wallBlock := by
  have hMap : sourceVertexMap data hc hab hOne (data.sourceEndpoint b block.1) =
      (contractDatum data hc hab hOne).sourceEndpoint
        (fold target hab b) block.1 :=
    (sourceEndpoint_repr data hc hab hOne b block.1).symm
  rw [show WallBlock.sourceVertex data b block = data.sourceEndpoint b block.1 from rfl,
    hMap, GraphContraction.fold_self]
  apply ((contractDatum data hc hab hOne).sourceEndpoint_eq_iff
    ⟨a, hab⟩ block.1 _).mpr
  refine ⟨rfl, ?_⟩
  rw [contractDatum_vertexPartition_merge]
  have hCoarse := congrArg Subtype.val
    ((SheetPartition.mem_blocksWithin _ _ _ _).mp hBlock)
  change (mergedPartition data a b).repr block.1 =
    (mergedPartition data a b).repr wallBlock.1 at hCoarse
  have hSourceSheet :
    (WallBlock.sourceVertex (contractDatum data hc hab hOne)
        ⟨a, hab⟩ wallBlock).1.2 =
        (mergedPartition data a b).repr wallBlock.1 := by
    change (contractVertexPartition data a b ⟨a, hab⟩).repr wallBlock.1 = _
    rw [contractVertexPartition_merge]
    rfl
  unfold SheetPartition.Rel
  rw [hSourceSheet]
  exact hCoarse.trans ((mergedPartition data a b).repr_idem wallBlock.1).symm

/-- The old divalent endpoint forces its unique retained target direction to
be one of the two actual surviving directions of the contracted nd2 profile.
No no-return or side assignment is assumed: the endpoint is found by the
target census, and survival is transported by the inherited contraction
compatibility receipt. -/
theorem divalentOccurrence_eq_small_or_large
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) :
    divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile ∨
      divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile := by
  classical
  let isolated := divalentOccurrence data hc hab hOne fullDim star
  let wallData := contractDatum data hc hab hOne
  have hIsolated := divalentOccurrence_spec data hc hab hOne fullDim star
  have hEndpointSum := (endpoints_of_threeStar data hc hab hOne fullDim.valid
    fullDim.changeMinimal star).1
  have hMapped : ∃ edge : IncidentSourceEdge wallData
      (WallBlock.sourceVertex wallData ⟨a, hab⟩ input.distinguishedBlock),
      ¬ IsDangling wallData edge.1 ∧ edge.1.1.1 = isolated := by
    rcases exists_ramified_block_at_divalent data hc hab hOne fullDim hForest
      star input with hLeft | hRight
    · obtain ⟨block, hBlock, hRamification⟩ := hLeft.2
      have hSide : IncomingTargetExpansion.right hc hab hOne isolated = false := by
        rcases hIsolated.2 with hAtLeft | hAtRight
        · simpa only [isolated] using hAtLeft.2
        · omega
      have hAt : unfoldEdge hc hab hOne isolated ∈
          GluingDatum.incidentEdges a :=
        (right_eq_false_iff_of_incident hc hab hOne isolated hIsolated.1).mp hSide
      obtain ⟨oldEdge, hSurvives, hTarget⟩ :=
        exists_survivor_over_direction data fullDim.danglingEdgeNoGlue
          fullDim.connected block hRamification hLeft.1
          (unfoldEdge hc hab hOne isolated) hAt
      have hAway : oldEdge.1.1.1 ≠ contracted := by
        intro hEq
        apply unfoldEdge_ne_contracted hc hab hOne isolated
        exact hTarget.symm.trans hEq
      let oldAway : {edge : data.SourceEdge // edge.1.1 ≠ contracted} :=
        ⟨oldEdge.1, hAway⟩
      let oldTargetAway : {edge : target.edges // edge ≠ contracted} :=
        ⟨oldEdge.1.1.1, hAway⟩
      let mapped := sourceEdgeMap data hc hab hOne oldAway
      have hMappedTarget : mapped.1.1 = isolated := by
        have hTargetAway : oldTargetAway =
            ⟨unfoldEdge hc hab hOne isolated,
              unfoldEdge_ne_contracted hc hab hOne isolated⟩ := by
          apply Subtype.ext
          exact hTarget
        change foldEdge hc hab hOne oldTargetAway = isolated
        rw [hTargetAway, foldEdge_unfoldEdge]
      have hMappedSurvives : ¬ IsDangling wallData mapped := by
        intro hDangling
        exact hSurvives (hCompat.2 oldAway hDangling)
      have hMappedIncident := incident_sourceEdgeMap data hc hab hOne oldAway oldEdge.2
      rw [sourceVertexMap_left_eq_wallBlock data hc hab hOne
        input.distinguishedBlock block hBlock] at hMappedIncident
      refine ⟨⟨mapped, hMappedIncident⟩, hMappedSurvives, ?_⟩
      simpa only [isolated] using hMappedTarget
    · obtain ⟨block, hBlock, hRamification⟩ := hRight.2
      have hSide : IncomingTargetExpansion.right hc hab hOne isolated = true := by
        rcases hIsolated.2 with hAtLeft | hAtRight
        · omega
        · simpa only [isolated] using hAtRight.2
      have hAt : unfoldEdge hc hab hOne isolated ∈
          GluingDatum.incidentEdges b :=
        (right_eq_true_iff hc hab hOne isolated).mp hSide
      obtain ⟨oldEdge, hSurvives, hTarget⟩ :=
        exists_survivor_over_direction data fullDim.danglingEdgeNoGlue
          fullDim.connected block hRamification hRight.1
          (unfoldEdge hc hab hOne isolated) hAt
      have hAway : oldEdge.1.1.1 ≠ contracted := by
        intro hEq
        apply unfoldEdge_ne_contracted hc hab hOne isolated
        exact hTarget.symm.trans hEq
      let oldAway : {edge : data.SourceEdge // edge.1.1 ≠ contracted} :=
        ⟨oldEdge.1, hAway⟩
      let oldTargetAway : {edge : target.edges // edge ≠ contracted} :=
        ⟨oldEdge.1.1.1, hAway⟩
      let mapped := sourceEdgeMap data hc hab hOne oldAway
      have hMappedTarget : mapped.1.1 = isolated := by
        have hTargetAway : oldTargetAway =
            ⟨unfoldEdge hc hab hOne isolated,
              unfoldEdge_ne_contracted hc hab hOne isolated⟩ := by
          apply Subtype.ext
          exact hTarget
        change foldEdge hc hab hOne oldTargetAway = isolated
        rw [hTargetAway, foldEdge_unfoldEdge]
      have hMappedSurvives : ¬ IsDangling wallData mapped := by
        intro hDangling
        exact hSurvives (hCompat.2 oldAway hDangling)
      have hMappedIncident := incident_sourceEdgeMap data hc hab hOne oldAway oldEdge.2
      rw [sourceVertexMap_right_eq_wallBlock data hc hab hOne
        input.distinguishedBlock block hBlock] at hMappedIncident
      refine ⟨⟨mapped, hMappedIncident⟩, hMappedSurvives, ?_⟩
      simpa only [isolated] using hMappedTarget
  obtain ⟨mapped, hSurvives, hTarget⟩ := hMapped
  have hMember : mapped ∈ survivors wallData input.distinguishedBlock :=
    (mem_survivors wallData input.distinguishedBlock mapped).mpr hSurvives
  rw [profile.surviving] at hMember
  rcases Finset.mem_insert.mp hMember with hSmall | hLarge
  · left
    have hTargetSmall := congrArg
      (fun edge : IncidentSourceEdge wallData
        (WallBlock.sourceVertex wallData ⟨a, hab⟩ input.distinguishedBlock) ↦
          edge.1.1.1) hSmall
    exact hTarget.symm.trans hTargetSmall
  · right
    have hTargetLarge := congrArg
      (fun edge : IncidentSourceEdge wallData
        (WallBlock.sourceVertex wallData ⟨a, hab⟩ input.distinguishedBlock) ↦
          edge.1.1.1) (Finset.mem_singleton.mp hLarge)
    exact hTarget.symm.trans hTargetLarge

/-- Agreement, up to exchanging the two restored endpoints, with a prescribed
side predicate on the contracted wall star. -/
def Placement
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (side : (contract target hab hOne).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
    IncomingTargetExpansion.right hc hab hOne edge = side edge) ∨
  (∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
    IncomingTargetExpansion.right hc hab hOne edge = !(side edge))

/-- If the isolated direction is SMALL, the actual incoming target placement
is the target of the source-derived coarse Figure 31 candidate. -/
theorem coarse_placement_of_eq_small
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hSmall : divalentOccurrence data hc hab hOne fullDim star =
      smallTarget input profile) :
    Placement hc hab hOne (coarseCandidate input profile).right := by
  change Placement hc hab hOne (rightOf (smallTarget input profile))
  have hPlacement := divalentOccurrence_placement data hc hab hOne fullDim star
  simpa only [Placement, hSmall] using hPlacement

/-- If the isolated direction is LARGE, the actual incoming target placement
is the target of the oppositely oriented fine Figure 31 candidate. -/
theorem fine_placement_of_eq_large
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hLarge : divalentOccurrence data hc hab hOne fullDim star =
      largeTarget input profile) :
    Placement hc hab hOne (fineCandidate input profile).right := by
  change Placement hc hab hOne (rightOf (largeTarget input profile))
  have hPlacement := divalentOccurrence_placement data hc hab hOne fullDim star
  simpa only [Placement, hLarge] using hPlacement

/-- The literal target isomorphism to the actual coarse candidate. -/
noncomputable def coarseTargetIso
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hSmall : divalentOccurrence data hc hab hOne fullDim star =
      smallTarget input profile) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩
        (coarseCandidate input profile).right) :=
  incomingIso hc hab hOne (coarseCandidate input profile).right
    (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)

/-- Every literal incoming Option occurrence, including the contracted
occurrence `none`, is carried to the corresponding coarse-candidate column. -/
theorem coarseTargetIso_occurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hSmall : divalentOccurrence data hc hab hOne fullDim star =
      smallTarget input profile)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv
        (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
        (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (coarseCandidate input profile).right column := by
  exact incomingIso_occurrence hc hab hOne (coarseCandidate input profile).right
    (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)
    fullDim.targetConnected fullDim.targetGenus column

/-- The literal target isomorphism to the actual fine candidate. -/
noncomputable def fineTargetIso
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hLarge : divalentOccurrence data hc hab hOne fullDim star =
      largeTarget input profile) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩
        (fineCandidate input profile).right) :=
  incomingIso hc hab hOne (fineCandidate input profile).right
    (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)

/-- Every literal incoming Option occurrence, including the contracted
occurrence `none`, is carried to the corresponding fine-candidate column. -/
theorem fineTargetIso_occurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hLarge : divalentOccurrence data hc hab hOne fullDim star =
      largeTarget input profile)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv
        (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
        (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (fineCandidate input profile).right column := by
  exact incomingIso_occurrence hc hab hOne (fineCandidate input profile).right
    (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)
    fullDim.targetConnected fullDim.targetGenus column

/-- The source-derived SMALL/LARGE alternative packages the corresponding
actual target normalization, with the literal column formula for every
retained (`some`) and restored (`none`) occurrence. -/
theorem exists_coarse_or_fine_normalization
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) :
    (∃ hSmall : divalentOccurrence data hc hab hOne fullDim star =
        smallTarget input profile,
      ∀ column : Option (contract target hab hOne).edges,
        GluingTransport.edgeEquiv
            (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
            (incomingColumnEquiv hc hab hOne column) =
          occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
            (coarseCandidate input profile).right column) ∨
    (∃ hLarge : divalentOccurrence data hc hab hOne fullDim star =
        largeTarget input profile,
      ∀ column : Option (contract target hab hOne).edges,
        GluingTransport.edgeEquiv
            (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
            (incomingColumnEquiv hc hab hOne column) =
          occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
            (fineCandidate input profile).right column) := by
  rcases divalentOccurrence_eq_small_or_large data hc hab hOne fullDim hForest
      hCompat star input profile with hSmall | hLarge
  · left
    exact ⟨hSmall, coarseTargetIso_occurrence data hc hab hOne fullDim star
      input profile hSmall⟩
  · right
    exact ⟨hLarge, fineTargetIso_occurrence data hc hab hOne fullDim star
      input profile hLarge⟩

end DraismaVargas.LocalCases.W3Nd2IncomingDirection
