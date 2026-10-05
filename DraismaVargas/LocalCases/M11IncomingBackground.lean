module

public import DraismaVargas.LocalCases.M11IncomingPartitions
public import DraismaVargas.LocalCases.StablePathContraction
public import DraismaVargas.LocalCases.W2RankObstructions
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# Incoming M11 background blocks at an asymmetric target split

For an r0 wall block, ramification additivity makes every incoming endpoint
block unramified.  If one old target endpoint is a leaf, the leaf dichotomy
forces that endpoint partition, and hence the contracted-edge partition, to
be discrete on the whole merged block.  The forest equation then forces the
opposite endpoint partition to be joined.
-/

namespace DraismaVargas.LocalCases.M11IncomingBackground

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource W2R1Target SecondEquation
open FullDimensionalSource M11IncomingPartitions

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

theorem blockCountWithin_eq_blockCard_of_discreteOnBlock
    {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d)
    (hDiscrete : DiscreteOnBlock fine coarse root) :
    fine.blockCountWithin coarse root = coarse.blockCard root := by
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  apply Finset.card_image_of_injOn
  intro first hFirst second hSecond hRepr
  have hFirstCoarse : coarse.Rel root first :=
    (coarse.mem_block_iff root first).mp hFirst
  have hSecondCoarse : coarse.Rel root second :=
    (coarse.mem_block_iff root second).mp hSecond
  exact (hDiscrete first second hFirstCoarse hSecondCoarse).mp
    ((fine.rel_iff first second).mpr hRepr)

/-- Full relation- and count-level census for a background block when the
left incoming target endpoint is a leaf. -/
theorem background_census_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {selected : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star selected)
    (background : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hBackground : background ≠ selected)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    DiscreteOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) background.1 ∧
      DiscreteOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) background.1 ∧
      JoinedOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) background.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) background.1 =
        (mergedPartition incoming a b).blockCard background.1 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) background.1 =
        (mergedPartition incoming a b).blockCard background.1 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) background.1 = 1 := by
  let wallData := contractDatum incoming hc hab hOne
  let wall : (contract target hab hOne).V := ⟨a, hab⟩
  have hBackgroundZero : wallData.localRamification wall background = 0 :=
    W2RankObstructions.other_localRamification_eq_zero input selected
      profile.ramification background hBackground
  have hLeftDiscrete : DiscreteOnBlock (incoming.vertexPartition a)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst _hSecond
    constructor
    · intro hTogether
      let root : Fin degree := background.1
      have hWallRel : (wallData.vertexPartition wall).Rel background.1 first := by
        change (wallData.vertexPartition wall).Rel root first
        have hPartition : wallData.vertexPartition wall = mergedPartition incoming a b := by
          dsimp only [wallData, wall]
          exact contractDatum_vertexPartition_merge incoming hc hab hOne
        rw [hPartition]
        exact hFirst
      have hZeroAtRoot : localRamificationAt wallData wall background.1 = 0 := by
        exact (localRamificationAt_block wallData wall background).trans hBackgroundZero
      have hZeroAtFirst : localRamificationAt wallData wall first = 0 :=
        (localRamificationAt_congr wallData wall hWallRel).symm.trans hZeroAtRoot
      have hEndpointZero := (StablePathContraction.endpoint_localRamification_eq_zero
        incoming hc hab hOne fullDim.valid hForest first hZeroAtFirst).1
      rcases StableLocalProperties.leaf_block_dichotomy incoming fullDim.valid
          fullDim.noDanglingTargetFibres a hLeaf (fullDim.changeMinimal a)
          ((incoming.vertexPartition a).toBlock first) with hUnit | hRamified
      · have hFirstCard : (incoming.vertexPartition a).blockCard first = 1 := by
          exact ((incoming.vertexPartition a).blockCard_congr
            ((incoming.vertexPartition a).rel_repr_right first)).trans hUnit.2.1
        have hSecondMem : second ∈ (incoming.vertexPartition a).block first :=
          ((incoming.vertexPartition a).mem_block_iff first second).mpr hTogether
        rw [(incoming.vertexPartition a).block_eq_singleton_of_blockCard_eq_one
          first hFirstCard, Finset.mem_singleton] at hSecondMem
        exact hSecondMem.symm
      · rw [hEndpointZero] at hRamified
        omega
    · rintro rfl
      rfl
  have hEdgeDiscrete : DiscreteOnBlock (incoming.edgePartition contracted)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst hSecond
    constructor
    · intro hTogether
      have hEndpointRel :=
        (refines_of_mem_incidentEdges_local incoming
          (contracted_mem_incidentEdges_left hc)).rel hTogether
      exact (hLeftDiscrete first second hFirst hSecond).mp hEndpointRel
    · rintro rfl
      rfl
  have hLeftCount := blockCountWithin_eq_blockCard_of_discreteOnBlock
    (incoming.vertexPartition a) (mergedPartition incoming a b) background.1 hLeftDiscrete
  have hEdgeCount := blockCountWithin_eq_blockCard_of_discreteOnBlock
    (incoming.edgePartition contracted) (mergedPartition incoming a b) background.1 hEdgeDiscrete
  let mergedBlock := selectedMergedBlock incoming hc hab hOne background
  have hTree := hForest mergedBlock
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.edgePartition contracted) (mergedPartition incoming a b)
      (edgePartition_refines_mergedPartition incoming hc),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b)] at hTree
  dsimp [mergedBlock, selectedMergedBlock] at hTree
  have hRightCount : (incoming.vertexPartition b).blockCountWithin
      (mergedPartition incoming a b) background.1 = 1 := by omega
  have hRightJoined := joinedOnBlock_of_blockCountWithin_eq_one
    (incoming.vertexPartition b) (mergedPartition incoming a b) background.1
    (vertexPartition_refines_mergedPartition_right incoming a b) hRightCount
  exact ⟨hLeftDiscrete, hEdgeDiscrete, hRightJoined,
    hLeftCount, hEdgeCount, hRightCount⟩

/-- Symmetric asymmetric-target census when the right incoming endpoint is
the leaf. -/
theorem background_census_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {selected : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star selected)
    (background : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hBackground : background ≠ selected)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    JoinedOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) background.1 ∧
      DiscreteOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) background.1 ∧
      DiscreteOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) background.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) background.1 = 1 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) background.1 =
        (mergedPartition incoming a b).blockCard background.1 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) background.1 =
        (mergedPartition incoming a b).blockCard background.1 := by
  let wallData := contractDatum incoming hc hab hOne
  let wall : (contract target hab hOne).V := ⟨a, hab⟩
  have hBackgroundZero : wallData.localRamification wall background = 0 :=
    W2RankObstructions.other_localRamification_eq_zero input selected
      profile.ramification background hBackground
  have hRightDiscrete : DiscreteOnBlock (incoming.vertexPartition b)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst _hSecond
    constructor
    · intro hTogether
      let root : Fin degree := background.1
      have hWallRel : (wallData.vertexPartition wall).Rel background.1 first := by
        change (wallData.vertexPartition wall).Rel root first
        have hPartition : wallData.vertexPartition wall = mergedPartition incoming a b := by
          dsimp only [wallData, wall]
          exact contractDatum_vertexPartition_merge incoming hc hab hOne
        rw [hPartition]
        exact hFirst
      have hZeroAtRoot : localRamificationAt wallData wall background.1 = 0 :=
        (localRamificationAt_block wallData wall background).trans hBackgroundZero
      have hZeroAtFirst : localRamificationAt wallData wall first = 0 :=
        (localRamificationAt_congr wallData wall hWallRel).symm.trans hZeroAtRoot
      have hEndpointZero := (StablePathContraction.endpoint_localRamification_eq_zero
        incoming hc hab hOne fullDim.valid hForest first hZeroAtFirst).2
      rcases StableLocalProperties.leaf_block_dichotomy incoming fullDim.valid
          fullDim.noDanglingTargetFibres b hLeaf (fullDim.changeMinimal b)
          ((incoming.vertexPartition b).toBlock first) with hUnit | hRamified
      · have hFirstCard : (incoming.vertexPartition b).blockCard first = 1 :=
          ((incoming.vertexPartition b).blockCard_congr
            ((incoming.vertexPartition b).rel_repr_right first)).trans hUnit.2.1
        have hSecondMem : second ∈ (incoming.vertexPartition b).block first :=
          ((incoming.vertexPartition b).mem_block_iff first second).mpr hTogether
        rw [(incoming.vertexPartition b).block_eq_singleton_of_blockCard_eq_one
          first hFirstCard, Finset.mem_singleton] at hSecondMem
        exact hSecondMem.symm
      · rw [hEndpointZero] at hRamified
        omega
    · rintro rfl
      rfl
  have hEdgeDiscrete : DiscreteOnBlock (incoming.edgePartition contracted)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst hSecond
    constructor
    · intro hTogether
      have hEndpointRel :=
        (refines_of_mem_incidentEdges_local incoming
          (contracted_mem_incidentEdges_right hc)).rel hTogether
      exact (hRightDiscrete first second hFirst hSecond).mp hEndpointRel
    · rintro rfl
      rfl
  have hRightCount := blockCountWithin_eq_blockCard_of_discreteOnBlock
    (incoming.vertexPartition b) (mergedPartition incoming a b) background.1 hRightDiscrete
  have hEdgeCount := blockCountWithin_eq_blockCard_of_discreteOnBlock
    (incoming.edgePartition contracted) (mergedPartition incoming a b) background.1 hEdgeDiscrete
  let mergedBlock := selectedMergedBlock incoming hc hab hOne background
  have hTree := hForest mergedBlock
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.edgePartition contracted) (mergedPartition incoming a b)
      (edgePartition_refines_mergedPartition incoming hc),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b)] at hTree
  dsimp [mergedBlock, selectedMergedBlock] at hTree
  have hLeftCount : (incoming.vertexPartition a).blockCountWithin
      (mergedPartition incoming a b) background.1 = 1 := by omega
  have hLeftJoined := joinedOnBlock_of_blockCountWithin_eq_one
    (incoming.vertexPartition a) (mergedPartition incoming a b) background.1
    (vertexPartition_refines_mergedPartition incoming a b) hLeftCount
  exact ⟨hLeftJoined, hEdgeDiscrete, hRightDiscrete,
    hLeftCount, hEdgeCount, hRightCount⟩

/-- At two divalent incoming target endpoints, an r0 background block is
joined at both endpoints and along the contracted occurrence.  The key point
is local: vanishing ramification makes the contracted-edge relation equal to
each endpoint relation, so an alternating chain in their join is already a
chain in the contracted-edge relation. -/
theorem background_census_of_both_divalent
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {selected : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star selected)
    (background : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hBackground : background ≠ selected)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2) :
    JoinedOnBlock (incoming.vertexPartition a)
        (mergedPartition incoming a b) background.1 ∧
      JoinedOnBlock (incoming.edgePartition contracted)
        (mergedPartition incoming a b) background.1 ∧
      JoinedOnBlock (incoming.vertexPartition b)
        (mergedPartition incoming a b) background.1 ∧
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) background.1 = 1 ∧
      (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) background.1 = 1 ∧
      (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) background.1 = 1 := by
  let wallData := contractDatum incoming hc hab hOne
  let wall : (contract target hab hOne).V := ⟨a, hab⟩
  have hBackgroundZero : wallData.localRamification wall background = 0 :=
    W2RankObstructions.other_localRamification_eq_zero input selected
      profile.ramification background hBackground
  have hEndpointZero (sheet : Fin degree)
      (hSheet : (mergedPartition incoming a b).Rel background.1 sheet) :
      incoming.localRamification a ((incoming.vertexPartition a).toBlock sheet) = 0 ∧
        incoming.localRamification b ((incoming.vertexPartition b).toBlock sheet) = 0 := by
    let root : Fin degree := background.1
    have hWallRel : (wallData.vertexPartition wall).Rel background.1 sheet := by
      change (wallData.vertexPartition wall).Rel root sheet
      have hPartition : wallData.vertexPartition wall = mergedPartition incoming a b := by
        dsimp only [wallData, wall]
        exact contractDatum_vertexPartition_merge incoming hc hab hOne
      rw [hPartition]
      exact hSheet
    have hZeroAtRoot : localRamificationAt wallData wall background.1 = 0 :=
      (localRamificationAt_block wallData wall background).trans hBackgroundZero
    have hZeroAtSheet : localRamificationAt wallData wall sheet = 0 :=
      (localRamificationAt_congr wallData wall hWallRel).symm.trans hZeroAtRoot
    exact StablePathContraction.endpoint_localRamification_eq_zero
      incoming hc hab hOne fullDim.valid hForest sheet hZeroAtSheet
  have hEdgeJoined : JoinedOnBlock (incoming.edgePartition contracted)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst hSecond
    have hJoin : (mergedPartition incoming a b).Rel first second := hFirst.symm.trans hSecond
    have hAlt := (ContractionFibre.join_rel_iff_altChain
      (incoming.vertexPartition a) (incoming.vertexPartition b) first second).mp hJoin
    induction hAlt with
    | refl => rfl
    | tail hChain hStep ih =>
        have hPrefix := (ContractionFibre.join_rel_iff_altChain
          (incoming.vertexPartition a) (incoming.vertexPartition b) _ _).mpr hChain
        have hWithin : (mergedPartition incoming a b).Rel background.1 _ :=
          hFirst.trans hPrefix
        have hZero := hEndpointZero _ hWithin
        have hEdgeStep := hStep.elim
          (fun hLeft ↦
            (StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero
              incoming a hLeftDivalent _ hZero.1 contracted
              (contracted_mem_incidentEdges_left hc) _).mpr hLeft)
          (fun hRight ↦
            (StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero
              incoming b hRightDivalent _ hZero.2 contracted
              (contracted_mem_incidentEdges_right hc) _).mpr hRight)
        exact (ih hWithin hPrefix).trans hEdgeStep
  have hLeftJoined : JoinedOnBlock (incoming.vertexPartition a)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst hSecond
    have hZero := (hEndpointZero first hFirst).1
    exact (StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero
      incoming a hLeftDivalent first hZero contracted
      (contracted_mem_incidentEdges_left hc) second).mp
        (hEdgeJoined first second hFirst hSecond)
  have hRightJoined : JoinedOnBlock (incoming.vertexPartition b)
      (mergedPartition incoming a b) background.1 := by
    intro first second hFirst hSecond
    have hZero := (hEndpointZero first hFirst).2
    exact (StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero
      incoming b hRightDivalent first hZero contracted
      (contracted_mem_incidentEdges_right hc) second).mp
        (hEdgeJoined first second hFirst hSecond)
  exact ⟨hLeftJoined, hEdgeJoined, hRightJoined,
    blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hLeftJoined,
    blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hEdgeJoined,
    blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hRightJoined⟩

end DraismaVargas.LocalCases.M11IncomingBackground
