module

public import DraismaVargas.LocalCases.M11IncomingSelectedCases
public import DraismaVargas.LocalCases.M11IncomingBackground
public import DraismaVargas.LocalCases.M11IncomingOuterPartitions
public import DraismaVargas.LocalCases.M11RemoteCandidates
public import DraismaVargas.Infrastructure.PartitionNormalization

@[expose] public section

/-!
# Pointwise partition matching for the incoming M11 split

After the actual leaf target is normalized to the first split target, every
incoming sheet partition has the same blocks as the literal position-zero M11
candidate.  The proof compares the selected wall class and every background
class separately before invoking representative normalization.
-/

namespace DraismaVargas.LocalCases.M11IncomingSplitMatching

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open GraphContraction GluingContraction ContractionRamification
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates
open W4Assembly W2R1Target SecondEquation FullDimensionalSource
open M11IncomingPartitions M11IncomingSelectedCases M11IncomingBackground
open M11IncomingTargetNormalization M11IncomingOuterPartitions

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

private theorem sameBlocks_of_eq {d : ℕ} {first second : SheetPartition d}
    (h : first = second) : first.SameBlocks second := by
  rw [h]
  exact SheetPartition.SameBlocks.refl _

private theorem sameBlocks_pasteLeft_of_local
    (wall fine : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (hFine : fine.Refines wall)
    (hLocal : ∀ first second, wall.Rel first second →
      (fine.Rel first second ↔
        (resolution (wall.repr first)).left.Rel first second)) :
    fine.SameBlocks (LocalResolution.paste wall resolution hContracts).left := by
  intro first second
  change fine.Rel first second ↔
    (LocalResolution.pasteLeft wall resolution hContracts).Rel first second
  unfold LocalResolution.pasteLeft
  rw [wall.paste_rel_iff]
  constructor
  · intro hRel
    exact (hLocal first second (hFine.rel hRel)).mp hRel
  · intro hRel
    have hWall := (hContracts (wall.repr first)).left_refines.rel hRel
    exact (hLocal first second hWall).mpr hRel

private theorem sameBlocks_pasteRight_of_local
    (wall fine : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (hFine : fine.Refines wall)
    (hLocal : ∀ first second, wall.Rel first second →
      (fine.Rel first second ↔
        (resolution (wall.repr first)).right.Rel first second)) :
    fine.SameBlocks (LocalResolution.paste wall resolution hContracts).right := by
  intro first second
  change fine.Rel first second ↔
    (LocalResolution.pasteRight wall resolution hContracts).Rel first second
  unfold LocalResolution.pasteRight
  rw [wall.paste_rel_iff]
  constructor
  · intro hRel
    exact (hLocal first second (hFine.rel hRel)).mp hRel
  · intro hRel
    have hWall := (hContracts (wall.repr first)).right_refines.rel hRel
    exact (hLocal first second hWall).mpr hRel

private theorem sameBlocks_pasteNewEdge_of_local
    (wall fine : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (hFine : fine.Refines wall)
    (hLocal : ∀ first second, wall.Rel first second →
      (fine.Rel first second ↔
        (resolution (wall.repr first)).newEdge.Rel first second)) :
    fine.SameBlocks (LocalResolution.paste wall resolution hContracts).newEdge := by
  intro first second
  change fine.Rel first second ↔
    (LocalResolution.pasteNewEdge wall resolution hContracts).Rel first second
  unfold LocalResolution.pasteNewEdge
  rw [wall.paste_rel_iff]
  constructor
  · intro hRel
    exact (hLocal first second (hFine.rel hRel)).mp hRel
  · intro hRel
    have hWall := ((resolution (wall.repr first)).edge_refines_left.trans
      (hContracts (wall.repr first)).left_refines).rel hRel
    exact (hLocal first second hWall).mpr hRel

private theorem split_leaf_sameBlocks
    (wall leaf : SheetPartition degree) (selected : Fin degree)
    (hLeafRefines : leaf.Refines wall)
    (hSelected : JoinedOnBlock leaf wall selected)
    (hBackground : ∀ root, ¬ wall.Rel selected root →
      DiscreteOnBlock leaf wall root)
    (hContracts : ∀ anchor,
      (LocalResolution.onBlock wall selected
        (splitResolutionAt wall selected) (backgroundResolution wall) anchor).ContractsTo wall) :
    leaf.SameBlocks
      (LocalResolution.paste wall
        (LocalResolution.onBlock wall selected
          (splitResolutionAt wall selected) (backgroundResolution wall))
        hContracts).left := by
  apply sameBlocks_pasteLeft_of_local wall leaf _ hContracts hLeafRefines
  intro first second hWall
  by_cases hFirst : wall.Rel selected first
  · have hCanonical : wall.Rel selected (wall.repr first) :=
      hFirst.trans (wall.rel_repr_right first)
    rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hCanonical]
    change leaf.Rel first second ↔ wall.Rel first second
    exact ⟨fun _ => hWall, fun _ =>
      hSelected first second hFirst (hFirst.trans hWall)⟩
  · have hCanonical : ¬ wall.Rel selected (wall.repr first) := by
      intro h
      exact hFirst (h.trans (wall.rel_repr_left first))
    rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hCanonical]
    change leaf.Rel first second ↔ (wall.splitBlock (wall.repr first)).Rel first second
    rw [wall.splitBlock_rel_of_rel_anchor_iff
      (wall.repr first) first (wall.rel_repr_left first) second]
    exact hBackground first hFirst first second rfl hWall

private theorem split_trivalent_sameBlocks
    (wall trivalent : SheetPartition degree) (selected : Fin degree)
    (hTrivalentRefines : trivalent.Refines wall)
    (hSelected : DiscreteOnBlock trivalent wall selected)
    (hBackground : ∀ root, ¬ wall.Rel selected root →
      JoinedOnBlock trivalent wall root)
    (hContracts : ∀ anchor,
      (LocalResolution.onBlock wall selected
        (splitResolutionAt wall selected) (backgroundResolution wall) anchor).ContractsTo wall) :
    trivalent.SameBlocks
      (LocalResolution.paste wall
        (LocalResolution.onBlock wall selected
          (splitResolutionAt wall selected) (backgroundResolution wall))
        hContracts).right := by
  apply sameBlocks_pasteRight_of_local wall trivalent _ hContracts hTrivalentRefines
  intro first second hWall
  by_cases hFirst : wall.Rel selected first
  · have hCanonical : wall.Rel selected (wall.repr first) :=
      hFirst.trans (wall.rel_repr_right first)
    rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hCanonical]
    change trivalent.Rel first second ↔
      (wall.splitBlock selected).Rel first second
    rw [wall.splitBlock_rel_of_rel_anchor_iff selected first hFirst second]
    exact hSelected first second hFirst (hFirst.trans hWall)
  · have hCanonical : ¬ wall.Rel selected (wall.repr first) := by
      intro h
      exact hFirst (h.trans (wall.rel_repr_left first))
    rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hCanonical]
    change trivalent.Rel first second ↔ wall.Rel first second
    exact ⟨fun _ => hWall, fun _ =>
      hBackground first hFirst first second rfl hWall⟩

private theorem split_newEdge_sameBlocks
    (wall internal : SheetPartition degree) (selected : Fin degree)
    (hInternalRefines : internal.Refines wall)
    (hSelected : DiscreteOnBlock internal wall selected)
    (hBackground : ∀ root, ¬ wall.Rel selected root →
      DiscreteOnBlock internal wall root)
    (hContracts : ∀ anchor,
      (LocalResolution.onBlock wall selected
        (splitResolutionAt wall selected) (backgroundResolution wall) anchor).ContractsTo wall) :
    internal.SameBlocks
      (LocalResolution.paste wall
        (LocalResolution.onBlock wall selected
          (splitResolutionAt wall selected) (backgroundResolution wall))
        hContracts).newEdge := by
  apply sameBlocks_pasteNewEdge_of_local wall internal _ hContracts hInternalRefines
  intro first second hWall
  by_cases hFirst : wall.Rel selected first
  · have hCanonical : wall.Rel selected (wall.repr first) :=
      hFirst.trans (wall.rel_repr_right first)
    rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hCanonical]
    change internal.Rel first second ↔
      (wall.splitBlock selected).Rel first second
    rw [wall.splitBlock_rel_of_rel_anchor_iff selected first hFirst second]
    exact hSelected first second hFirst (hFirst.trans hWall)
  · have hCanonical : ¬ wall.Rel selected (wall.repr first) := by
      intro h
      exact hFirst (h.trans (wall.rel_repr_left first))
    rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hCanonical]
    change internal.Rel first second ↔
      (wall.splitBlock (wall.repr first)).Rel first second
    rw [wall.splitBlock_rel_of_rel_anchor_iff
      (wall.repr first) first (wall.rel_repr_left first) second]
    exact hBackground first hFirst first second rfl hWall

section CandidatePartitions

variable {wallTarget : CFGraph} {wallDegree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget wallDegree}
  {star : TwoStar wallTarget wall}

private theorem firstSplit_leaf_sameBlocks
    (input : W2SourceInput wallData star)
    {block : WallBlock wallData wall}
    (profile : W2R2SourceProfile.SourceProfile wallData star block)
    (hCard : (wallData.vertexPartition wall).blockCard block.1 = 2)
    (leaf : SheetPartition wallDegree)
    (hLeafRefines : leaf.Refines (wallData.vertexPartition wall))
    (hSelected : JoinedOnBlock leaf (wallData.vertexPartition wall) block.1)
    (hBackground : ∀ root, ¬ (wallData.vertexPartition wall).Rel block.1 root →
      DiscreteOnBlock leaf (wallData.vertexPartition wall) root) :
    leaf.SameBlocks
      ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
        (oldVertex wallTarget wall)) := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_wall]
  apply split_leaf_sameBlocks (wallData.vertexPartition wall) leaf block.1
    hLeafRefines hSelected hBackground

private theorem firstSplit_trivalent_sameBlocks
    (input : W2SourceInput wallData star)
    {block : WallBlock wallData wall}
    (profile : W2R2SourceProfile.SourceProfile wallData star block)
    (hCard : (wallData.vertexPartition wall).blockCard block.1 = 2)
    (trivalent : SheetPartition wallDegree)
    (hTrivalentRefines : trivalent.Refines (wallData.vertexPartition wall))
    (hSelected : DiscreteOnBlock trivalent (wallData.vertexPartition wall) block.1)
    (hBackground : ∀ root, ¬ (wallData.vertexPartition wall).Rel block.1 root →
      JoinedOnBlock trivalent (wallData.vertexPartition wall) root) :
    trivalent.SameBlocks
      ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
        (freshVertex wallTarget)) := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_fresh]
  apply split_trivalent_sameBlocks (wallData.vertexPartition wall) trivalent block.1
    hTrivalentRefines hSelected hBackground

private theorem firstSplit_internal_sameBlocks
    (input : W2SourceInput wallData star)
    {block : WallBlock wallData wall}
    (profile : W2R2SourceProfile.SourceProfile wallData star block)
    (hCard : (wallData.vertexPartition wall).blockCard block.1 = 2)
    (internal : SheetPartition wallDegree)
    (hInternalRefines : internal.Refines (wallData.vertexPartition wall))
    (hSelected : DiscreteOnBlock internal (wallData.vertexPartition wall) block.1)
    (hBackground : ∀ root, ¬ (wallData.vertexPartition wall).Rel block.1 root →
      DiscreteOnBlock internal (wallData.vertexPartition wall) root) :
    internal.SameBlocks
      ((firstSplitPattern input profile hCard).candidate.datum.edgePartition
        (occurrenceEquiv wallTarget wall (fun _ => true) none)) := by
  change internal.SameBlocks
    ((firstSplitPattern input profile hCard).candidate.datum.edgePartition
      (occurrenceEquiv wallTarget wall
        (firstSplitPattern input profile hCard).candidate.right none))
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_new]
  apply split_newEdge_sameBlocks (wallData.vertexPartition wall) internal block.1
    hInternalRefines hSelected hBackground

private theorem firstSplit_vertexPartition_old_of_ne
    (input : W2SourceInput wallData star)
    {block : WallBlock wallData wall}
    (profile : W2R2SourceProfile.SourceProfile wallData star block)
    (hCard : (wallData.vertexPartition wall).blockCard block.1 = 2)
    (vertex : wallTarget.V) (hNe : vertex ≠ wall) :
    (firstSplitPattern input profile hCard).candidate.datum.vertexPartition
        (oldVertex wallTarget vertex) = wallData.vertexPartition vertex := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hNe]

private theorem firstSplit_edgePartition_old
    (input : W2SourceInput wallData star)
    {block : WallBlock wallData wall}
    (profile : W2R2SourceProfile.SourceProfile wallData star block)
    (hCard : (wallData.vertexPartition wall).blockCard block.1 = 2)
    (edge : wallTarget.edges) :
    (firstSplitPattern input profile hCard).candidate.datum.edgePartition
        (occurrenceEquiv wallTarget wall (fun _ => true) (some edge)) =
      wallData.edgePartition edge := by
  change (firstSplitPattern input profile hCard).candidate.datum.edgePartition
      (occurrenceEquiv wallTarget wall
        (firstSplitPattern input profile hCard).candidate.right (some edge)) =
    wallData.edgePartition edge
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_old]

end CandidatePartitions

private theorem background_relations_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    ∀ root, ¬ (mergedPartition incoming a b).Rel block.1 root →
      DiscreteOnBlock (incoming.vertexPartition a)
          (mergedPartition incoming a b) root ∧
        DiscreteOnBlock (incoming.edgePartition contracted)
          (mergedPartition incoming a b) root ∧
        JoinedOnBlock (incoming.vertexPartition b)
          (mergedPartition incoming a b) root := by
  intro root hRoot
  let background : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩ :=
    WallBlock.ofSheet (contractDatum incoming hc hab hOne) ⟨a, hab⟩ root
  have hNe : background ≠ block := by
    intro hEq
    apply hRoot
    have hEqVal := congrArg Subtype.val hEq
    dsimp [background, WallBlock.ofSheet] at hEqVal
    have hPartition :
        contractVertexPartition incoming a b ⟨a, hab⟩ =
          mergedPartition incoming a b :=
      contractVertexPartition_merge incoming a b hab
    have hEqVal' : (mergedPartition incoming a b).repr root = block.1 :=
      (congrArg (fun partition : SheetPartition degree => partition.repr root)
        hPartition.symm).trans hEqVal
    have hBlockFixed : (mergedPartition incoming a b).repr block.1 = block.1 :=
      (congrArg (fun partition : SheetPartition degree => partition.repr block.1)
        hPartition.symm).trans block.2
    change (mergedPartition incoming a b).repr block.1 =
      (mergedPartition incoming a b).repr root
    exact hBlockFixed.trans hEqVal'.symm
  have hCensus := background_census_of_left_leaf incoming hc hab hOne
    fullDim hForest input profile background hNe hLeaf
  have hBackgroundVal :
      background.1 = (mergedPartition incoming a b).repr root := by
    dsimp [background, WallBlock.ofSheet]
    exact congrArg (fun partition : SheetPartition degree => partition.repr root)
      (contractVertexPartition_merge incoming a b hab)
  refine ⟨?_, ?_, ?_⟩
  · intro first second hFirst hSecond
    exact hCensus.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)
  · intro first second hFirst hSecond
    exact hCensus.2.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)
  · intro first second hFirst hSecond
    exact hCensus.2.2.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)

private theorem background_relations_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    ∀ root, ¬ (mergedPartition incoming a b).Rel block.1 root →
      JoinedOnBlock (incoming.vertexPartition a)
          (mergedPartition incoming a b) root ∧
        DiscreteOnBlock (incoming.edgePartition contracted)
          (mergedPartition incoming a b) root ∧
        DiscreteOnBlock (incoming.vertexPartition b)
          (mergedPartition incoming a b) root := by
  intro root hRoot
  let background : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩ :=
    WallBlock.ofSheet (contractDatum incoming hc hab hOne) ⟨a, hab⟩ root
  have hNe : background ≠ block := by
    intro hEq
    apply hRoot
    have hEqVal := congrArg Subtype.val hEq
    dsimp [background, WallBlock.ofSheet] at hEqVal
    have hPartition :
        contractVertexPartition incoming a b ⟨a, hab⟩ =
          mergedPartition incoming a b :=
      contractVertexPartition_merge incoming a b hab
    have hEqVal' : (mergedPartition incoming a b).repr root = block.1 :=
      (congrArg (fun partition : SheetPartition degree => partition.repr root)
        hPartition.symm).trans hEqVal
    have hBlockFixed : (mergedPartition incoming a b).repr block.1 = block.1 :=
      (congrArg (fun partition : SheetPartition degree => partition.repr block.1)
        hPartition.symm).trans block.2
    change (mergedPartition incoming a b).repr block.1 =
      (mergedPartition incoming a b).repr root
    exact hBlockFixed.trans hEqVal'.symm
  have hCensus := background_census_of_right_leaf incoming hc hab hOne
    fullDim hForest input profile background hNe hLeaf
  have hBackgroundVal :
      background.1 = (mergedPartition incoming a b).repr root := by
    dsimp [background, WallBlock.ofSheet]
    exact congrArg (fun partition : SheetPartition degree => partition.repr root)
      (contractVertexPartition_merge incoming a b hab)
  refine ⟨?_, ?_, ?_⟩
  · intro first second hFirst hSecond
    exact hCensus.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)
  · intro first second hFirst hSecond
    exact hCensus.2.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)
  · intro first second hFirst hSecond
    exact hCensus.2.2.1 first second
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hFirst)
      (by rw [hBackgroundVal]
          exact ((mergedPartition incoming a b).rel_repr_left root).trans hSecond)

/-- Pointwise vertex-partition matching after a left-leaf incoming target is
normalized to the first split target. -/
theorem vertexPartitions_sameBlocks_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    ∀ vertex,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).vertexPartition vertex).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition vertex) := by
  have hSelected := selected_census_of_left_leaf incoming hc hab hOne fullDim
    hForest profile hCard hLeaf
  have hBackground := background_relations_of_left_leaf incoming hc hab hOne
    fullDim hForest input profile hLeaf
  intro vertex
  rcases vertex with vertex | _
  · by_cases hWall : vertex = (⟨a, hab⟩ : (contract target hab hOne).V)
    · subst vertex
      have hOuter := congrArg Prod.fst
        (split_endpointPartitions_of_leaf_left incoming hc hab hOne star hLeaf)
      have hLeafRefines :
          (incoming.vertexPartition a).Refines
            ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
        simpa only [contractDatum_vertexPartition_merge] using
          vertexPartition_refines_mergedPartition incoming a b
      have hSelectedLeaf : JoinedOnBlock (incoming.vertexPartition a)
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
        simpa only [contractDatum_vertexPartition_merge] using hSelected.1
      exact (sameBlocks_of_eq hOuter).trans
        (firstSplit_leaf_sameBlocks input profile hCard
          (incoming.vertexPartition a)
          hLeafRefines hSelectedLeaf (fun root hRoot => by
            have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
              simpa only [contractDatum_vertexPartition_merge] using hRoot
            simpa only [contractDatum_vertexPartition_merge] using
              (hBackground root hRoot').1))
    · have hOuter := transported_vertexPartition_of_ne incoming hc hab hOne
        (fun _ => true) (splitPlacement hc hab hOne star (Or.inl hLeaf))
        vertex hWall
      have hOuter' :
          (GluingTransport.transport
            (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).vertexPartition
              (oldVertex (contract target hab hOne) vertex) =
            (contractDatum incoming hc hab hOne).vertexPartition vertex := by
        simpa only [splitIso] using hOuter
      change ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).vertexPartition
          (oldVertex (contract target hab hOne) vertex)).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
          (oldVertex (contract target hab hOne) vertex))
      rw [hOuter']
      rw [firstSplit_vertexPartition_old_of_ne input profile hCard vertex hWall]
      exact SheetPartition.SameBlocks.refl _
  · cases ‹Unit›
    have hOuter := congrArg Prod.snd
      (split_endpointPartitions_of_leaf_left incoming hc hab hOne star hLeaf)
    have hTrivalentRefines :
        (incoming.vertexPartition b).Refines
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
      simpa only [contractDatum_vertexPartition_merge] using
        vertexPartition_refines_mergedPartition_right incoming a b
    have hSelectedTrivalent : DiscreteOnBlock (incoming.vertexPartition b)
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
      simpa only [contractDatum_vertexPartition_merge] using hSelected.2.2.1
    exact (sameBlocks_of_eq hOuter).trans
      (firstSplit_trivalent_sameBlocks input profile hCard
        (incoming.vertexPartition b)
        hTrivalentRefines hSelectedTrivalent
        (fun root hRoot => by
          have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
            simpa only [contractDatum_vertexPartition_merge] using hRoot
          simpa only [contractDatum_vertexPartition_merge] using
            (hBackground root hRoot').2.2))

/-- Pointwise edge-partition matching after a left-leaf incoming target is
normalized to the first split target. -/
theorem edgePartitions_sameBlocks_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    ∀ edge : (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩
        (firstSplitPattern input profile hCard).candidate.right).edges,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).edgePartition edge).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.edgePartition edge) := by
  have hSelected := selected_census_of_left_leaf incoming hc hab hOne fullDim
    hForest profile hCard hLeaf
  have hBackground := background_relations_of_left_leaf incoming hc hab hOne
    fullDim hForest input profile hLeaf
  intro edge
  obtain ⟨column, rfl⟩ :=
    (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (fun _ => true)).surjective edge
  cases column with
  | none =>
    have hOuter := transported_edgePartition_new incoming hc hab hOne (fun _ => true)
      (splitPlacement hc hab hOne star (Or.inl hLeaf))
      fullDim.targetConnected fullDim.targetGenus
    have hInternalRefines :
        (incoming.edgePartition contracted).Refines
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
      simpa only [contractDatum_vertexPartition_merge] using
        edgePartition_refines_mergedPartition incoming hc
    have hSelectedInternal : DiscreteOnBlock (incoming.edgePartition contracted)
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
      simpa only [contractDatum_vertexPartition_merge] using hSelected.2.1
    exact (sameBlocks_of_eq hOuter).trans
      (firstSplit_internal_sameBlocks input profile hCard
        (incoming.edgePartition contracted) hInternalRefines hSelectedInternal
        (fun root hRoot => by
          have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
            simpa only [contractDatum_vertexPartition_merge] using hRoot
          simpa only [contractDatum_vertexPartition_merge] using
            (hBackground root hRoot').2.1))
  | some edge =>
    have hOuter := transported_edgePartition_retained incoming hc hab hOne (fun _ => true)
      (splitPlacement hc hab hOne star (Or.inl hLeaf))
      fullDim.targetConnected fullDim.targetGenus edge
    have hCandidate := firstSplit_edgePartition_old input profile hCard edge
    exact sameBlocks_of_eq (hOuter.trans hCandidate.symm)

/-- Pointwise vertex-partition matching after a right-leaf incoming target is
normalized, with the endpoint swap built into the actual `splitIso`. -/
theorem vertexPartitions_sameBlocks_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    ∀ vertex,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).vertexPartition vertex).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition vertex) := by
  have hSelected := selected_census_of_right_leaf incoming hc hab hOne fullDim
    hForest profile hCard hLeaf
  have hBackground := background_relations_of_right_leaf incoming hc hab hOne
    fullDim hForest input profile hLeaf
  intro vertex
  rcases vertex with vertex | _
  · by_cases hWall : vertex = (⟨a, hab⟩ : (contract target hab hOne).V)
    · subst vertex
      have hOuter := congrArg Prod.fst
        (split_endpointPartitions_of_leaf_right incoming hc hab hOne star hLeaf)
      have hLeafRefines :
          (incoming.vertexPartition b).Refines
            ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
        simpa only [contractDatum_vertexPartition_merge] using
          vertexPartition_refines_mergedPartition_right incoming a b
      have hSelectedLeaf : JoinedOnBlock (incoming.vertexPartition b)
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
        simpa only [contractDatum_vertexPartition_merge] using hSelected.2.2.1
      exact (sameBlocks_of_eq hOuter).trans
        (firstSplit_leaf_sameBlocks input profile hCard
          (incoming.vertexPartition b)
          hLeafRefines hSelectedLeaf (fun root hRoot => by
            have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
              simpa only [contractDatum_vertexPartition_merge] using hRoot
            simpa only [contractDatum_vertexPartition_merge] using
              (hBackground root hRoot').2.2))
    · have hOuter := transported_vertexPartition_of_ne incoming hc hab hOne
        (fun _ => true) (splitPlacement hc hab hOne star (Or.inr hLeaf))
        vertex hWall
      have hOuter' :
          (GluingTransport.transport
            (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).vertexPartition
              (oldVertex (contract target hab hOne) vertex) =
            (contractDatum incoming hc hab hOne).vertexPartition vertex := by
        simpa only [splitIso] using hOuter
      change ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).vertexPartition
          (oldVertex (contract target hab hOne) vertex)).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
          (oldVertex (contract target hab hOne) vertex))
      rw [hOuter']
      rw [firstSplit_vertexPartition_old_of_ne input profile hCard vertex hWall]
      exact SheetPartition.SameBlocks.refl _
  · cases ‹Unit›
    have hOuter := congrArg Prod.snd
      (split_endpointPartitions_of_leaf_right incoming hc hab hOne star hLeaf)
    have hTrivalentRefines :
        (incoming.vertexPartition a).Refines
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
      simpa only [contractDatum_vertexPartition_merge] using
        vertexPartition_refines_mergedPartition incoming a b
    have hSelectedTrivalent : DiscreteOnBlock (incoming.vertexPartition a)
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
      simpa only [contractDatum_vertexPartition_merge] using hSelected.1
    exact (sameBlocks_of_eq hOuter).trans
      (firstSplit_trivalent_sameBlocks input profile hCard
        (incoming.vertexPartition a)
        hTrivalentRefines hSelectedTrivalent
        (fun root hRoot => by
          have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
            simpa only [contractDatum_vertexPartition_merge] using hRoot
          simpa only [contractDatum_vertexPartition_merge] using
            (hBackground root hRoot').1))

/-- Pointwise edge-partition matching in the right-leaf split case. -/
theorem edgePartitions_sameBlocks_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    ∀ edge : (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩
        (firstSplitPattern input profile hCard).candidate.right).edges,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).edgePartition edge).SameBlocks
        ((firstSplitPattern input profile hCard).candidate.datum.edgePartition edge) := by
  have hSelected := selected_census_of_right_leaf incoming hc hab hOne fullDim
    hForest profile hCard hLeaf
  have hBackground := background_relations_of_right_leaf incoming hc hab hOne
    fullDim hForest input profile hLeaf
  intro edge
  obtain ⟨column, rfl⟩ :=
    (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (fun _ => true)).surjective edge
  cases column with
  | none =>
    have hOuter := transported_edgePartition_new incoming hc hab hOne (fun _ => true)
      (splitPlacement hc hab hOne star (Or.inr hLeaf))
      fullDim.targetConnected fullDim.targetGenus
    have hInternalRefines :
        (incoming.edgePartition contracted).Refines
          ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
      simpa only [contractDatum_vertexPartition_merge] using
        edgePartition_refines_mergedPartition incoming hc
    have hSelectedInternal : DiscreteOnBlock (incoming.edgePartition contracted)
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 := by
      simpa only [contractDatum_vertexPartition_merge] using hSelected.2.1
    exact (sameBlocks_of_eq hOuter).trans
      (firstSplit_internal_sameBlocks input profile hCard
        (incoming.edgePartition contracted) hInternalRefines hSelectedInternal
        (fun root hRoot => by
          have hRoot' : ¬ (mergedPartition incoming a b).Rel block.1 root := by
            simpa only [contractDatum_vertexPartition_merge] using hRoot
          simpa only [contractDatum_vertexPartition_merge] using
            (hBackground root hRoot').2.1))
  | some edge =>
    have hOuter := transported_edgePartition_retained incoming hc hab hOne (fun _ => true)
      (splitPlacement hc hab hOne star (Or.inr hLeaf))
      fullDim.targetConnected fullDim.targetGenus edge
    have hCandidate := firstSplit_edgePartition_old input profile hCard edge
    exact sameBlocks_of_eq (hOuter.trans hCandidate.symm)

/-- Whole-cover pointwise partition matching against the actual position-zero
M11 family member in the left-leaf split case. -/
theorem sameBlocks_against_position_zero_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    (∀ vertex : (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget.V,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).vertexPartition vertex).SameBlocks
        ((M11RemoteCandidates.candidates input profile hCard 0).datum.vertexPartition vertex)) ∧
    (∀ edge : (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget.edges,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).edgePartition edge).SameBlocks
        ((M11RemoteCandidates.candidates input profile hCard 0).datum.edgePartition edge)) := by
  exact ⟨vertexPartitions_sameBlocks_of_left_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf,
    edgePartitions_sameBlocks_of_left_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf⟩

/-- Whole-cover pointwise partition matching against the same actual
position-zero member in the right-leaf split case. -/
theorem sameBlocks_against_position_zero_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    (∀ vertex : (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget.V,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).vertexPartition vertex).SameBlocks
        ((M11RemoteCandidates.candidates input profile hCard 0).datum.vertexPartition vertex)) ∧
    (∀ edge : (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget.edges,
      ((GluingTransport.transport
        (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).edgePartition edge).SameBlocks
        ((M11RemoteCandidates.candidates input profile hCard 0).datum.edgePartition edge)) := by
  exact ⟨vertexPartitions_sameBlocks_of_right_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf,
    edgePartitions_sameBlocks_of_right_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf⟩

/-- The compatible within-block sheet normalization in the left-leaf case. -/
noncomputable def sheetRelabeling_of_left_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inl hLeaf)) incoming).SheetRelabeling :=
  PartitionNormalization.sheetRelabeling
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inl hLeaf)) incoming)
    (M11RemoteCandidates.candidates input profile hCard 0).datum
    (sameBlocks_against_position_zero_of_left_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).1
    (sameBlocks_against_position_zero_of_left_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).2

/-- Normalizing inside every actual block makes the left-leaf incoming datum
literally equal to position zero, including its representative tables. -/
theorem sheetRelabeling_of_left_leaf_apply
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    (sheetRelabeling_of_left_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf).apply =
        (M11RemoteCandidates.candidates input profile hCard 0).datum :=
  PartitionNormalization.sheetRelabeling_apply
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inl hLeaf)) incoming)
    (M11RemoteCandidates.candidates input profile hCard 0).datum
    (sameBlocks_against_position_zero_of_left_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).1
    (sameBlocks_against_position_zero_of_left_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).2

/-- The compatible within-block sheet normalization in the right-leaf case. -/
noncomputable def sheetRelabeling_of_right_leaf
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inr hLeaf)) incoming).SheetRelabeling :=
  PartitionNormalization.sheetRelabeling
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inr hLeaf)) incoming)
    (M11RemoteCandidates.candidates input profile hCard 0).datum
    (sameBlocks_against_position_zero_of_right_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).1
    (sameBlocks_against_position_zero_of_right_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).2

/-- Normalizing inside every actual block makes the right-leaf incoming datum
literally equal to position zero. -/
theorem sheetRelabeling_of_right_leaf_apply
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile
      (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    (sheetRelabeling_of_right_leaf incoming hc hab hOne fullDim hForest
      input profile hCard hLeaf).apply =
        (M11RemoteCandidates.candidates input profile hCard 0).datum :=
  PartitionNormalization.sheetRelabeling_apply
    (GluingTransport.transport
      (splitIso hc hab hOne star (Or.inr hLeaf)) incoming)
    (M11RemoteCandidates.candidates input profile hCard 0).datum
    (sameBlocks_against_position_zero_of_right_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).1
    (sameBlocks_against_position_zero_of_right_leaf incoming hc hab hOne fullDim
      hForest input profile hCard hLeaf).2

end DraismaVargas.LocalCases.M11IncomingSplitMatching
