module

public import DraismaVargas.LocalCases.M11IncomingCoordinates
public import DraismaVargas.LocalCases.FullContractionFibre

@[expose] public section

/-!
# The selected two-sheet partition census before an M11 contraction

For the actual incoming cover, restrict the two endpoint partitions and the
contracted-occurrence partition to the selected two-sheet block of the
contracted wall datum.  Forestness leaves exactly three block-count patterns:
joined/joined with one internal occurrence, or one joined and one discrete
endpoint with two internal occurrences.

The statements are deliberately about induced block counts.  They do not
identify representative functions merely from equality of relations.
-/

namespace DraismaVargas.LocalCases.M11IncomingPartitions

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-- A fine partition joins the whole chosen coarse block, stated only at the
relation level so no representative-function equality is inferred. -/
def JoinedOnBlock {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d) : Prop :=
  ∀ i j, coarse.Rel root i → coarse.Rel root j → fine.Rel i j

/-- A fine partition is discrete on the chosen coarse block. -/
def DiscreteOnBlock {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d) : Prop :=
  ∀ i j, coarse.Rel root i → coarse.Rel root j → (fine.Rel i j ↔ i = j)

theorem joinedOnBlock_of_blockCountWithin_eq_one
    {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d)
    (hRefines : fine.Refines coarse)
    (hCount : fine.blockCountWithin coarse root = 1) :
    JoinedOnBlock fine coarse root := by
  intro i j hi hj
  have hBlock := fine.block_eq_of_refines_of_blockCountWithin_eq_one
    coarse hRefines root hCount
  have hri : fine.Rel root i := by
    apply (fine.mem_block_iff root i).mp
    rw [hBlock]
    exact (coarse.mem_block_iff root i).mpr hi
  have hrj : fine.Rel root j := by
    apply (fine.mem_block_iff root j).mp
    rw [hBlock]
    exact (coarse.mem_block_iff root j).mpr hj
  exact hri.symm.trans hrj

theorem blockCountWithin_eq_one_of_joinedOnBlock
    {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d)
    (hJoined : JoinedOnBlock fine coarse root) :
    fine.blockCountWithin coarse root = 1 := by
  unfold SheetPartition.blockCountWithin
  have hImage : (coarse.block root).image fine.repr = {fine.repr root} := by
    ext representative
    constructor
    · intro hRepresentative
      obtain ⟨sheet, hSheet, hImageEq⟩ := Finset.mem_image.mp hRepresentative
      have hCoarse : coarse.Rel root sheet :=
        (coarse.mem_block_iff root sheet).mp hSheet
      exact Finset.mem_singleton.mpr
        (hImageEq.symm.trans
          ((fine.rel_iff root sheet).mp (hJoined root sheet rfl hCoarse)).symm)
    · intro hRepresentative
      rw [Finset.mem_singleton] at hRepresentative
      subst representative
      exact Finset.mem_image.mpr ⟨root, coarse.self_mem_block root, rfl⟩
  rw [hImage]
  simp

/-- Every refinement of a two-sheet block is, on that block, either joined
or discrete. -/
theorem joinedOnBlock_or_discreteOnBlock_of_card_two
    {d : ℕ} (fine coarse : SheetPartition d) (root : Fin d)
    (hRefines : fine.Refines coarse) (hCard : coarse.blockCard root = 2) :
    JoinedOnBlock fine coarse root ∨ DiscreteOnBlock fine coarse root := by
  by_cases hCount : fine.blockCountWithin coarse root = 1
  · left
    exact joinedOnBlock_of_blockCountWithin_eq_one fine coarse root hRefines hCount
  · have hCountTwo : fine.blockCountWithin coarse root = 2 := by
      have hPos := fine.blockCountWithin_pos coarse root
      have hLe : fine.blockCountWithin coarse root ≤ 2 := by
        unfold SheetPartition.blockCountWithin
        rw [← hCard]
        exact Finset.card_image_le
      omega
    right
    intro i j hi hj
    constructor
    · intro hij
      by_contra hne
      have hPairCard : ({i, j} : Finset (Fin d)).card = 2 := by simp [hne]
      have hPairSubset : ({i, j} : Finset (Fin d)) ⊆ coarse.block root := by
        intro sheet hSheet
        simp only [Finset.mem_insert, Finset.mem_singleton] at hSheet
        rcases hSheet with rfl | rfl
        · exact (coarse.mem_block_iff root _).mpr hi
        · exact (coarse.mem_block_iff root _).mpr hj
      have hCoarsePair : coarse.block root = {i, j} := by
        exact (Finset.eq_of_subset_of_card_le hPairSubset (by
          change coarse.blockCard root ≤ ({i, j} : Finset (Fin d)).card
          rw [hCard, hPairCard])).symm
      have hImage : (coarse.block root).image fine.repr = {fine.repr i} := by
        rw [hCoarsePair]
        simp only [Finset.image_insert, Finset.image_singleton]
        rw [(fine.rel_iff i j).mp hij]
        simp
      unfold SheetPartition.blockCountWithin at hCountTwo
      rw [hImage] at hCountTwo
      simp at hCountTwo
    · rintro rfl
      rfl

/-- The selected wall block, read safely as a block of the literal join of
the two incoming endpoint partitions. -/
def selectedMergedBlock (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩) :
    (mergedPartition incoming a b).Blocks :=
  ⟨block.1, by
    rw [← contractDatum_vertexPartition_merge incoming hc hab hOne]
    exact block.2⟩

theorem selectedMergedBlock_card
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2) :
    (mergedPartition incoming a b).blockCard block.1 = 2 := by
  rw [← contractDatum_vertexPartition_merge incoming hc hab hOne]
  exact hCard

/-- The complete selected-block census.  Count one means that the fine
partition has the whole selected join block as one block; on this two-sheet
block count two is the discrete alternative. -/
theorem selected_blockCount_census
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hForest : ContractionForest incoming a b contracted)
    (block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2) :
    (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∨
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∧
        (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∨
      (incoming.vertexPartition a).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 ∧
        (incoming.vertexPartition b).blockCountWithin
          (mergedPartition incoming a b) block.1 = 1 ∧
        (incoming.edgePartition contracted).blockCountWithin
          (mergedPartition incoming a b) block.1 = 2 := by
  let selected := selectedMergedBlock incoming hc hab hOne block
  have hSelectedCard : (mergedPartition incoming a b).blockCard selected.1 = 2 := by
    exact selectedMergedBlock_card incoming hc hab hOne block hCard
  have hLeftPos := SheetPartition.blockCountWithin_pos
    (incoming.vertexPartition a) (mergedPartition incoming a b) selected.1
  have hRightPos := SheetPartition.blockCountWithin_pos
    (incoming.vertexPartition b) (mergedPartition incoming a b) selected.1
  have hEdgePos := SheetPartition.blockCountWithin_pos
    (incoming.edgePartition contracted) (mergedPartition incoming a b) selected.1
  have hLeftLe := SheetPartition.blockCountWithin_le_blockCard
    (incoming.vertexPartition a) (mergedPartition incoming a b)
    (vertexPartition_refines_mergedPartition incoming a b) selected
  have hRightLe := SheetPartition.blockCountWithin_le_blockCard
    (incoming.vertexPartition b) (mergedPartition incoming a b)
    (vertexPartition_refines_mergedPartition_right incoming a b) selected
  have hEdgeLe := SheetPartition.blockCountWithin_le_blockCard
    (incoming.edgePartition contracted) (mergedPartition incoming a b)
    (edgePartition_refines_mergedPartition incoming hc) selected
  rw [hSelectedCard] at hLeftLe hRightLe hEdgeLe
  have hTree := hForest selected
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.edgePartition contracted) (mergedPartition incoming a b)
      (edgePartition_refines_mergedPartition incoming hc),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b)] at hTree
  dsimp [selected, selectedMergedBlock] at hLeftPos hRightPos hEdgePos hLeftLe hRightLe hEdgeLe hTree
  omega

/-- Relation-level form of the census: all three incoming restrictions are
joined or discrete on the selected two-sheet block, and at least one actual
endpoint restriction is joined. -/
theorem selected_relation_census
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hForest : ContractionForest incoming a b contracted)
    (block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      block.1 = 2) :
    (JoinedOnBlock (incoming.vertexPartition a) (mergedPartition incoming a b) block.1 ∨
        DiscreteOnBlock (incoming.vertexPartition a) (mergedPartition incoming a b) block.1) ∧
      (JoinedOnBlock (incoming.vertexPartition b) (mergedPartition incoming a b) block.1 ∨
        DiscreteOnBlock (incoming.vertexPartition b) (mergedPartition incoming a b) block.1) ∧
      (JoinedOnBlock (incoming.edgePartition contracted) (mergedPartition incoming a b) block.1 ∨
        DiscreteOnBlock (incoming.edgePartition contracted) (mergedPartition incoming a b) block.1) ∧
      (JoinedOnBlock (incoming.vertexPartition a) (mergedPartition incoming a b) block.1 ∨
        JoinedOnBlock (incoming.vertexPartition b) (mergedPartition incoming a b) block.1) := by
  have hMergedCard := selectedMergedBlock_card incoming hc hab hOne block hCard
  have hLeftRefines := vertexPartition_refines_mergedPartition incoming a b
  have hRightRefines := vertexPartition_refines_mergedPartition_right incoming a b
  have hEdgeRefines := edgePartition_refines_mergedPartition incoming hc
  refine ⟨joinedOnBlock_or_discreteOnBlock_of_card_two _ _ _ hLeftRefines hMergedCard,
    joinedOnBlock_or_discreteOnBlock_of_card_two _ _ _ hRightRefines hMergedCard,
    joinedOnBlock_or_discreteOnBlock_of_card_two _ _ _ hEdgeRefines hMergedCard, ?_⟩
  rcases selected_blockCount_census incoming hc hab hOne hForest block hCard with
    hJoined | hSplitRight | hSplitLeft
  · exact Or.inl (joinedOnBlock_of_blockCountWithin_eq_one _ _ _ hLeftRefines hJoined.1)
  · exact Or.inl (joinedOnBlock_of_blockCountWithin_eq_one _ _ _ hLeftRefines hSplitRight.1)
  · exact Or.inr (joinedOnBlock_of_blockCountWithin_eq_one _ _ _ hRightRefines hSplitLeft.2.1)

/-- Forestness rules out two distinct internal occurrences when both actual
endpoint restrictions are joined: the contracted-occurrence restriction then
has exactly one block. -/
theorem internal_blockCount_eq_one_of_endpoints_joined
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hForest : ContractionForest incoming a b contracted)
    (block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hLeft : JoinedOnBlock (incoming.vertexPartition a)
      (mergedPartition incoming a b) block.1)
    (hRight : JoinedOnBlock (incoming.vertexPartition b)
      (mergedPartition incoming a b) block.1) :
    (incoming.edgePartition contracted).blockCountWithin
      (mergedPartition incoming a b) block.1 = 1 := by
  let selected := selectedMergedBlock incoming hc hab hOne block
  have hLeftCount := blockCountWithin_eq_one_of_joinedOnBlock
    (incoming.vertexPartition a) (mergedPartition incoming a b) block.1 hLeft
  have hRightCount := blockCountWithin_eq_one_of_joinedOnBlock
    (incoming.vertexPartition b) (mergedPartition incoming a b) block.1 hRight
  have hTree := hForest selected
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.edgePartition contracted) (mergedPartition incoming a b)
      (edgePartition_refines_mergedPartition incoming hc),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition a) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition incoming a b),
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (incoming.vertexPartition b) (mergedPartition incoming a b)
      (vertexPartition_refines_mergedPartition_right incoming a b)] at hTree
  dsimp [selected, selectedMergedBlock] at hTree
  omega

end DraismaVargas.LocalCases.M11IncomingPartitions
