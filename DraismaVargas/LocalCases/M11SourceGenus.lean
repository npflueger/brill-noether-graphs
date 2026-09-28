import DraismaVargas.LocalCases.M11RemoteCandidates
import DraismaVargas.Infrastructure.SheetGluingGenus

/-!
# Source genus of the three universal M11 candidates

Figure 32 of Draisma–Vargas Part I, arXiv:1909.12924 (case
`{w2-r2-nd3-M-11}`), replaces each wall block by a star: one endpoint keeps the wall
block and the other endpoint has exactly the partition of the new edge.
The distinguished split block and the r0 background use opposite orientations.
Counting canonical representatives sheet by sheet proves the pasted Euler
identity without assuming a source genus or a displayed stable-path census.
The remote second split first applies a source-graph relabelling equivalence.
-/

namespace DraismaVargas.LocalCases.M11SourceGenus

open DraismaVargas.Infrastructure
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates
open W4Assembly W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- Pasting stars in either orientation preserves the source Euler count.
The identity holds pointwise on canonical-representative indicators, so no
uniform choice of orientation on the wall blocks is required. -/
theorem paste_block_euler (partition : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo partition)
    (hStar : ∀ anchor,
      ((resolution anchor).left = partition ∧
        (resolution anchor).newEdge = (resolution anchor).right) ∨
      ((resolution anchor).right = partition ∧
        (resolution anchor).newEdge = (resolution anchor).left)) :
    Fintype.card (LocalResolution.paste partition resolution hContracts).newEdge.Blocks +
        Fintype.card partition.Blocks =
      Fintype.card (LocalResolution.paste partition resolution hContracts).left.Blocks +
        Fintype.card (LocalResolution.paste partition resolution hContracts).right.Blocks := by
  classical
  simp only [SheetPartition.card_blocks_eq_sum_fixed, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sheet _
  change
    (if (resolution (partition.repr sheet)).newEdge.repr sheet = sheet then 1 else 0) +
        (if partition.repr sheet = sheet then 1 else 0) =
      (if (resolution (partition.repr sheet)).left.repr sheet = sheet then 1 else 0) +
        (if (resolution (partition.repr sheet)).right.repr sheet = sheet then 1 else 0)
  rcases hStar (partition.repr sheet) with ⟨hLeft, hNew⟩ | ⟨hRight, hNew⟩
  · rw [hLeft, hNew, Nat.add_comm]
  · rw [hRight, hNew]

/-- A blockwise Euler identity assembles to the pasted one.  This is the
weakening of `paste_block_euler` that a non-star resolution needs: only the
three induced block counts on each wall block are compared, not the canonical
representatives sheet by sheet.

Its first user is `W3ShiftSourceCandidates`, whose Position II.b local
resolution (in the sense of Part I) is not a star.  It is stated here because
`ResolutionAssembly`'s own import closure reaches neither
`Infrastructure.Change` (for `SheetPartition.card_blocks_eq_sum_blockCountWithin`)
nor `BalancedGlobal` (needed by `candidate_sourceGenus_of_blockwise_euler`
below), while this file reaches both. -/
theorem paste_block_euler_of_counts (wallPartition : SheetPartition degree)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wallPartition)
    (hEuler : ∀ anchor, wallPartition.repr anchor = anchor →
      (resolution anchor).newEdge.blockCountWithin wallPartition anchor + 1 =
        (resolution anchor).left.blockCountWithin wallPartition anchor +
          (resolution anchor).right.blockCountWithin wallPartition anchor) :
    Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).newEdge.Blocks +
        Fintype.card wallPartition.Blocks =
      Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).left.Blocks +
        Fintype.card
          (LocalResolution.paste wallPartition resolution hContracts).right.Blocks := by
  classical
  have hNewRefines :
      (LocalResolution.paste wallPartition resolution hContracts).newEdge.Refines
        wallPartition :=
    (LocalResolution.pasteNewEdge_refines_left wallPartition resolution hContracts).trans
      (LocalResolution.pasteLeft_refines wallPartition resolution hContracts)
  have hLeftRefines :
      (LocalResolution.paste wallPartition resolution hContracts).left.Refines
        wallPartition :=
    LocalResolution.pasteLeft_refines wallPartition resolution hContracts
  have hRightRefines :
      (LocalResolution.paste wallPartition resolution hContracts).right.Refines
        wallPartition :=
    LocalResolution.pasteRight_refines wallPartition resolution hContracts
  rw [SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hNewRefines,
    SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hLeftRefines,
    SheetPartition.card_blocks_eq_sum_blockCountWithin _ wallPartition hRightRefines]
  have hCard : Fintype.card wallPartition.Blocks = ∑ _block : wallPartition.Blocks, 1 := by
    simp
  rw [hCard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro block _
  rw [LocalResolution.pasteNewEdge_blockCountWithin, LocalResolution.pasteLeft_blockCountWithin,
    LocalResolution.pasteRight_blockCountWithin, block.2]
  exact hEuler block.1 block.2

/-- A literal candidate assembled from such stars preserves source genus. -/
theorem candidate_sourceGenus_of_stars (candidate : BalancedGlobal.Candidate target degree data wall)
    (hStar : ∀ anchor,
      ((candidate.resolution anchor).left = data.vertexPartition wall ∧
        (candidate.resolution anchor).newEdge = (candidate.resolution anchor).right) ∨
      ((candidate.resolution anchor).right = data.vertexPartition wall ∧
        (candidate.resolution anchor).newEdge = (candidate.resolution anchor).left)) :
    genus candidate.datum.sourceGraph = genus data.sourceGraph := by
  apply (GlobalResolution.sourceGraph_genus_eq_iff_block_card data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)).mpr
  exact paste_block_euler _ _ _ hStar

/-- A candidate whose blockwise Euler defect vanishes preserves source genus.

Stated here, alongside `paste_block_euler_of_counts` above, for the same
reason: `ResolutionAssembly` does not reach `BalancedGlobal`. -/
theorem candidate_sourceGenus_of_blockwise_euler
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hEuler : ∀ anchor, (data.vertexPartition wall).repr anchor = anchor →
      (candidate.resolution anchor).newEdge.blockCountWithin
            (data.vertexPartition wall) anchor + 1 =
        (candidate.resolution anchor).left.blockCountWithin
            (data.vertexPartition wall) anchor +
          (candidate.resolution anchor).right.blockCountWithin
            (data.vertexPartition wall) anchor) :
    genus candidate.datum.sourceGraph = genus data.sourceGraph := by
  apply (GlobalResolution.sourceGraph_genus_eq_iff_block_card data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)).mpr
  exact paste_block_euler_of_counts _ _ _ hEuler

theorem firstSplit_sourceGenus (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    genus (firstSplitPattern input profile hCard).candidate.datum.sourceGraph =
      genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (firstSplitPattern input profile hCard).candidate.resolution anchor =
    LocalResolution.onBlock (data.vertexPartition wall) block.1
      (splitResolutionAt (data.vertexPartition wall) block.1)
      (backgroundResolution (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel block.1 anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

theorem joined_sourceGenus (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    genus (joinedPattern data star block hCard).candidate.datum.sourceGraph =
      genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (joinedPattern data star block hCard).candidate.resolution anchor =
    LocalResolution.onBlock (data.vertexPartition wall) block.1
      (joinedResolutionAt (data.vertexPartition wall))
      (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  simp only [LocalResolution.onBlock, ite_self]
  exact Or.inl ⟨rfl, rfl⟩

/-- Remote sheet transport is an equivalence of the source graph, not just
an equality of its local wall data. -/
theorem swappedDatum_sourceGenus {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    genus (swappedDatum profile hCard).sourceGraph = genus data.sourceGraph := by
  exact (wallBranchSwap data wall (branchRoot star profile.doubleLabel)
    (branchRoot_ne star profile.doubleLabel) block.1 (otherSheet block hCard)
    (otherSheet_spec block hCard).1).sourceGraphLaplacianEquiv.genus_eq

theorem secondSplit_sourceGenus (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    genus (secondSplitPattern input profile hCard).candidate.datum.sourceGraph =
      genus data.sourceGraph := by
  trans genus (swappedDatum profile hCard).sourceGraph
  · apply candidate_sourceGenus_of_stars
    intro anchor
    have hResolution : (secondSplitPattern input profile hCard).candidate.resolution anchor =
      LocalResolution.onBlock ((swappedDatum profile hCard).vertexPartition wall) block.1
        (splitResolutionAt ((swappedDatum profile hCard).vertexPartition wall) block.1)
        (backgroundResolution ((swappedDatum profile hCard).vertexPartition wall)) anchor := rfl
    rw [hResolution]
    by_cases hSelected : ((swappedDatum profile hCard).vertexPartition wall).Rel block.1 anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
      exact Or.inr ⟨rfl, rfl⟩
  · exact swappedDatum_sourceGenus profile hCard

/-- Every actual member of the source-derived universal M11 family has the
same source genus as the contracted datum. -/
theorem candidates_sourceGenus (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (position : Fin 3) :
    genus (M11RemoteCandidates.candidates input profile hCard position).datum.sourceGraph =
      genus data.sourceGraph := by
  fin_cases position
  · exact firstSplit_sourceGenus input profile hCard
  · exact secondSplit_sourceGenus input profile hCard
  · exact joined_sourceGenus data star block hCard

end DraismaVargas.LocalCases.M11SourceGenus
