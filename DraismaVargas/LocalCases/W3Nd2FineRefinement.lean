import DraismaVargas.LocalCases.W3Nd2SourceCandidates

/-!
# Localized refinement for the true W3 nd2 fine member

This module identifies the third target direction in the actual Figure 31
source profile.  Above the distinguished wall block every occurrence in that
direction is dangling, hence has a singleton edge block.  Consequently that
edge partition refines the small-direction partition on the selected block.

The large survivor has index equal to the complete wall-block cardinality,
so its edge block is exactly the selected wall block.  All conclusions are
localized with `SheetPartition.RefinesOnBlock`; nothing is asserted about
unrelated background blocks.
-/

namespace DraismaVargas.LocalCases.W3Nd2FineRefinement

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

abbrev smallTarget (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : target.edges :=
  profile.small.1.1.1

abbrev largeTarget (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : target.edges :=
  profile.large.1.1.1

theorem smallTarget_mem (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    smallTarget input profile ∈ GluingDatum.incidentEdges wall :=
  ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
    profile.small.1).mp profile.small.2).1

theorem largeTarget_mem (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    largeTarget input profile ∈ GluingDatum.incidentEdges wall :=
  ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
    profile.large.1).mp profile.large.2).1

private theorem large_eq_rightFirst_or_rightSecond
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    largeTarget input profile = (orientedStar input profile).rightFirst ∨
      largeTarget input profile = (orientedStar input profile).rightSecond := by
  have hAt := ((incident_wallBlock_sourceVertex_iff data
    input.distinguishedBlock profile.large.1).mp profile.large.2).1
  rw [(orientedStar input profile).incidentEdges_eq] at hAt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
  rcases hAt with hSmall | hFirst | hSecond
  · exact (profile.target_ne hSmall.symm).elim
  · exact Or.inl hFirst
  · exact Or.inr hSecond

/-- The target occurrence in the third direction, distinct from the two
surviving directions in the actual nd2 profile. -/
noncomputable def thirdTarget (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : target.edges :=
  if largeTarget input profile = (orientedStar input profile).rightFirst then
    (orientedStar input profile).rightSecond
  else
    (orientedStar input profile).rightFirst

theorem thirdTarget_mem (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    thirdTarget input profile ∈ GluingDatum.incidentEdges wall := by
  by_cases hLarge : largeTarget input profile =
      (orientedStar input profile).rightFirst
  · simp only [thirdTarget, if_pos hLarge]
    rw [(orientedStar input profile).incidentEdges_eq]
    simp
  · simp only [thirdTarget, if_neg hLarge]
    rw [(orientedStar input profile).incidentEdges_eq]
    simp

theorem thirdTarget_ne_small (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    thirdTarget input profile ≠ smallTarget input profile := by
  by_cases hLarge : largeTarget input profile =
      (orientedStar input profile).rightFirst
  · simpa only [thirdTarget, if_pos hLarge, smallTarget] using
      (orientedStar input profile).rightSecond_ne_left
  · simpa only [thirdTarget, if_neg hLarge, smallTarget] using
      (orientedStar input profile).rightFirst_ne_left

theorem thirdTarget_ne_large (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    thirdTarget input profile ≠ largeTarget input profile := by
  by_cases hLarge : largeTarget input profile =
      (orientedStar input profile).rightFirst
  · simp only [thirdTarget, if_pos hLarge]
    intro hEq
    apply (orientedStar input profile).right_ne
    exact hLarge.symm.trans hEq.symm
  · simp only [thirdTarget, if_neg hLarge]
    intro hEq
    exact hLarge hEq.symm

theorem incidentEdges_eq (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    GluingDatum.incidentEdges wall =
      {smallTarget input profile, largeTarget input profile,
        thirdTarget input profile} := by
  by_cases hLarge : largeTarget input profile =
      (orientedStar input profile).rightFirst
  · rw [(orientedStar input profile).incidentEdges_eq]
    simp only [smallTarget, thirdTarget, if_pos hLarge]
    rw [hLarge]
  · rcases large_eq_rightFirst_or_rightSecond input profile with
      hFirst | hSecond
    · exact (hLarge hFirst).elim
    · rw [(orientedStar input profile).incidentEdges_eq]
      simp only [smallTarget, thirdTarget, if_neg hLarge]
      rw [hSecond, Finset.pair_comm]

/-- The canonical source occurrence in the third direction through a selected
sheet. -/
noncomputable abbrev thirdSourceEdge (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    data.SourceEdge :=
  data.sourceEdge (thirdTarget input profile) sheet

@[simp] theorem thirdSourceEdge_target (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    (thirdSourceEdge input profile sheet).1.1 = thirdTarget input profile := rfl

@[simp] theorem thirdSourceEdge_sheet (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    (thirdSourceEdge input profile sheet).1.2 =
      (data.edgePartition (thirdTarget input profile)).repr sheet := rfl

theorem thirdSourceEdge_incident (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Incident data (thirdSourceEdge input profile sheet)
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
  have hRefines := refines_of_mem_incidentEdges data (thirdTarget_mem input profile)
  have hEdgeRel := hRefines.rel
    ((data.edgePartition (thirdTarget input profile)).rel_repr_right sheet)
  apply (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock _).mpr
  refine ⟨thirdTarget_mem input profile, Subtype.ext ?_⟩
  exact hEdgeRel.symm.trans (hSheet.symm.trans input.distinguishedBlock.2)

theorem thirdSourceEdge_wallBlock (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    WallBlock.ofSheet data wall (thirdSourceEdge input profile sheet).1.2 =
      input.distinguishedBlock :=
  ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
    (thirdSourceEdge input profile sheet)).mp
      (thirdSourceEdge_incident input profile sheet hSheet)).2

theorem thirdSourceEdge_isDangling (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    IsDangling data (thirdSourceEdge input profile sheet) := by
  by_contra hSurvives
  let incident : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
    ⟨thirdSourceEdge input profile sheet,
      thirdSourceEdge_incident input profile sheet hSheet⟩
  have hMem : incident ∈ survivors data input.distinguishedBlock :=
    (mem_survivors data input.distinguishedBlock incident).mpr hSurvives
  rw [profile.surviving] at hMem
  rcases Finset.mem_insert.mp hMem with hSmall | hLarge
  · have hTarget := congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ edge.1.1.1)
      hSmall
    exact thirdTarget_ne_small input profile hTarget
  · have hTarget := congrArg (fun edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ edge.1.1.1)
      (Finset.mem_singleton.mp hLarge)
    exact thirdTarget_ne_large input profile hTarget

theorem thirdSourceEdge_index_eq_one (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    data.sourceEdgeIndex (thirdSourceEdge input profile sheet) = 1 :=
  input.dangling_no_glue _
    (thirdSourceEdge_isDangling input profile sheet hSheet)

theorem third_blockCard_eq_one (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCard sheet = 1 := by
  rw [← GluingDatum.sourceEdgeIndex_sourceEdge data
    (thirdTarget input profile) sheet]
  exact thirdSourceEdge_index_eq_one input profile sheet hSheet

/-- The third-direction partition is singleton-refined on the distinguished
wall block. -/
theorem third_refinesOnBlock_splitBlock (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (thirdTarget input profile)).RefinesOnBlock
      ((data.vertexPartition wall).splitBlock input.distinguishedBlock.1)
      (data.vertexPartition wall)
      input.distinguishedBlock.1 := by
  intro first second hFirst hThird
  have hSingleton :=
    (data.edgePartition (thirdTarget input profile)).block_eq_singleton_of_blockCard_eq_one
      first (third_blockCard_eq_one input profile first hFirst)
  have hMember :=
    ((data.edgePartition (thirdTarget input profile)).mem_block_iff first second).mpr
      hThird
  rw [hSingleton, Finset.mem_singleton] at hMember
  subst second
  rfl

/-- The singleton third-direction blocks refine the small-direction partition
on the distinguished wall block. -/
theorem third_refinesOnBlock_fine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (thirdTarget input profile)).RefinesOnBlock
      (finePartition input profile) (data.vertexPartition wall)
      input.distinguishedBlock.1 :=
  (third_refinesOnBlock_splitBlock input profile).refinesAny_of_splitBlock _

/-- Exact third-direction contribution at the selected fine endpoint: one
induced edge block for each sheet of the small-direction block. -/
theorem third_blockCountWithin_fine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCountWithin
        (finePartition input profile) sheet =
      (finePartition input profile).blockCard sheet :=
  SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (thirdTarget input profile))
    (finePartition input profile) (data.vertexPartition wall)
    input.distinguishedBlock.1 sheet
    (third_refinesOnBlock_splitBlock input profile)
    (fine_refines_wall input profile) hSheet

/-- The small direction is literally the selected fine partition. -/
theorem small_refinesOnBlock_fine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (smallTarget input profile)).RefinesOnBlock
      (finePartition input profile) (data.vertexPartition wall)
      input.distinguishedBlock.1 :=
  (SheetPartition.Refines.refl (finePartition input profile)).refinesOnBlock _

/-- The large-direction edge partition has the ordinary edge-to-wall
refinement, stated in the same selected-block interface as the other two
directions. -/
theorem large_refinesOnBlock_wall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (largeTarget input profile)).RefinesOnBlock
      (data.vertexPartition wall) (data.vertexPartition wall)
      input.distinguishedBlock.1 :=
  (refines_of_mem_incidentEdges data (largeTarget_mem input profile)).refinesOnBlock _

/-- The large-direction edge block through its source representative occupies
the complete distinguished wall block. -/
theorem large_block_eq_wall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (largeTarget input profile)).block profile.large.1.1.2 =
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
  let fine := data.edgePartition (largeTarget input profile)
  let coarse := data.vertexPartition wall
  let largeSheet := profile.large.1.1.2
  have hAt := ((incident_wallBlock_sourceVertex_iff data
    input.distinguishedBlock profile.large.1).mp profile.large.2).1
  have hRefines : fine.Refines coarse := refines_of_mem_incidentEdges data hAt
  have hLargeWall : coarse.Rel input.distinguishedBlock.1 largeSheet := by
    have hBlock := ((incident_wallBlock_sourceVertex_iff data
      input.distinguishedBlock profile.large.1).mp profile.large.2).2
    have hValue := congrArg Subtype.val hBlock
    change coarse.repr largeSheet = input.distinguishedBlock.1 at hValue
    change coarse.repr input.distinguishedBlock.1 = coarse.repr largeSheet
    rw [input.distinguishedBlock.2, hValue]
  have hSubset : fine.block largeSheet ⊆
      coarse.block input.distinguishedBlock.1 := by
    intro sheet hSheet
    have hFineRel := (fine.mem_block_iff largeSheet sheet).mp hSheet
    exact (coarse.mem_block_iff input.distinguishedBlock.1 sheet).mpr
      (hLargeWall.trans (hRefines.rel hFineRel))
  apply Finset.eq_of_subset_of_card_le hSubset
  have hCard : fine.blockCard largeSheet =
      coarse.blockCard input.distinguishedBlock.1 := by
    exact profile.large_index
  exact Nat.le_of_eq hCard.symm

/-- Every selected sheet lies in the large survivor's complete edge block. -/
theorem large_rel_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (largeTarget input profile)).Rel
      profile.large.1.1.2 sheet := by
  apply (data.edgePartition (largeTarget input profile)).mem_block_iff _ _ |>.mp
  rw [large_block_eq_wall input profile]
  exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hSheet

/-- On the selected wall block, the wall partition also refines the actual
large-direction edge partition.  Together with ordinary edge-to-vertex
refinement this says that the two partitions coincide locally. -/
theorem wall_refinesOnBlock_large (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.vertexPartition wall).RefinesOnBlock
      (data.edgePartition (largeTarget input profile))
      (data.vertexPartition wall) input.distinguishedBlock.1 := by
  intro first second hFirst hWall
  have hLargeFirst := large_rel_of_wall_rel input profile first hFirst
  have hSecond : (data.vertexPartition wall).Rel input.distinguishedBlock.1 second :=
    hFirst.trans hWall
  have hLargeSecond := large_rel_of_wall_rel input profile second hSecond
  exact hLargeFirst.symm.trans hLargeSecond

end DraismaVargas.LocalCases.W3Nd2FineRefinement
