import DraismaVargas.LocalCases.M11SplitSurvival
import DraismaVargas.LocalCases.StableSourceMatrix

/-!
# The first M11 split's literal new length column

The first split of Figure 32 of Draisma--Vargas Part I (Case
`{w2-r2-nd3-M-11}`) contributes twice its new target length to the
retained double-direction edge on the deleted occurrence's sheet, and zero
to every other stable row. The new fibre is counted from actual surviving
occurrences, not a supplied matrix or stable-row enumeration.
-/

namespace DraismaVargas.LocalCases.M11SplitColumn

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitRows M11SplitSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- Unit new-edge blocks have the sheet itself as canonical representative.
Thus different sheets really give distinct new source occurrences. -/
theorem firstSplit_newSourceEdge_sheet (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet).1.2 = sheet := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let partition := (ResolutionM11.LocalResolution.paste (data.vertexPartition wall)
    candidate.resolution candidate.contracts).newEdge
  have hOne : partition.blockCard sheet = 1 :=
    (candidate.sourceEdgeIndex_newSourceEdge sheet).symm.trans (firstSplit_newSourceEdge_index input profile hCard sheet)
  have hMem : partition.repr sheet ∈ partition.block sheet :=
    (partition.mem_block_iff sheet (partition.repr sheet)).mpr (partition.rel_repr_right sheet)
  rw [partition.block_eq_singleton_of_blockCard_eq_one sheet hOne, Finset.mem_singleton] at hMem
  exact hMem

theorem firstSplit_newSourceEdge_injective (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Injective (firstSplitPattern input profile hCard).candidate.newSourceEdge := by
  intro first second hEqual
  exact (firstSplit_newSourceEdge_sheet input profile hCard first).symm.trans
    ((congrArg (fun edge ↦ edge.1.2) hEqual).trans (firstSplit_newSourceEdge_sheet input profile hCard second))

/-- The new occurrences on any actual stable row are precisely the image of
the distinguished two-sheet block on the retained row, and empty otherwise. -/
theorem firstSplit_new_occurrences (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (firstSplitPattern input profile hCard).candidate.datum) :
    StableSourceMatrix.occurrences (firstSplitPattern input profile hCard).candidate.datum path
      (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right none) =
      if path = (firstSplit_retainedDouble input profile hCard).stablePath then
        ((data.vertexPartition wall).block block.1).image (firstSplitPattern input profile hCard).candidate.newSourceEdge
      else ∅ := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  ext edge
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hEqual := eq_newSourceEdge_of_target candidate edge hTarget
    have hNewSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := hEqual ▸ hSurvives
    have hRel := (firstSplit_new_survives_iff input profile hCard edge.1.2).mp hNewSurvives
    have hTyped : (⟨edge, hSurvives⟩ : NonDanglingEdge candidate.datum) =
        ⟨candidate.newSourceEdge edge.1.2, hNewSurvives⟩ := Subtype.ext hEqual
    have hPath : (firstSplit_retainedDouble input profile hCard).stablePath = path :=
      (firstSplit_new_stablePath_eq_retained input profile hCard edge.1.2 hRel).symm.trans
        ((congrArg NonDanglingEdge.stablePath hTyped).symm.trans hRow)
    rw [if_pos hPath.symm]
    exact Finset.mem_image.mpr ⟨edge.1.2, ((data.vertexPartition wall).mem_block_iff _ _).mpr hRel, hEqual.symm⟩
  · intro hEdge
    split_ifs at hEdge with hPath
    · obtain ⟨sheet, hSheet, rfl⟩ := Finset.mem_image.mp hEdge
      have hRel := ((data.vertexPartition wall).mem_block_iff _ _).mp hSheet
      exact ⟨⟨firstSplit_new_survives input profile hCard sheet hRel,
        (firstSplit_new_stablePath_eq_retained input profile hCard sheet hRel).trans hPath.symm⟩, rfl⟩
    · exact (Finset.notMem_empty edge hEdge).elim

/-- Figure 32's coefficient two on the actual first-split stable-source
matrix. The retained row is geometrically identified; no matrix receipt is
assumed, and the statement covers every natural stable row. -/
theorem firstSplit_matrix_new_column (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (firstSplitPattern input profile hCard).candidate.datum) :
    StableSourceMatrix.matrix (firstSplitPattern input profile hCard).candidate.datum path
      (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right none) =
      if path = (firstSplit_retainedDouble input profile hCard).stablePath then 2 else 0 := by
  classical
  rw [StableSourceMatrix.matrix, firstSplit_new_occurrences input profile hCard path]
  split_ifs
  · have hImageCard :
        (((data.vertexPartition wall).block block.1).image
          (firstSplitPattern input profile hCard).candidate.newSourceEdge).card = 2 :=
      (Finset.card_image_of_injective _ (firstSplit_newSourceEdge_injective input profile hCard)).trans hCard
    calc
      _ = ∑ _edge ∈ ((data.vertexPartition wall).block block.1).image
          (firstSplitPattern input profile hCard).candidate.newSourceEdge, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro edge hEdge
        obtain ⟨sheet, _, rfl⟩ := Finset.mem_image.mp hEdge
        rw [firstSplit_newSourceEdge_index]
        norm_num
      _ = 2 := by simp [hImageCard]
  · exact Finset.sum_empty

end DraismaVargas.LocalCases.M11SplitColumn
