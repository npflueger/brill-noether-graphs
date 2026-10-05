module

public import DraismaVargas.LocalCases.M11RemoteSurvival
public import DraismaVargas.LocalCases.M11BranchSeparation
public import DraismaVargas.LocalCases.StableSourceMatrix

@[expose] public section

/-!
# The remote M11 split's literal new length column

The two distinguished unit-index arms survive and belong to the natural
retained double-direction row identified after the remote branch swap.
Every other new arm is dangling. Counting the actual source occurrences gives
coefficient two on that row and zero on every other natural stable row.

The final theorem uses target-tree branch separation to name that occurrence
as the transported original `e2`. A complete common-row labelling, the
comparison of retained columns, and the cofactor balance are not treated here.
-/

namespace DraismaVargas.LocalCases.M11RemoteColumn

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11RemoteCandidates M11SplitRows M11RemoteSurvival M11RemotePruning M11BranchSeparation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

theorem secondSplit_newSourceEdge_sheet (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet).1.2 = sheet := by
  let candidate := (secondSplitPattern input profile hCard).candidate
  let partition := (ResolutionM11.LocalResolution.paste ((swappedDatum profile hCard).vertexPartition wall)
    candidate.resolution candidate.contracts).newEdge
  have hOne : partition.blockCard sheet = 1 :=
    (candidate.sourceEdgeIndex_newSourceEdge sheet).symm.trans (secondSplit_newSourceEdge_index input profile hCard sheet)
  have hMem : partition.repr sheet ∈ partition.block sheet :=
    (partition.mem_block_iff sheet (partition.repr sheet)).mpr (partition.rel_repr_right sheet)
  rw [partition.block_eq_singleton_of_blockCard_eq_one sheet hOne, Finset.mem_singleton] at hMem
  exact hMem

theorem secondSplit_newSourceEdge_injective (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Injective (secondSplitPattern input profile hCard).candidate.newSourceEdge := by
  intro first second hEqual
  exact (secondSplit_newSourceEdge_sheet input profile hCard first).symm.trans
    ((congrArg (fun edge ↦ edge.1.2) hEqual).trans (secondSplit_newSourceEdge_sheet input profile hCard second))

/-- Exact occurrence census on every natural stable row of the second split. -/
theorem secondSplit_new_occurrences (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (secondSplitPattern input profile hCard).candidate.datum) :
    StableSourceMatrix.occurrences (secondSplitPattern input profile hCard).candidate.datum path
      (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right none) =
      if path = (secondSplit_retainedDouble input profile hCard).stablePath then
        ((data.vertexPartition wall).block block.1).image (secondSplitPattern input profile hCard).candidate.newSourceEdge
      else ∅ := by
  classical
  let candidate := (secondSplitPattern input profile hCard).candidate
  ext edge
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hEqual := eq_newSourceEdge_of_target candidate edge hTarget
    have hNewSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge edge.1.2) := hEqual ▸ hSurvives
    have hRel := (secondSplit_new_survives_iff input profile hCard edge.1.2).mp hNewSurvives
    have hTyped : (⟨edge, hSurvives⟩ : NonDanglingEdge candidate.datum) =
        ⟨candidate.newSourceEdge edge.1.2, hNewSurvives⟩ := Subtype.ext hEqual
    have hPath : (secondSplit_retainedDouble input profile hCard).stablePath = path :=
      (secondSplit_new_stablePath_eq_retained input profile hCard edge.1.2 hRel).symm.trans
        ((congrArg NonDanglingEdge.stablePath hTyped).symm.trans hRow)
    rw [ite_eq_left hPath.symm]
    exact Finset.mem_image.mpr ⟨edge.1.2, ((data.vertexPartition wall).mem_block_iff _ _).mpr hRel, hEqual.symm⟩
  · intro hEdge
    split_ifs at hEdge with hPath
    · obtain ⟨sheet, hSheet, rfl⟩ := Finset.mem_image.mp hEdge
      have hRel := ((data.vertexPartition wall).mem_block_iff _ _).mp hSheet
      exact ⟨⟨secondSplit_new_survives input profile hCard sheet hRel,
        (secondSplit_new_stablePath_eq_retained input profile hCard sheet hRel).trans hPath.symm⟩, rfl⟩
    · exact (Finset.notMem_empty edge hEdge).elim

/-- Coefficient two on the actual retained row, zero on all other rows.
No matrix entries or stable-row enumeration are supplied as hypotheses. -/
theorem secondSplit_matrix_new_column (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (secondSplitPattern input profile hCard).candidate.datum) :
    StableSourceMatrix.matrix (secondSplitPattern input profile hCard).candidate.datum path
      (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right none) =
      if path = (secondSplit_retainedDouble input profile hCard).stablePath then 2 else 0 := by
  classical
  rw [StableSourceMatrix.matrix, secondSplit_new_occurrences input profile hCard path]
  split_ifs
  · have hImageCard :
        (((data.vertexPartition wall).block block.1).image
          (secondSplitPattern input profile hCard).candidate.newSourceEdge).card = 2 :=
      (Finset.card_image_of_injective _ (secondSplit_newSourceEdge_injective input profile hCard)).trans hCard
    calc
      _ = ∑ _edge ∈ ((data.vertexPartition wall).block block.1).image
          (secondSplitPattern input profile hCard).candidate.newSourceEdge, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro edge hEdge
        obtain ⟨sheet, _, rfl⟩ := Finset.mem_image.mp hEdge
        rw [secondSplit_newSourceEdge_index]
        norm_num
      _ = 2 := by simp [hImageCard]
  · exact Finset.sum_empty

/-- The actual second-split image of the original opposite double occurrence.
The target-tree assumptions justify its equality with the natural retained
row found above; they do not assert a full stable-row bijection. -/
noncomputable def secondSplit_oppositeDouble
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (secondSplitPattern input profile hCard).candidate.datum :=
  ⟨(secondSplitPattern input profile hCard).candidate.oldSourceEdge
      ((branchRelabeling profile hCard).sourceEdgeEquiv (oppositeDouble profile hCard).1), by
    have hEqual := congrArg (secondSplitPattern input profile hCard).candidate.oldSourceEdge
      (swapped_retainedDouble_eq hConnected hGenus profile hCard)
    exact hEqual ▸ (secondSplit_retainedDouble input profile hCard).2⟩

theorem secondSplit_retainedDouble_eq_oppositeDouble
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    secondSplit_retainedDouble input profile hCard =
      secondSplit_oppositeDouble hConnected hGenus input profile hCard :=
  Subtype.ext (congrArg (secondSplitPattern input profile hCard).candidate.oldSourceEdge
    (swapped_retainedDouble_eq hConnected hGenus profile hCard))

/-- The coefficient-two column on the stable class of the transported
original `e2` occurrence. This is a literal natural-source-matrix statement. -/
theorem secondSplit_matrix_new_column_original
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath (secondSplitPattern input profile hCard).candidate.datum) :
    StableSourceMatrix.matrix (secondSplitPattern input profile hCard).candidate.datum path
      (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right none) =
      if path = (secondSplit_oppositeDouble hConnected hGenus input profile hCard).stablePath then 2 else 0 := by
  rw [secondSplit_matrix_new_column,
    secondSplit_retainedDouble_eq_oppositeDouble hConnected hGenus input profile hCard]

end DraismaVargas.LocalCases.M11RemoteColumn
