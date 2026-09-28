import DraismaVargasCount.InheritedLimitRows

/-!
# Inherited branch labels at positive-request limits

The literal source contraction maps every incoming branch to a limit branch.
At a merged fibre the forest Euler formula says that the limit valency is two
plus the number of branch constituents; metric separation bounds that number
by one. Away from the merge the source map and surviving valency are unchanged.
Thus every limit branch has exactly one incoming branch, giving `branchEquiv`
and inherited `branchLabel` without a graph identification receipt.

This module does not prove per-row incidence multiplicity preservation.
Combining `branchLabel` with `InheritedLimitRows.rowLabel` into a genuine
`CoreIdentification` requires that additional theorem, especially for rows
whose two incidences lie at the same branch. No such compatibility is assumed
or silently packaged here.
-/

namespace DraismaVargas.Count.InheritedLimitBranches
open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource
open PrunedFibreValency PrunedFibreTree PrunedContractionFibre FullContractionFibre
open StableGraphIncidence InheritedLimitRows SegmentWalls WallStar
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)

noncomputable def vertexMap : w.frame.data.SourceVertex → w.limit.SourceVertex :=
  sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)

noncomputable def branchFibre (v : w.limit.SourceVertex) : Finset w.frame.data.SourceVertex := by
  classical
  exact (activeFibreVertices w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) v).filter
    (fun u ↦ nonDanglingValency w.frame.data u = 3)

theorem mem_branchFibre (v : w.limit.SourceVertex) (u : w.frame.data.SourceVertex) :
    u ∈ branchFibre w v ↔ vertexMap w u = v ∧ nonDanglingValency w.frame.data u = 3 := by
  classical
  rw [branchFibre, Finset.mem_filter]
  have hm := mem_activeFibreVertices w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) v u
  constructor
  · exact fun h ↦ ⟨(hm.mp h.1).1,h.2⟩
  · exact fun h ↦ ⟨hm.mpr ⟨h.1,by omega⟩,h.2⟩

theorem exists_mergedBlock (v : w.limit.SourceVertex)
    (hv : v.1.1 = ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
      fst_ne_snd (w.frame.edgeOf w.column)⟩) :
    ∃ block, mergedVertex w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) block = v := by
  let block : (mergedPartition w.frame.data
      (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1
      (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks :=
    ⟨v.1.2, by
      have h := v.2
      change (w.limit.vertexPartition v.1.1).repr v.1.2 = v.1.2 at h
      rw [hv] at h
      change ((contractDatum w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column)).vertexPartition _).repr _ = _ at h
      rw [contractDatum_vertexPartition_merge] at h
      exact h⟩
  exact ⟨block, Subtype.ext (Prod.ext hv.symm rfl)⟩

include hy in
theorem branchFibre_card_add_two (v : w.limit.SourceVertex)
    (hv : v.1.1 = ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
      fst_ne_snd (w.frame.edgeOf w.column)⟩)
    (hNonzero : nonDanglingValency w.limit v ≠ 0) :
    nonDanglingValency w.limit v = (branchFibre w v).card + 2 := by
  obtain ⟨block,rfl⟩ := exists_mergedBlock w v hv
  exact WallAdmissibilityStable.nonDanglingValency_mergedVertex_eq_card_branch_add_two
    w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    (danglingCompatible w hy) (forest w hy) w.frame.fullDim.trivalent
    (NonDanglingValency.nonDanglingValency_ne_one _ w.frame.fullDim.connected) block hNonzero

include hy in
theorem limit_trivalent (v : w.limit.SourceVertex) :
    nonDanglingValency w.limit v ≤ 3 := by
  obtain ⟨u,rfl⟩ := sourceVertexMap_surjective w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) v
  by_cases ha : u.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 ∨
      u.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
  · have hv : (vertexMap w u).1.1 =
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩ :=
      fold_eq_of_eq_or _ ha
    obtain ⟨block,hblock⟩ := exists_mergedBlock w (vertexMap w u) hv
    change nonDanglingValency w.limit (vertexMap w u) ≤ 3
    rw [← hblock]
    exact WallAdmissibilityStable.nonDanglingValency_mergedVertex_le_three
      w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      (WallAdmissibilityStable.exists_stablePath_eq_target_ne w.frame.fullDim.labelling
        (w.frame.coordsAt y) (rows_ne_zero w hy) (zero_coordinate w))
      (danglingCompatible w hy) (forest w hy) w.frame.fullDim.trivalent
      (NonDanglingValency.nonDanglingValency_ne_one _ w.frame.fullDim.connected) block
  · exact (nonDanglingValency_sourceVertexMap w.frame.data (danglingCompatible w hy) u
      (fun h ↦ ha (Or.inl h)) (fun h ↦ ha (Or.inr h))).le.trans
      (w.frame.fullDim.trivalent u)

include hy in
theorem branch_maps_to_branch (v : BranchVertex w.frame.data) :
    3 ≤ nonDanglingValency w.limit (vertexMap w v.1) := by
  have hThree : nonDanglingValency w.frame.data v.1 = 3 :=
    le_antisymm (w.frame.fullDim.trivalent v.1) v.2
  by_cases ha : v.1.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 ∨
      v.1.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
  · have hv : (vertexMap w v.1).1.1 =
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩ :=
      fold_eq_of_eq_or _ ha
    obtain ⟨block,hblock⟩ := exists_mergedBlock w (vertexMap w v.1) hv
    have hMem : v.1 ∈ activeFibreVertices w.frame.data rfl
        (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
        (mergedVertex w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column) block) := by
      rw [mem_activeFibreVertices, hblock]
      exact ⟨rfl,by omega⟩
    have hTwo := WallAdmissibilityStable.two_le_nonDanglingValency_mergedVertex
      w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      (danglingCompatible w hy) (forest w hy)
      (NonDanglingValency.nonDanglingValency_ne_one _ w.frame.fullDim.connected) block ⟨v.1,hMem⟩
    rw [hblock] at hTwo
    change 2 ≤ nonDanglingValency w.limit (vertexMap w v.1) at hTwo
    have heq := branchFibre_card_add_two w hy (vertexMap w v.1) hv (by omega)
    have hPos : 0 < (branchFibre w (vertexMap w v.1)).card :=
      Finset.card_pos.mpr ⟨v.1, (mem_branchFibre w _ _).mpr ⟨rfl,hThree⟩⟩
    omega
  · exact v.2.trans (nonDanglingValency_sourceVertexMap w.frame.data (danglingCompatible w hy) v.1
      (fun h ↦ ha (Or.inl h)) (fun h ↦ ha (Or.inr h))).ge


include hy in
theorem branchFibre_card_eq_one (v : BranchVertex w.limit) :
    (branchFibre w v.1).card = 1 := by
  classical
  by_cases hv : v.1.1.1 =
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩
  · have hThree := le_antisymm (limit_trivalent w hy v.1) v.2
    have heq := branchFibre_card_add_two w hy v.1 hv (by omega)
    omega
  · obtain ⟨u,hu⟩ := sourceVertexMap_surjective w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) v.1
    have hAway : ¬ (u.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 ∨
        u.1.1 = (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2) := by
      intro h
      apply hv
      exact (congrArg (fun vertex : w.limit.SourceVertex ↦ vertex.1.1) hu).symm.trans
        (fold_eq_of_eq_or _ h)
    have hVal := nonDanglingValency_sourceVertexMap w.frame.data (danglingCompatible w hy) u
      (fun h ↦ hAway (Or.inl h)) (fun h ↦ hAway (Or.inr h))
    have hThree : nonDanglingValency w.frame.data u = 3 := by
      have hBranch : 3 ≤ nonDanglingValency w.frame.data u := by
        have hm : vertexMap w u = v.1 := hu
        have : 3 ≤ nonDanglingValency w.limit (vertexMap w u) := by
          rw [hm]
          exact v.2
        exact this.trans hVal.le
      exact le_antisymm (w.frame.fullDim.trivalent u) hBranch
    have hfibre : branchFibre w v.1 = {u} := by
      ext z
      rw [mem_branchFibre, Finset.mem_singleton]
      constructor
      · intro hz
        exact ((sourceVertexMap_eq_iff_of_ne w.frame.data rfl
          (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) u z
          (fun h ↦ hAway (Or.inl h)) (fun h ↦ hAway (Or.inr h))).mp
            (hu.trans hz.1.symm)).symm
      · rintro rfl
        exact ⟨hu,hThree⟩
    rw [hfibre, Finset.card_singleton]

noncomputable def branchMap (v : BranchVertex w.frame.data) : BranchVertex w.limit :=
  ⟨vertexMap w v.1, branch_maps_to_branch w hy v⟩

theorem branchMap_injective : Function.Injective (branchMap w hy) := by
  intro u v h
  have hm : vertexMap w u.1 = vertexMap w v.1 := congrArg Subtype.val h
  apply Subtype.ext
  have hu : u.1 ∈ branchFibre w (branchMap w hy u).1 :=
    (mem_branchFibre w _ _).mpr
      ⟨rfl,le_antisymm (w.frame.fullDim.trivalent u.1) u.2⟩
  have hv : v.1 ∈ branchFibre w (branchMap w hy u).1 :=
    (mem_branchFibre w _ _).mpr
      ⟨hm.symm,le_antisymm (w.frame.fullDim.trivalent v.1) v.2⟩
  exact Finset.card_le_one.mp (le_of_eq (branchFibre_card_eq_one w hy (branchMap w hy u))) _ hu _ hv

theorem branchMap_surjective : Function.Surjective (branchMap w hy) := by
  intro v
  have hPos : 0 < (branchFibre w v.1).card := by rw [branchFibre_card_eq_one w hy v]; omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hPos
  obtain ⟨hmap,hThree⟩ := (mem_branchFibre w _ _).mp hu
  exact ⟨⟨u,by omega⟩,Subtype.ext hmap⟩

/-- The actual source contraction induces the surviving branch dictionary. -/
noncomputable def branchEquiv : BranchVertex w.frame.data ≃ BranchVertex w.limit :=
  Equiv.ofBijective (branchMap w hy) ⟨branchMap_injective w hy,branchMap_surjective w hy⟩

theorem branchEquiv_val (v : BranchVertex w.frame.data) :
    (branchEquiv w hy v).1 = vertexMap w v.1 := rfl

/-- The label inherited from the unique incoming branch constituent. -/
noncomputable def branchLabel : BranchVertex w.limit ≃ Fin n :=
  (branchEquiv w hy).symm.trans w.frame.ident.vertex

end DraismaVargas.Count.InheritedLimitBranches

