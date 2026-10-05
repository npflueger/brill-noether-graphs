module

public import DraismaVargasCount.StarMetricCompatibility
public import DraismaVargasCount.GeometricStableTransport
public import DraismaVargas.LocalCases.WallAdmissibilityStable
public import DraismaVargas.LocalCases.IncomingNormalizationRows

@[expose] public section

/-!
# Inherited rows and rectangular matrices at positive-request limits

For an actual `WallStar.Regrowth` whose fixed source request is positive, the
forest and dangling compatibility follow from its own full-dimensional
presentation and wall metric. The occurrence-level stable-path lift is
bijective by `WallAdmissibilityStable.stablePathLift_bijective`.
This provides `rowEquiv` and `rowLabel`, not merely equality of row counts.

The retained source occurrence embedding preserves indices and identifies
the row-filtered occurrence sets. Consequently `matrix_retained` identifies
the rectangular natural limit matrix with the retained incoming columns in
the fixed core-row order. A geometric limit isomorphism preserving these
actual inherited row labels therefore preserves those columns and, by the
incoming square matrix's nonsingularity, the limit metric.

This is the all-positive-source-row case, not the single-zero-source-row
facet theorem. It works also when a contracted leaf permits a return chain.
No forest, pruning, row equivalence, matrix agreement, or metric agreement is
assumed as an extra receipt. Preservation of inherited labels by a supplied
limit isomorphism is an explicit geometric condition, not proved for every
unlabelled datum isomorphism.

The branch-vertex/incidence dictionary of the limit is not constructed here
(inherited branch labels are in `InheritedLimitBranches`). Thus these results
provide actual inherited row labels, but do not package a full source-core
identification or alter either star quotient.
-/

namespace DraismaVargas.Count.InheritedLimitRows

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GluingContraction GraphContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource
open SegmentWalls WallStar
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)

include hy in
theorem rows_ne_zero (row : Fin p) :
    w.frame.matrix.mulVec (w.frame.coordsAt y) row ≠ 0 := by
  rw [w.frame.mulVec_coordsAt y]
  exact ne_of_gt (hy (w.frame.slot row))

theorem zero_coordinate :
    w.frame.coordsAt y
      (w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column)) = 0 := by
  simpa only [Frame.edgeOf, Equiv.symm_apply_apply] using w.degenerate.1

include hy in
theorem forest :
    ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1
      (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column) :=
  SourceFibreForest.contractionForest_of_fullDimensional w.frame.fullDim
    (w.frame.coordsAt y) w.degenerate.closed (rows_ne_zero w hy) rfl (zero_coordinate w)

include hy in
theorem danglingCompatible :
    DanglingCompatible w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) :=
  WallAdmissibility.danglingCompatible_of_fullDimensional w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    w.frame.fullDim (w.frame.coordsAt y) w.degenerate.closed (rows_ne_zero w hy) (zero_coordinate w)

/-- The actual retained-source occurrence embedding. -/
noncomputable def edgeEmbedding : w.limit.SourceEdge ↪ w.frame.data.SourceEdge :=
  sourceEdgeEmbedding w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)

theorem edgeEmbedding_target (edge : w.limit.SourceEdge) :
    (edgeEmbedding w edge).1.1 =
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) edge.1.1 :=
  congrArg Prod.fst (IncomingNormalizationRows.sourceEdgeEmbedding_val w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) edge)

theorem edgeEmbedding_index (edge : w.limit.SourceEdge) :
    w.frame.data.sourceEdgeIndex (edgeEmbedding w edge) = w.limit.sourceEdgeIndex edge :=
  sourceEdgeIndex_sourceEdgeEmbedding _ _ _ _ _

include hy in
theorem edgeEmbedding_dangling (edge : w.limit.SourceEdge) :
    IsDangling w.frame.data (edgeEmbedding w edge) ↔ IsDangling w.limit edge :=
  ⟨fun h ↦ (danglingCompatible w hy).1.embedding edge h,
    fun h ↦ (danglingCompatible w hy).2.embedding edge h⟩

/-- The row dictionary is the occurrence-level lift, not a choice from
equality of cardinalities. -/
noncomputable def rowEquiv : StablePath w.limit ≃ StablePath w.frame.data :=
  Equiv.ofBijective
    (PrunedFibreStablePath.stablePathLift w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      w.frame.fullDim.connected (danglingCompatible w hy) (forest w hy))
    (WallAdmissibilityStable.stablePathLift_bijective w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      (WallAdmissibilityStable.exists_stablePath_eq_target_ne w.frame.fullDim.labelling
        (w.frame.coordsAt y) (rows_ne_zero w hy) (zero_coordinate w))
      w.frame.fullDim.connected (danglingCompatible w hy) (forest w hy)
      w.frame.fullDim.trivalent
      (NonDanglingValency.nonDanglingValency_ne_one _ w.frame.fullDim.connected))

theorem rowEquiv_mk (edge : NonDanglingEdge w.limit) :
    rowEquiv w hy edge.stablePath =
      NonDanglingEdge.stablePath
        ⟨edgeEmbedding w edge.1, fun h ↦ edge.2 ((edgeEmbedding_dangling w hy edge.1).mp h)⟩ := rfl

/-- Each contracted row inherits the incoming row's fixed core slot. -/
noncomputable def rowLabel : StablePath w.limit ≃ Fin p :=
  (rowEquiv w hy).trans w.frame.ident.row


theorem unfoldEdge_injective :
    Function.Injective (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)) := by
  intro e f h
  apply (foldEdgeEquiv rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)).symm.injective
  exact Subtype.ext h

theorem mem_occurrences_embedding_iff (row : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) (edge : w.limit.SourceEdge) :
    edgeEmbedding w edge ∈ StableSourceMatrix.occurrences w.frame.data (rowEquiv w hy row)
      (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) place) ↔
    edge ∈ StableSourceMatrix.occurrences w.limit row place := by
  rw [StableSourceMatrix.mem_occurrences, StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives,hRow⟩, hTarget⟩
    have hs : ¬ IsDangling w.limit edge := fun h ↦
      hSurvives ((edgeEmbedding_dangling w hy edge).mpr h)
    refine ⟨⟨hs, ?_⟩, ?_⟩
    · apply (rowEquiv w hy).injective
      exact (rowEquiv_mk w hy ⟨edge, hs⟩).trans hRow
    · apply unfoldEdge_injective w
      rwa [edgeEmbedding_target] at hTarget
  · rintro ⟨⟨hSurvives,hRow⟩,hTarget⟩
    have hs : ¬ IsDangling w.frame.data (edgeEmbedding w edge) := fun h ↦
      hSurvives ((edgeEmbedding_dangling w hy edge).mp h)
    refine ⟨⟨hs, ?_⟩, ?_⟩
    · exact (rowEquiv_mk w hy ⟨edge,hSurvives⟩).symm.trans
        (congrArg (rowEquiv w hy) hRow)
    · rw [edgeEmbedding_target, hTarget]

theorem occurrences_image (row : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) :
    (StableSourceMatrix.occurrences w.limit row place).image (edgeEmbedding w) =
      StableSourceMatrix.occurrences w.frame.data (rowEquiv w hy row)
        (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column) place) := by
  classical
  ext edge
  constructor
  · intro h
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp h
    exact (mem_occurrences_embedding_iff w hy row place old).mpr hOld
  · intro h
    have ht := ((StableSourceMatrix.mem_occurrences _ _ _).mp h).2
    have hne : edge.1.1 ≠ w.frame.edgeOf w.column := by
      rw [ht]
      exact unfoldEdge_ne_contracted rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) place
    obtain ⟨old,hOld⟩ := exists_sourceEdgeEmbedding_eq w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) hne
    change edgeEmbedding w old = edge at hOld
    refine Finset.mem_image.mpr ⟨old, ?_, hOld⟩
    apply (mem_occurrences_embedding_iff w hy row place old).mp
    rwa [hOld]

/-- The contracted natural matrix is exactly the retained incoming matrix. -/
theorem matrix_unfoldEdge (row : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix w.limit row place =
      StableSourceMatrix.matrix w.frame.data (rowEquiv w hy row)
        (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column) place) := by
  classical
  unfold StableSourceMatrix.matrix
  rw [← occurrences_image w hy row place, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro edge _
    rw [edgeEmbedding_index]
  · exact fun _ _ _ _ h ↦ (edgeEmbedding w).injective h


theorem unfoldEdge_retainedColumns (c : {c : Fin p // c ≠ w.column}) :
    unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)
      (StarMetricCompatibility.retainedColumns w.frame w.column c) =
      w.frame.fullDim.labelling.targetEdge c.1 := by
  change ((foldEdgeEquiv rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)).symm
    ((foldEdgeEquiv rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)) _)).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Rectangular limit entries in inherited fixed-core row order. -/
theorem matrix_retained (slot : Fin p) (c : {c : Fin p // c ≠ w.column}) :
    StableSourceMatrix.matrix w.limit ((rowLabel w hy).symm slot)
      (StarMetricCompatibility.retainedColumns w.frame w.column c) =
      w.frame.matrix (w.frame.slot.symm slot) c.1 := by
  rw [matrix_unfoldEdge w hy, unfoldEdge_retainedColumns]
  unfold Frame.matrix
  rw [StableSourceMatrix.labelling_matrix_eq]
  congr 1
  simp [rowLabel, Frame.slot]

theorem limit_connected : w.limit.Connected :=
  GluingContraction.connected_contractDatum w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    w.frame.fullDim.connected


/-- The surviving-column dictionary carried by a geometric limit isomorphism. -/
noncomputable def limitColumns (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit) :
    {c : Fin p // c ≠ w.column} ≃ {c : Fin p // c ≠ w'.column} :=
  (StarMetricCompatibility.retainedColumns w.frame w.column).trans
    (iso.targetEdge.trans (StarMetricCompatibility.retainedColumns w'.frame w'.column).symm)

/-- An isomorphism preserving the actual inherited row labels forces equality
of retained member matrix entries. No matrix agreement receipt is assumed. -/
theorem matrix_retained_iso (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit)
    (hLabel : ∀ row : StablePath w.limit,
      rowLabel w' hy (iso.stablePathEquiv (limit_connected w) row) = rowLabel w hy row)
    (slot : Fin p) (c : {c : Fin p // c ≠ w.column}) :
    w'.frame.matrix (w'.frame.slot.symm slot) (limitColumns w w' iso c).1 =
      w.frame.matrix (w.frame.slot.symm slot) c.1 := by
  have hRow : iso.stablePathEquiv (limit_connected w) ((rowLabel w hy).symm slot) =
      (rowLabel w' hy).symm slot := by
    apply (rowLabel w' hy).injective
    rw [hLabel, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hCol : StarMetricCompatibility.retainedColumns w'.frame w'.column
      (limitColumns w w' iso c) =
      iso.targetEdge (StarMetricCompatibility.retainedColumns w.frame w.column c) := by
    simp [limitColumns]
  rw [← matrix_retained w' hy slot, ← matrix_retained w hy slot, ← hRow, hCol]
  exact iso.matrix_map (limit_connected w) _ _

/-- The strict retained-column condition `StarMetricCompatibility.RetainedColumnsAgree`
holds for a limit isomorphism preserving the actual inherited labels. -/
theorem retainedColumnsAgree_of_labelledIso (w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit)
    (hLabel : ∀ row : StablePath w.limit,
      rowLabel w' hy (iso.stablePathEquiv (limit_connected w) row) = rowLabel w hy row) :
    StarMetricCompatibility.RetainedColumnsAgree w w' iso := by
  intro r c
  have h := matrix_retained_iso w hy w' (GeometricDatumIso.ofStrict iso) hLabel
    (w.frame.slot r) c
  simpa only [Equiv.symm_apply_apply, limitColumns,
    StarMetricCompatibility.limitColumnEquiv, GeometricDatumIso.ofStrict] using h


/-- Extend the actual surviving-column dictionary over the collapsed coordinate. -/
noncomputable def allColumns (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit) : Fin p ≃ Fin p :=
  (Equiv.optionSubtypeNe w.column).symm.trans
    ((Equiv.optionCongr (limitColumns w w' iso)).trans
      (Equiv.optionSubtypeNe w'.column))

theorem allColumns_collapsed (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit) :
    allColumns w w' iso w.column = w'.column := by
  simp [allColumns]

theorem allColumns_retained (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit) (c : {c : Fin p // c ≠ w.column}) :
    allColumns w w' iso c.1 = (limitColumns w w' iso c).1 := by
  simp [allColumns, Equiv.optionSubtypeNe_symm_of_ne c.2]

/-- At the fixed positive source request, preserving actual inherited labels
forces preservation of the limit metric. -/
theorem limitLength_map_of_labelledIso (w' : Regrowth core y degree)
    (iso : GeometricDatumIso w.limit w'.limit)
    (hLabel : ∀ row : StablePath w.limit,
      rowLabel w' hy (iso.stablePathEquiv (limit_connected w) row) = rowLabel w hy row)
    (edge : (w.frame.limitTarget w.column).edges) :
    StarPilot.limitLength w' (iso.targetEdge edge) = StarPilot.limitLength w edge := by
  have hcoords := StarMetricCompatibility.coords_eq_of_retained_columns
    (allColumns w w' iso)
    (by rw [allColumns_collapsed]; exact w'.degenerate.1)
    (fun r c hc ↦ by
      rw [allColumns_retained w w' iso ⟨c,hc⟩]
      simpa only [Equiv.symm_apply_apply] using
        matrix_retained_iso w hy w' iso hLabel (w.frame.slot r) ⟨c,hc⟩)
  have heq := hcoords ((StarMetricCompatibility.retainedColumns w.frame w.column).symm edge).1
  rw [allColumns_retained] at heq
  have hc : limitColumns w w' iso
      ((StarMetricCompatibility.retainedColumns w.frame w.column).symm edge) =
      (StarMetricCompatibility.retainedColumns w'.frame w'.column).symm (iso.targetEdge edge) := by
    simp [limitColumns]
  rw [hc, StarMetricCompatibility.coords_retainedColumns_symm,
    StarMetricCompatibility.coords_retainedColumns_symm] at heq
  exact heq

end DraismaVargas.Count.InheritedLimitRows

