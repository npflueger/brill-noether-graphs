import DraismaVargas.LocalCases.PrunedFibreStablePath
import DraismaVargas.LocalCases.StableSourceMatrix
import DraismaVargas.LocalCases.FullDimensionalSource
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Inherited full column rank of the literal limit matrix

Source: Draisma--Vargas Part I, `lemma-limit-matrix-change` and
`lemma-limit-full-rank` (subsection on inherited properties of limits).  The matrix is the literal
occurrence sum `StableSourceMatrix.matrix`, including at a rectangular wall.

The proved stable-path lift maps wall rows into incoming rows. Summing wall
rows along that map recovers the incoming retained columns occurrence by
occurrence.  This row pushforward is linear; independence of its image columns
implies independence of the wall columns.  No row bijection or assumed
inherited rank enters the proof.
-/

namespace DraismaVargas.LocalCases.WallInheritedRank

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource StableSourceMatrix WallDegeneration PrunedFibreStablePath
open FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

/-- The natural matrix entry, summed on actual surviving occurrences. This
equivalent presentation removes only the proof witness of survival. -/
theorem matrix_eq_sum_nonDanglingEdge (data : GluingDatum target degree)
    (path : StablePath data) (targetEdge : target.edges) :
    matrix data path targetEdge =
      ∑ edge : NonDanglingEdge data,
        if edge.stablePath = path ∧ edge.1.1.1 = targetEdge then
          (1 : ℚ) / data.sourceEdgeIndex edge.1 else 0 := by
  classical
  rw [← Finset.sum_filter]
  unfold matrix
  let survivor (edge : data.SourceEdge) (hEdge : edge ∈ occurrences data path targetEdge) :
      NonDanglingEdge data := ⟨edge, ((mem_occurrences path targetEdge edge).mp hEdge).1.choose⟩
  refine Finset.sum_bij survivor ?_ ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨hRow, hTarget⟩ := (mem_occurrences path targetEdge edge).mp hEdge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hRow.choose_spec, hTarget⟩
  · intro first hFirst second hSecond hEq
    exact congrArg Subtype.val hEq
  · intro edge hEdge
    obtain ⟨hRow, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    refine ⟨edge.1, (mem_occurrences path targetEdge edge.1).mpr
      ⟨⟨edge.2, hRow⟩, hTarget⟩, ?_⟩
    exact Subtype.ext rfl
  · intro edge hEdge
    rfl

section Contraction

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

theorem unfoldEdge_injective : Function.Injective (unfoldEdge hc hab hOne) := by
  intro first second hEq
  exact (foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext hEq)

/-- The surviving source embedding respects the literal target occurrence,
not merely its endpoint pair. -/
theorem sourceEdgeEmbedding_target
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (sourceEdgeEmbedding data hc hab hOne edge).1.1 = unfoldEdge hc hab hOne edge.1.1 := by
  obtain ⟨preimage, rfl⟩ := sourceEdgeMap_surjective data hc hab hOne edge
  rw [sourceEdgeEmbedding_sourceEdgeMap]
  exact (unfoldEdge_foldEdge hc hab hOne ⟨preimage.1.1.1, preimage.2⟩).symm

/-- Every incoming survivor away from the contracted target occurrence has
an actual surviving wall occurrence as its preimage. -/
theorem exists_nonDanglingEmbedding_eq (hCompat : DanglingCompatible data hc hab hOne)
    (edge : NonDanglingEdge data) (hTarget : edge.1.1.1 ≠ contracted) :
    ∃ preimage : NonDanglingEdge (contractDatum data hc hab hOne),
      nonDanglingEmbedding data hCompat.1 preimage = edge := by
  let preimage : NonDanglingEdge (contractDatum data hc hab hOne) :=
    ⟨sourceEdgeMap data hc hab hOne ⟨edge.1, hTarget⟩,
      fun hBad ↦ edge.2 (hCompat.2 ⟨edge.1, hTarget⟩ hBad)⟩
  refine ⟨preimage, Subtype.ext ?_⟩
  exact sourceEdgeEmbedding_sourceEdgeMap data hc hab hOne ⟨edge.1, hTarget⟩

variable (hConnected : graph_connected data.sourceGraph)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)

/-- Literal occurrence transport after grouping rows by the proved
stable-path lift.  Every retained occurrence contributes exactly once. -/
theorem sum_lifted_occurrences
    (path : StablePath data) (targetEdge : (contract target hab hOne).edges) :
    (∑ edge ∈ (Finset.univ : Finset (NonDanglingEdge (contractDatum data hc hab hOne))).filter
      (fun edge ↦ stablePathLift data hc hab hOne hConnected hCompat hForest edge.stablePath = path ∧
        edge.1.1.1 = targetEdge), (1 : ℚ) / (contractDatum data hc hab hOne).sourceEdgeIndex edge.1) =
      ∑ edge ∈ (Finset.univ : Finset (NonDanglingEdge data)).filter
        (fun edge ↦ edge.stablePath = path ∧ edge.1.1.1 = unfoldEdge hc hab hOne targetEdge),
        (1 : ℚ) / data.sourceEdgeIndex edge.1 := by
  classical
  refine Finset.sum_bij (fun edge _ ↦ nonDanglingEmbedding data hCompat.1 edge) ?_ ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨hRow, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact (stablePathLift_mk data hc hab hOne hConnected hCompat hForest edge).symm.trans hRow
    · change (sourceEdgeEmbedding data hc hab hOne edge.1).1.1 = _
      rw [sourceEdgeEmbedding_target, hTarget]
  · intro first _ second _ hEq
    exact nonDanglingEmbedding_injective data hCompat.1 hEq
  · intro edge hEdge
    obtain ⟨hRow, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    have hNe : edge.1.1.1 ≠ contracted := by
      rw [hTarget]
      exact unfoldEdge_ne_contracted hc hab hOne targetEdge
    obtain ⟨preimage, hPreimage⟩ := exists_nonDanglingEmbedding_eq data hc hab hOne hCompat edge hNe
    refine ⟨preimage, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hPreimage⟩
    · rw [stablePathLift_mk, hPreimage]
      exact hRow
    · apply unfoldEdge_injective hc hab hOne
      have hPreimageTarget := sourceEdgeEmbedding_target data hc hab hOne preimage.1
      have hEq := congrArg (fun e : NonDanglingEdge data ↦ e.1.1.1) hPreimage
      exact hPreimageTarget.symm.trans (hEq.trans hTarget)
  · intro edge _
    rw [nonDanglingEmbedding_val, sourceEdgeIndex_sourceEdgeEmbedding]

/-- **The literal limit-matrix pushforward identity.**  Summing wall rows
along the actual stable-path lift recovers each incoming retained entry. -/
theorem sum_rows_matrix
    (path : StablePath data) (targetEdge : (contract target hab hOne).edges) :
    (∑ row ∈ (Finset.univ : Finset (StablePath (contractDatum data hc hab hOne))).filter
      (fun row ↦ stablePathLift data hc hab hOne hConnected hCompat hForest row = path),
      matrix (contractDatum data hc hab hOne) row targetEdge) =
      matrix data path (unfoldEdge hc hab hOne targetEdge) := by
  classical
  have hRowSum (edge : NonDanglingEdge (contractDatum data hc hab hOne)) :
      (∑ row ∈ (Finset.univ : Finset (StablePath (contractDatum data hc hab hOne))).filter
        (fun row ↦ stablePathLift data hc hab hOne hConnected hCompat hForest row = path),
        if edge.stablePath = row ∧ edge.1.1.1 = targetEdge then
          (1 : ℚ) / (contractDatum data hc hab hOne).sourceEdgeIndex edge.1 else 0) =
        if stablePathLift data hc hab hOne hConnected hCompat hForest edge.stablePath = path ∧
          edge.1.1.1 = targetEdge then
            (1 : ℚ) / (contractDatum data hc hab hOne).sourceEdgeIndex edge.1 else 0 := by
    by_cases hTarget : edge.1.1.1 = targetEdge
    · simp [hTarget]
    · simp [hTarget]
  simp_rw [matrix_eq_sum_nonDanglingEdge]
  rw [Finset.sum_comm]
  simp_rw [hRowSum]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  exact sum_lifted_occurrences data hc hab hOne hConnected hCompat hForest path targetEdge

section Labelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (labelling : StableLengthMatrixLabelling data coordinate)

/-- Row pushforward into the honest incoming coordinate space. It is a
finite sum of coordinate projections, hence linear without any row bijection. -/
noncomputable def rowPushforward :
    (StablePath (contractDatum data hc hab hOne) → ℚ) →ₗ[ℚ] (coordinate → ℚ) := by
  classical
  exact LinearMap.pi fun row ↦
    ∑ path ∈ (Finset.univ : Finset (StablePath (contractDatum data hc hab hOne))).filter
      (fun path ↦ stablePathLift data hc hab hOne hConnected hCompat hForest path = labelling.row.symm row),
      (LinearMap.proj path : (StablePath (contractDatum data hc hab hOne) → ℚ) →ₗ[ℚ] ℚ)

omit [Fintype coordinate] in
/-- A single wall row pushes forward to the coordinate vector of its actual
incoming stable class, even when distinct wall rows have the same image. -/
theorem rowPushforward_single (path : StablePath (contractDatum data hc hab hOne)) :
    rowPushforward data hc hab hOne hConnected hCompat hForest labelling
      (Pi.single path (1 : ℚ)) =
        Pi.single (labelling.row
          (stablePathLift data hc hab hOne hConnected hCompat hForest path)) (1 : ℚ) := by
  classical
  funext row
  simp only [rowPushforward, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [← Equiv.apply_eq_iff_eq labelling.row, Equiv.apply_symm_apply, eq_comm]

/-- Each literal wall column pushes forward to exactly the corresponding
retained column of the incoming nonsingular presentation. -/
theorem rowPushforward_column (targetEdge : (contract target hab hOne).edges) :
    rowPushforward data hc hab hOne hConnected hCompat hForest labelling
      ((matrix (contractDatum data hc hab hOne)).col targetEdge) =
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).col
        (labelling.targetEdge.symm (unfoldEdge hc hab hOne targetEdge)) := by
  funext row
  simp only [rowPushforward, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply]
  change (∑ path ∈ (Finset.univ : Finset (StablePath (contractDatum data hc hab hOne))).filter
    (fun path ↦ stablePathLift data hc hab hOne hConnected hCompat hForest path = labelling.row.symm row),
    matrix (contractDatum data hc hab hOne) path targetEdge) =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        (labelling.targetEdge.symm (unfoldEdge hc hab hOne targetEdge))
  rw [labelling_matrix_eq, Equiv.apply_symm_apply]
  exact sum_rows_matrix data hc hab hOne hConnected hCompat hForest _ targetEdge

end Labelling

/-- **Draisma--Vargas `lemma-limit-full-rank`, for the literal natural wall
matrix.**  An honest full-dimensional incoming presentation, an actual forest
contraction, and occurrencewise dangling compatibility imply independence of
all wall columns. No arbitrary stable-row equivalence or rank receipt is
supplied. -/
theorem columns_independent {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted) :
    LinearIndependent ℚ (matrix (contractDatum data hc hab hOne)).col := by
  classical
  let retained : (contract target hab hOne).edges → coordinate :=
    fun targetEdge ↦ fullDim.labelling.targetEdge.symm (unfoldEdge hc hab hOne targetEdge)
  have hRetained : Function.Injective retained :=
    fullDim.labelling.targetEdge.symm.injective.comp (unfoldEdge_injective hc hab hOne)
  have hIncoming : LinearIndependent ℚ
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero fullDim.det_ne_zero
  apply LinearIndependent.of_comp
    (rowPushforward data hc hab hOne fullDim.valid.1 hCompat hForest fullDim.labelling)
  have hColumns :
      rowPushforward data hc hab hOne fullDim.valid.1 hCompat hForest fullDim.labelling ∘
          (matrix (contractDatum data hc hab hOne)).col =
        (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).col ∘ retained := by
    funext targetEdge
    exact rowPushforward_column data hc hab hOne fullDim.valid.1 hCompat hForest fullDim.labelling targetEdge
  rw [hColumns]
  exact hIncoming.comp retained hRetained

end Contraction

end DraismaVargas.LocalCases.WallInheritedRank
