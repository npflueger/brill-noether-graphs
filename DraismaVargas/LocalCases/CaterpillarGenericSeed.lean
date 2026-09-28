import DraismaVargas.LocalCases.CaterpillarSeed
import DraismaVargas.LocalCases.AtlasGenericStart

/-!
# A genuine caterpillar seed with a generic starting metric

The uniform cover supplies an inhabited positive chart. The finite-hyperplane
avoidance theorem `AtlasGenericStart.exists_positiveInChart_atlasGeneric`
perturbs its metric inside that SAME chart, keeping the prescribed finishing
metric fixed. The positive rational coordinates then supply the actual seed
pencil and its time-zero state.

This discharges both the seed-region and genericity inputs of the first
march's initialization. It does not construct interior progress or a
terminal-face completion, nor a graph-tracked state interface.
-/

namespace DraismaVargas.LocalCases.CaterpillarGenericSeed

open DraismaVargas.Infrastructure
open FullDimensionalSource FiniteAtlasMarch

noncomputable def matrix (m : ℕ) :
    Matrix (Fin (6 * m + 3)) (Fin (6 * m + 3)) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (CaterpillarRows.fullDim m).labelling.presentation

noncomputable def label (m : ℕ) : MatrixAtlas.chart (Fin (6 * m + 3)) (m + 2) :=
  InitialState.presentationChart (CaterpillarRows.fullDim m).labelling.presentation
    (CaterpillarRows.fullDim m).decomposes.nodup (CaterpillarRows.fullDim m).det_ne_zero

@[simp] theorem atlasMatrix_label (m : ℕ) : MatrixAtlas.atlasMatrix (label m) = matrix m :=
  InitialState.atlasMatrix_presentationChart _ _ _

/-- Arbitrary positive rational coordinates on the actual uniform seed
produce a semantic state over their displayed source metric. -/
noncomputable def state (m : ℕ)
    (coordinates : Fin (6 * m + 3) → ℚ) (hPositive : ∀ i, 0 < coordinates i)
    (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
    (hMap : (matrix m).mulVec coordinates = baseStart) :
    SemanticAtlasMarch.State (m + 2)
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      baseStart baseFinish where
  toMatrixState := FiniteAtlasMarch.State.initial (label m) coordinates
    (chartCoordinates (MatrixAtlas.atlasMatrix (label m)) baseFinish) hPositive
    (by rw [atlasMatrix_label]; exact hMap)
    (mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseFinish)
  carriesPencil := by
    change SemanticAtlasMarch.CarriesClearedPencil (m + 2)
      (MatrixAtlas.atlasMatrix (label m)) coordinates
    rw [atlasMatrix_label]
    exact CaterpillarSeed.carriesClearedPencil m (CaterpillarRows.fullDim m)
      coordinates hPositive

@[simp] theorem state_restartTime (m : ℕ)
    (coordinates : Fin (6 * m + 3) → ℚ) (hPositive : ∀ i, 0 < coordinates i)
    (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
    (hMap : (matrix m).mulVec coordinates = baseStart) :
    (state m coordinates hPositive baseStart baseFinish hMap).toMatrixState.restartTime = 0 :=
  rfl

/-- Positivity in the actual caterpillar chart is positivity of every source
row, by its proved positive diagonal pattern. -/
theorem mulVec_pos (m : ℕ) (coordinates : Fin (6 * m + 3) → ℚ)
    (hPositive : ∀ i, 0 < coordinates i) (row : Fin (6 * m + 3)) :
    0 < (matrix m).mulVec coordinates row := by
  change 0 < (GluingDatum.LengthMatrixPresentation.matrix
    (CaterpillarRows.labelling m).presentation).mulVec coordinates row
  rw [(CaterpillarRows.diagonalPattern m).matrix_eq_diagonal, Matrix.mulVec_diagonal]
  exact mul_pos ((CaterpillarRows.diagonalPattern m).matrix_diag_pos row) (hPositive row)

/-- Uniform initialization with no supplied genericity or seed-region
receipt. The same start is generic for every chart of the finite atlas. -/
theorem exists_genericInitialState (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ) :
    ∃ baseStart : Fin (6 * m + 3) → ℚ,
      (∀ row, 0 < baseStart row) ∧
      AtlasGenericStart.AtlasGeneric (m + 2) baseStart baseFinish ∧
      ∃ initial : SemanticAtlasMarch.State (m + 2)
        (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
        baseStart baseFinish,
        initial.toMatrixState.restartTime = 0 := by
  have hInverse : chartCoordinates (MatrixAtlas.atlasMatrix (label m))
      ((matrix m).mulVec fun _ ↦ (1 : ℚ)) = (fun _ ↦ (1 : ℚ)) := by
    rw [atlasMatrix_label]
    exact chartCoordinates_eq_of_mulVec_eq _ (CaterpillarRows.fullDim m).det_ne_zero rfl
  obtain ⟨baseStart, hPositive, hGeneric⟩ :=
    AtlasGenericStart.exists_positiveInChart_atlasGeneric (m + 2) (label m)
      ((matrix m).mulVec fun _ ↦ (1 : ℚ)) baseFinish (by
        intro i
        rw [hInverse]
        exact one_pos)
  let coordinates := chartCoordinates (MatrixAtlas.atlasMatrix (label m)) baseStart
  have hMap : (matrix m).mulVec coordinates = baseStart := by
    rw [← atlasMatrix_label]
    exact mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseStart
  refine ⟨baseStart, ?_, hGeneric, state m coordinates hPositive baseStart baseFinish hMap,
    rfl⟩
  intro row
  rw [← hMap]
  exact mulVec_pos m coordinates hPositive row

/-- The chosen seed provides the two interior-march prerequisites uniformly:
simple negative crossings at every restart, and nonzero honest source rows
along every actually reached interior segment. Progress itself is not
provided here. -/
theorem exists_initializedMarch (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ) (hFinish : ∀ row, 0 ≤ baseFinish row) :
    ∃ baseStart : Fin (6 * m + 3) → ℚ,
      ∃ initial : SemanticAtlasMarch.State (m + 2)
        (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
        baseStart baseFinish,
        (∀ row, 0 < baseStart row) ∧ initial.toMatrixState.restartTime = 0 ∧
        (∀ current : SemanticAtlasMarch.State (m + 2)
          (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
          baseStart baseFinish,
          RationalAffineWall.SimpleNegativeCrossings current.toMatrixState.currentStart
            current.toMatrixState.currentFinish ∧
          (Relation.ReflTransGen SemanticAtlasMarch.State.Step initial current →
            ∀ time : ℚ, 0 ≤ time → time < 1 → ∀ row,
              (MatrixAtlas.atlasMatrix current.toMatrixState.label).mulVec
                (RationalAffineWall.segment current.toMatrixState.currentStart
                  current.toMatrixState.currentFinish time) row ≠ 0)) := by
  obtain ⟨baseStart, hStart, hGeneric, initial, hZero⟩ :=
    exists_genericInitialState m baseFinish
  refine ⟨baseStart, initial, hStart, hZero, ?_⟩
  intro current
  refine ⟨hGeneric.simpleNegativeCrossings current, ?_⟩
  intro hReach time h0 h1 row
  exact NonTrivalentWallSetup.stableRow_ne_zero_of_lt_one current.toMatrixState
    hStart hFinish (SemanticAtlasMarch.State.restartTime_nonneg_of_reachable hZero hReach)
    h0 h1 row

end DraismaVargas.LocalCases.CaterpillarGenericSeed
