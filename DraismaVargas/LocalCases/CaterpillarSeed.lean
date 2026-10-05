module

public import DraismaVargas.LocalCases.SeedFromContraction
public import DraismaVargas.LocalCases.CaterpillarDatum
public import DraismaVargas.LocalCases.InitialState
public import DraismaVargas.LocalCases.CaterpillarRows
public import DraismaVargas.LocalCases.ReachableMarch

@[expose] public section

/-!
# The actual caterpillar cover as a neutral seed

Contract the first slope-two spine edge. Its edge partition equals both
endpoint partitions, so every contracted source fibre is one edge with two
vertices. Re-expansion is the original cover with all partitions restored.
The stable row/determinant calculation (`CaterpillarRows.fullDim`) supplies the
full-dimensional presentation. `uniformInitialState` enters the semantic march in
every even genus `2m+2`, with no hypothesis on the seed as an argument.

Below, "Part I" is Draisma–Vargas Part I, arXiv:1909.12924, and "Part II" is
Vargas, Part II, arXiv:2609.09109.
-/

namespace DraismaVargas.LocalCases.CaterpillarSeed

open Utilities DraismaVargas.Infrastructure
open CaterpillarTree CaterpillarDatum ContractionRamification

section Generic

/-- If the contracted occurrence and both endpoints have the same partition,
each merged source component consists of precisely one edge and its ends. -/
theorem contractionForest_of_equal_partitions {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (a b : target.V) (edge : target.edges)
    (hLeft : data.edgePartition edge = data.vertexPartition a)
    (hRight : data.vertexPartition b = data.vertexPartition a) :
    ContractionForest data a b edge := by
  intro block
  have hSame : (mergedPartition data a b).SameBlocks (data.vertexPartition a) := by
    unfold mergedPartition
    rw [hRight]
    exact (SheetPartition.isJoin_join _ _).unique
      (SheetPartition.isJoin_left_of_refines (SheetPartition.Refines.refl _))
  have hRefines : (data.vertexPartition a).Refines (mergedPartition data a b) :=
    fun i j h ↦ (hSame i j).mpr h
  have hCard : (SheetPartition.blocksWithin (data.vertexPartition a)
      (mergedPartition data a b) block).card = 1 := by
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin _ _ hRefines,
      hSame.blockCountWithin_eq_coarse, SheetPartition.blockCountWithin_self]
  rw [hLeft, hRight, hCard]

end Generic

/-- The first paired spine occurrence, of index one. -/
def cutIndex (m : ℕ) : Fin (6 * m + 3) := ⟨1, by omega⟩

def cut (m : ℕ) : (catTree m).edges := occ m (cutIndex m)

theorem cut_endpoints_ne (m : ℕ) : catParent m (cutIndex m) ≠ (cutIndex m).succ := by
  intro h
  have hVal := congrArg Fin.val h
  have hLe := catParent_le m (cutIndex m)
  simp only [Fin.val_succ] at hVal
  omega

theorem cut_num_edges (m : ℕ) :
    num_edges (catTree m) (catParent m (cutIndex m)) (cutIndex m).succ = 1 :=
  TreeFamily.num_edges_rootedTree_eq_one _ _ _ (cutIndex m)

theorem cut_edgePartition (m : ℕ) :
    (caterpillarDatum m).edgePartition (cut m) = pairPart m 1 := by
  unfold cut
  rw [caterpillarDatum_edgePartition, catEdgePart_of_pair m _ (Or.inl rfl)]
  norm_num [cutIndex, pairIndex, lolli]

theorem cut_leftPartition (m : ℕ) :
    (caterpillarDatum m).vertexPartition (catParent m (cutIndex m)) = pairPart m 1 := by
  change pairPart m (pairIndex (catParent m (cutIndex m)).val) = pairPart m 1
  congr 1
  norm_num [catParent_val, cutIndex, parentIndex, pairIndex, lolli]

theorem cut_rightPartition (m : ℕ) :
    (caterpillarDatum m).vertexPartition (cutIndex m).succ = pairPart m 1 := by
  change pairPart m (pairIndex (cutIndex m).succ.val) = pairPart m 1
  congr 1
  norm_num [cutIndex, pairIndex, lolli]
  rw [Nat.mod_eq_of_lt (by omega : 2 < 6 * m + 3 + 1)]

theorem cut_forest (m : ℕ) : ContractionForest (caterpillarDatum m)
    (catParent m (cutIndex m)) (cutIndex m).succ (cut m) :=
  contractionForest_of_equal_partitions _ _ _ _
    ((cut_edgePartition m).trans (cut_leftPartition m).symm)
    ((cut_rightPartition m).trans (cut_leftPartition m).symm)

/-- The literal genus `2m+2`, degree `m+2` caterpillar cover as a seed. -/
noncomputable def seed (m : ℕ) : SeedCandidate.Seed (m + 2) :=
  SeedFromContraction.seed (caterpillarDatum m) (occ_coe m (cutIndex m))
    (cut_endpoints_ne m) (cut_num_edges m) (catTree_connected m) (catTree_genus m)
    (caterpillarDatum_valid m) (cut_forest m)

theorem seed_datum (m : ℕ) : (seed m).candidate.datum =
    GluingTransport.transport
      (SeedFromContraction.iso (occ_coe m (cutIndex m))
        (cut_endpoints_ne m) (cut_num_edges m)) (caterpillarDatum m) :=
  SeedFromContraction.seed_datum _ _ _ _ _ _ _ _

/-- Once the actual stable-row determinant package is supplied, the
caterpillar enters the existing march in its original length coordinates. -/
theorem carriesClearedPencil (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    SemanticAtlasMarch.CarriesClearedPencil (m + 2)
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
      coordinates :=
  SeedFromContraction.carriesClearedPencil (caterpillarDatum m)
    (occ_coe m (cutIndex m)) (cut_endpoints_ne m) (cut_num_edges m)
    fullDim (cut_forest m) coordinates hPositive

/-- The seed's actual full-dimensional presentation, with the full input
matrix unchanged by the contraction/re-expansion target transport. -/
noncomputable def seedFullDim (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) coordinate) :
    FullDimensionalSource.FullDimensionalSourcePresentation
      (seed m).candidate.datum coordinate :=
  SeedFromContraction.seedFullDim (caterpillarDatum m)
    (occ_coe m (cutIndex m)) (cut_endpoints_ne m) (cut_num_edges m)
    fullDim (cut_forest m)

theorem seedFullDim_matrix (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) coordinate) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (seedFullDim m fullDim).labelling.presentation) =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation :=
  SeedFromContraction.seedFullDim_matrix (caterpillarDatum m)
    (occ_coe m (cutIndex m)) (cut_endpoints_ne m) (cut_num_edges m)
    fullDim (cut_forest m)

/-- Actual initial state, in the original cover's matrix coordinates, for
any prescribed terminal base point. Constructing its matrix half directly
keeps the time-zero invariant literal, without a dependent cast of the state. -/
noncomputable def initialState (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) coordinate) (baseFinish : coordinate → ℚ) :
    SemanticAtlasMarch.State (m + 2)
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := m + 2))
      ((GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).mulVec
        fun _ ↦ (1 : ℚ)) baseFinish where
  toMatrixState := InitialState.matrixState fullDim.labelling.presentation
    fullDim.decomposes.nodup fullDim.det_ne_zero baseFinish
  carriesPencil := by
    simpa only [InitialState.matrixState_label, InitialState.matrixState_currentStart,
      InitialState.atlasMatrix_presentationChart] using
      carriesClearedPencil m fullDim (fun _ ↦ (1 : ℚ)) (fun _ ↦ one_pos)

@[simp] theorem initialState_restartTime (m : ℕ) {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) coordinate) (baseFinish : coordinate → ℚ) :
    (initialState m fullDim baseFinish).toMatrixState.restartTime = 0 := rfl

/-- **The uniform Part II seed in the Part I semantic march.** No datum,
validity, forest, stable-row, determinant or full-dimensionality receipt is
an input. The requested finishing point is arbitrary. -/
noncomputable def uniformInitialState (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ) :
    SemanticAtlasMarch.State (m + 2)
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      ((GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.fullDim m).labelling.presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish :=
  initialState m (CaterpillarRows.fullDim m) baseFinish

@[simp] theorem uniformInitialState_restartTime (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ) :
    (uniformInitialState m baseFinish).toMatrixState.restartTime = 0 := rfl

/-- The actual seed starts strictly inside the positive source-length orthant. -/
theorem uniformBaseStart_pos (m : ℕ) (row : Fin (6 * m + 3)) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix
      (CaterpillarRows.fullDim m).labelling.presentation).mulVec
        (fun _ ↦ (1 : ℚ)) row := by
  change 0 < (GluingDatum.LengthMatrixPresentation.matrix
    (CaterpillarRows.labelling m).presentation).mulVec (fun _ ↦ (1 : ℚ)) row
  rw [(CaterpillarRows.diagonalPattern m).matrix_eq_diagonal, Matrix.mulVec_diagonal]
  simpa only [mul_one] using (CaterpillarRows.diagonalPattern m).matrix_diag_pos row

/-- Every honest presentation carried by a state reached from this actual
seed has nonzero stable rows at each interior wall. The initial positivity
and nonnegative restart time are proved here, not additional march inputs. -/
theorem rows_ne_zero_of_reachable (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ)
    (hFinish : ∀ row, 0 ≤ baseFinish row)
    (current : SemanticAtlasMarch.State (m + 2)
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      ((GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.fullDim m).labelling.presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish)
    (hReach : Relation.ReflTransGen SemanticAtlasMarch.State.Step
      (uniformInitialState m baseFinish) current)
    {target : CFGraph} {data : GluingDatum target (m + 2)}
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      data (Fin (6 * m + 3)))
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation =
      MatrixAtlas.atlasMatrix current.toMatrixState.label)
    {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1) :
    ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation).mulVec
      (RationalAffineWall.segment current.toMatrixState.currentStart
        current.toMatrixState.currentFinish time) row ≠ 0 :=
  SemanticAtlasMarch.State.rows_ne_zero_of_reachable fullDim
    (uniformInitialState_restartTime m baseFinish) hReach hMatrix
    (uniformBaseStart_pos m) hFinish h0 h1

theorem nonempty_uniformInitialState (m : ℕ)
    (baseFinish : Fin (6 * m + 3) → ℚ) :
    Nonempty (SemanticAtlasMarch.State (m + 2)
      (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
      ((GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.fullDim m).labelling.presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish) :=
  ⟨uniformInitialState m baseFinish⟩

end DraismaVargas.LocalCases.CaterpillarSeed
