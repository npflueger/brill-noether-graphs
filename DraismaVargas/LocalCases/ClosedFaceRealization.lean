import DraismaVargas.Infrastructure.NonnegativeRationalRealization
import DraismaVargas.LocalCases.BalancedGlobal

/-!
# Nonnegative closed-face realizations of global candidates

At a terminal point of the rational march, one globally assembled candidate
has nonnegative target coordinates.  Clearing them produces natural target
and source-occurrence lengths, some possibly zero.  This file retains the
common scale and proves the exact zero and stable-path identities needed by the
subsequent genus-preserving contraction and refinement step.
-/

namespace DraismaVargas.LocalCases.BalancedGlobal.Candidate

open Utilities
open Utilities.Certificate
open DraismaVargas.Infrastructure

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- The arithmetic realization of one candidate at a nonnegative closed-cone
point.  Unlike `ClearedPencil`, this does not claim that the zero-length graph
is already a positive subdivision or that rank has been transported through
its contractions. -/
structure ClearedFace
    (candidate : Candidate target degree data wall)
    {coordinate : Type*}
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) where
  realization : candidate.datum.NonnegativeIntegralRealization
  scale : ℕ
  scale_pos : 0 < scale
  targetLength_eq : ∀ column,
    (realization.targetLength (presentation.targetEdge column) : ℚ) =
      (scale : ℚ) * coordinates column

/-- Clear a nonnegative candidate metric while retaining its exact scale and
coordinate presentation. -/
noncomputable def clearedFace
    (candidate : Candidate target degree data wall)
    {coordinate : Type*}
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ i, 0 ≤ coordinates i) :
    ClearedFace candidate presentation coordinates := by
  let targetLength :
      (DraismaVargas.Infrastructure.TargetExpansion.graph
        target wall candidate.right).edges → ℚ := fun edge ↦
    coordinates (presentation.targetEdge.symm edge)
  have hTargetNonnegative : ∀ edge, 0 ≤ targetLength edge := by
    intro edge
    exact hNonnegative (presentation.targetEdge.symm edge)
  let realization :=
    GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational
      candidate.datum targetLength hTargetNonnegative
  let scale := candidate.datum.rationalRealizationScale targetLength
  refine {
    realization := realization
    scale := scale
    scale_pos := candidate.datum.rationalRealizationScale_pos targetLength
    targetLength_eq := ?_
  }
  intro column
  change
    ((GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational
      candidate.datum targetLength hTargetNonnegative).targetLength
        (presentation.targetEdge column) : ℚ) =
      (candidate.datum.rationalRealizationScale targetLength : ℚ) *
        coordinates column
  rw [GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational_targetLength_cast]
  simp [targetLength]

namespace ClearedFace

variable {candidate : Candidate target degree data wall}
  {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}

/-- The exact topological conditions under which the zero source occurrences
of a cleared face form an honest equal-genus contraction. -/
structure SourceContractionTopology
    (face : ClearedFace candidate presentation coordinates) : Prop where
  forest : Utilities.Certificate.ContractionForestCensusGeneral.IsForest
    (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
    face.realization.sourceZeroSet
  notLoopy : ¬ Utilities.Certificate.ContractionForestCensusGeneral.IsLoopy
    (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
    face.realization.sourceZeroSet

namespace SourceContractionTopology

/-- The canonical degenerate quotient-source subdivision attached to a
genus-preserving terminal face. -/
noncomputable def degSpec
    {face : ClearedFace candidate presentation coordinates}
    (topology : SourceContractionTopology face) :=
  face.realization.sourceDegSpec topology.forest topology.notLoopy

/-- Its canonical strictly positive contracted presentation. -/
noncomputable def contractedSpec
    {face : ClearedFace candidate presentation coordinates}
    (topology : SourceContractionTopology face) :=
  topology.degSpec.contractedSpec

/-- The public closed-face contraction gives an exact graph equivalence from
the positive contracted presentation to the degenerate quotient source. -/
noncomputable def laplacianEquiv
    {face : ClearedFace candidate presentation coordinates}
    (topology : SourceContractionTopology face) :
    LaplacianEquiv topology.contractedSpec.graph topology.degSpec.graph :=
  topology.degSpec.canonicalContraction.laplacianEquiv

/-- Brill--Noether existence is identical on the degenerate quotient-source
graph and its canonical positive contracted presentation. -/
theorem bnExists_iff
    {face : ClearedFace candidate presentation coordinates}
    (topology : SourceContractionTopology face) (rank divisorDegree : ℤ) :
    BNExists topology.contractedSpec.graph rank divisorDegree ↔
      BNExists topology.degSpec.graph rank divisorDegree :=
  topology.laplacianEquiv.bnExists_iff rank divisorDegree

end SourceContractionTopology

/-- A target occurrence vanishes in the cleared face exactly when its rational
coordinate vanishes. -/
theorem targetLength_eq_zero_iff
    (face : ClearedFace candidate presentation coordinates)
    (column : coordinate) :
    face.realization.targetLength (presentation.targetEdge column) = 0 ↔
      coordinates column = 0 := by
  have hScale : (face.scale : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt face.scale_pos
  constructor
  · intro hzero
    have h := face.targetLength_eq column
    rw [hzero, Nat.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hScale
  · intro hzero
    apply Nat.cast_injective (R := ℚ)
    rw [face.targetLength_eq, hzero, mul_zero, Nat.cast_zero]

/-- A source occurrence vanishes exactly when the target occurrence above it
vanishes. -/
theorem sourceLength_eq_zero_iff
    (face : ClearedFace candidate presentation coordinates)
    (edge : candidate.datum.SourceEdge) :
    face.realization.sourceLength edge = 0 ↔
      coordinates (presentation.targetEdge.symm edge.1.1) = 0 := by
  have hIndex : 0 < candidate.datum.sourceEdgeIndex edge :=
    candidate.datum.sourceEdgeIndex_pos edge
  constructor
  · intro hzero
    have hDilation := face.realization.dilation_length edge
    rw [hzero, Nat.mul_zero] at hDilation
    have hTargetZero : face.realization.targetLength edge.1.1 = 0 :=
      hDilation.symm
    have hColumn := face.targetLength_eq_zero_iff
      (presentation.targetEdge.symm edge.1.1)
    apply hColumn.mp
    simpa using hTargetZero
  · intro hzero
    have hTargetZero : face.realization.targetLength edge.1.1 = 0 := by
      have hColumn := face.targetLength_eq_zero_iff
        (presentation.targetEdge.symm edge.1.1)
      simpa using hColumn.mpr hzero
    have hDilation := face.realization.dilation_length edge
    rw [hTargetZero] at hDilation
    exact (Nat.mul_eq_zero.mp hDilation).resolve_left (Nat.ne_of_gt hIndex)

/-- The canonical quotient-source slot belongs to the contraction forest
exactly when the corresponding rational target coordinate vanishes. -/
theorem mem_sourceZeroSet_iff
    (face : ClearedFace candidate presentation coordinates)
    (slot : Fin candidate.datum.sourceGraph.edges.card) :
    slot ∈ face.realization.sourceZeroSet ↔
      coordinates (presentation.targetEdge.symm
        (face.realization.sourceEdgeAt slot).1.1) = 0 := by
  rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet]
  exact face.sourceLength_eq_zero_iff (face.realization.sourceEdgeAt slot)

/-- The cleared source segments along one displayed stable path sum to the
common scale times the corresponding rational matrix row. -/
theorem sourcePathLength_eq_scale_mul
    [Fintype coordinate] [DecidableEq coordinate]
    (face : ClearedFace candidate presentation coordinates)
    (sourceRow : coordinate) :
    ((presentation.path sourceRow).map
      (fun edge ↦ (face.realization.sourceLength edge : ℚ))).sum =
      (face.scale : ℚ) *
        (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
          coordinates sourceRow := by
  have hMatrix :=
    GluingDatum.LengthMatrixPresentation.matrix_mulVec_nonnegativeRealization
      presentation face.realization sourceRow
  have hTargetVector :
      (fun column ↦
        (face.realization.targetLength
          (presentation.targetEdge column) : ℚ)) =
        (face.scale : ℚ) • coordinates := by
    funext column
    simp only [Pi.smul_apply, smul_eq_mul]
    exact face.targetLength_eq column
  calc
    ((presentation.path sourceRow).map
        (fun edge ↦ (face.realization.sourceLength edge : ℚ))).sum =
      (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
        (fun column ↦
          (face.realization.targetLength
            (presentation.targetEdge column) : ℚ)) sourceRow := hMatrix.symm
    _ = (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
        ((face.scale : ℚ) • coordinates) sourceRow := by rw [hTargetVector]
    _ = (face.scale : ℚ) *
        (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
          coordinates sourceRow := by
      rw [Matrix.mulVec_smul]
      simp

/-- If the rational matrix represents an integral stable metric, each
possibly-zero source path has natural total length equal to the common scale
times that stable edge length.  This is the exact input expected by
`OrderedPathSplit.ofListWithZeros`. -/
theorem sourcePathLength_eq_scale_mul_of_matrixMap
    [Fintype coordinate] [DecidableEq coordinate]
    (face : ClearedFace candidate presentation coordinates)
    (stableLength : coordinate → ℕ)
    (hMap :
      (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
          coordinates = fun row ↦ (stableLength row : ℚ))
    (sourceRow : coordinate) :
    ((presentation.path sourceRow).map
      face.realization.sourceLength).sum =
        face.scale * stableLength sourceRow := by
  have hCastSum :
      ((((presentation.path sourceRow).map
        face.realization.sourceLength).sum : ℕ) : ℚ) =
      ((presentation.path sourceRow).map
        (fun edge ↦ (face.realization.sourceLength edge : ℚ))).sum := by
    induction presentation.path sourceRow with
    | nil => simp
    | cons edge rest ih => simp [ih]
  apply Nat.cast_injective (R := ℚ)
  rw [hCastSum, Nat.cast_mul, face.sourcePathLength_eq_scale_mul,
    congrFun hMap sourceRow]

end ClearedFace

end DraismaVargas.LocalCases.BalancedGlobal.Candidate
