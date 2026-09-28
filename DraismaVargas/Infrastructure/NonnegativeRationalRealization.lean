import DraismaVargas.Infrastructure.RationalRealization
import Utilities.Subdivision.ClosedFaceCensus

/-!
# Clearing a nonnegative rational gluing realization

A terminal point of the rational march of the Draisma--Vargas construction lies
in a closed cone: target
coordinates are nonnegative but may vanish.  This file clears such a point to
natural target and source-edge lengths without pretending that it is already
an `IntegralRealization`, whose lengths are strictly positive.

The zero source occurrences are characterized exactly by the zero target
occurrences above them.  Contracting those occurrences while preserving the
stable source type is a separate, later step (the closed-face endpoint of
`LocalCases.ClosedFaceRealization` and `LocalCases.ClosedEndpoint`).
-/

namespace DraismaVargas.Infrastructure

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ClosedFaceCensus

/-- The natural number represented by a nonnegative integral rational. -/
noncomputable def nonnegativeIntegralNat (q : ℚ) (hq : Integral q) : ℕ :=
  (Classical.choose hq).toNat

theorem nonnegativeIntegralNat_cast (q : ℚ) (hq : Integral q) (hnonneg : 0 ≤ q) :
    (nonnegativeIntegralNat q hq : ℚ) = q := by
  let z : ℤ := Classical.choose hq
  have hz : q = (z : ℚ) := Classical.choose_spec hq
  have hzNonnegQ : (0 : ℚ) ≤ (z : ℚ) := by simpa [← hz] using hnonneg
  have hzNonneg : 0 ≤ z := by exact_mod_cast hzNonnegQ
  change ((z.toNat : ℕ) : ℚ) = q
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hzNonneg, ← hz]

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- A closed-cone gluing realization.  Lengths are natural numbers and may
vanish, while the dilation equation remains exact on every source occurrence. -/
structure NonnegativeIntegralRealization
    (data : GluingDatum target degree) where
  targetLength : target.edges → ℕ
  sourceLength : data.SourceEdge → ℕ
  dilation_length : ∀ edge,
    data.sourceEdgeIndex edge * sourceLength edge = targetLength edge.1.1

/-- Clear a nonnegative rational target metric and every induced rational
source-edge length with the same explicit common scale used in the positive
realization. -/
noncomputable def NonnegativeIntegralRealization.ofNonnegativeRational
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hNonnegative : ∀ edge, 0 ≤ targetLength edge) :
    data.NonnegativeIntegralRealization where
  targetLength := fun edge ↦
    nonnegativeIntegralNat
      ((data.rationalRealizationScale targetLength : ℚ) * targetLength edge)
      (data.integral_rationalRealizationScale_target targetLength edge)
  sourceLength := fun edge ↦
    nonnegativeIntegralNat
      ((data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge)
      (data.integral_rationalRealizationScale_source targetLength edge)
  dilation_length := by
    intro edge
    have hScaleNonnegative :
        (0 : ℚ) ≤ data.rationalRealizationScale targetLength := by
      exact_mod_cast (data.rationalRealizationScale_pos targetLength).le
    have hSourceNonnegative :
        0 ≤ (data.rationalRealizationScale targetLength : ℚ) *
          data.sourceEdgeLength targetLength edge := by
      apply mul_nonneg hScaleNonnegative
      exact div_nonneg (hNonnegative edge.1.1) (by
        exact_mod_cast (data.sourceEdgeIndex_pos edge).le)
    have hTargetNonnegative :
        0 ≤ (data.rationalRealizationScale targetLength : ℚ) *
          targetLength edge.1.1 :=
      mul_nonneg hScaleNonnegative (hNonnegative edge.1.1)
    have hSourceCast := nonnegativeIntegralNat_cast
      ((data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge)
      (data.integral_rationalRealizationScale_source targetLength edge)
      hSourceNonnegative
    have hTargetCast := nonnegativeIntegralNat_cast
      ((data.rationalRealizationScale targetLength : ℚ) *
        targetLength edge.1.1)
      (data.integral_rationalRealizationScale_target targetLength edge.1.1)
      hTargetNonnegative
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_mul, hSourceCast, hTargetCast]
    unfold sourceEdgeLength
    have hIndex : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (data.sourceEdgeIndex_pos edge)
    field_simp [hIndex]

namespace NonnegativeIntegralRealization

variable {data : GluingDatum target degree}

/-- The exact sheet-block edge occupying a canonical quotient-source core
slot. -/
noncomputable def sourceEdgeAt
    (_realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) : data.SourceEdge :=
  data.sourceEdgeOfOccurrence
    (UnitSubdivisionPresentation.edgeOccurrence data.sourceGraph slot)

/-- Canonical source slots are equivalent to exact occurrence-labelled source
edges, also on a nonnegative face. -/
noncomputable def sourceSlotEquiv
    (_realization : data.NonnegativeIntegralRealization) :
    Fin data.sourceGraph.edges.card ≃ data.SourceEdge :=
  (UnitSubdivisionPresentation.edgeEquiv data.sourceGraph).symm.trans
    data.sourceEdgeOccurrenceEquiv.symm

@[simp] theorem sourceSlotEquiv_apply
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceSlotEquiv slot = realization.sourceEdgeAt slot := rfl

/-- Nonnegative length on each canonical quotient-source core slot. -/
noncomputable def sourceSlotLength
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) : ℕ :=
  realization.sourceLength (realization.sourceEdgeAt slot)

/-- The canonical zero-occurrence set of the quotient source. -/
noncomputable def sourceZeroSet
    (realization : data.NonnegativeIntegralRealization) :
    Finset (Fin data.sourceGraph.edges.card) :=
  zeroSet realization.sourceSlotLength

@[simp] theorem mem_sourceZeroSet
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    slot ∈ realization.sourceZeroSet ↔
      realization.sourceLength (realization.sourceEdgeAt slot) = 0 := by
  exact mem_zeroSet realization.sourceSlotLength slot

/-- The canonical degenerate subdivision of the quotient source.  The two
hypotheses say exactly that contracting the zero source occurrences preserves
genus and creates no surviving loop. -/
noncomputable def sourceDegSpec
    (realization : data.NonnegativeIntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy
      (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    Utilities.Certificate.DegenerateSpec.DegSpec
      (Fintype.card data.sourceGraph.V) data.sourceGraph.edges.card :=
  censusSpec (UnitSubdivisionPresentation.core data.sourceGraph)
    Fintype.card_pos realization.sourceSlotLength hForest hNotLoopy

@[simp] theorem sourceDegSpec_length
    (realization : data.NonnegativeIntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy
      (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (slot : Fin data.sourceGraph.edges.card) :
    (realization.sourceDegSpec hForest hNotLoopy).length slot =
      realization.sourceLength (realization.sourceEdgeAt slot) := rfl

/-- A forest closed face has the same genus as the unweighted quotient-source
core whose zero occurrences it contracts. -/
theorem genus_sourceDegSpec
    (realization : data.NonnegativeIntegralRealization)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet)
    (hNotLoopy : ¬ IsLoopy
      (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    genus (realization.sourceDegSpec hForest hNotLoopy).graph =
      genus data.sourceGraph := by
  rw [Utilities.Certificate.DegenerateSpec.DegSpec.genus_graph]
  rfl

@[simp]
theorem ofNonnegativeRational_targetLength_cast
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hNonnegative : ∀ edge, 0 ≤ targetLength edge) (edge : target.edges) :
    ((NonnegativeIntegralRealization.ofNonnegativeRational data targetLength
        hNonnegative).targetLength edge : ℚ) =
      (data.rationalRealizationScale targetLength : ℚ) * targetLength edge :=
  nonnegativeIntegralNat_cast _ _
    (mul_nonneg (by exact_mod_cast
      (data.rationalRealizationScale_pos targetLength).le)
      (hNonnegative edge))

@[simp]
theorem ofNonnegativeRational_sourceLength_cast
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hNonnegative : ∀ edge, 0 ≤ targetLength edge) (edge : data.SourceEdge) :
    ((NonnegativeIntegralRealization.ofNonnegativeRational data targetLength
        hNonnegative).sourceLength edge : ℚ) =
      (data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge :=
  nonnegativeIntegralNat_cast _ _
    (mul_nonneg (by exact_mod_cast
      (data.rationalRealizationScale_pos targetLength).le)
      (div_nonneg (hNonnegative edge.1.1) (by
        exact_mod_cast (data.sourceEdgeIndex_pos edge).le)))

@[simp]
theorem ofNonnegativeRational_targetLength_eq_zero_iff
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hNonnegative : ∀ edge, 0 ≤ targetLength edge) (edge : target.edges) :
    (NonnegativeIntegralRealization.ofNonnegativeRational data targetLength
        hNonnegative).targetLength edge = 0 ↔ targetLength edge = 0 := by
  constructor
  · intro hzero
    have hcast := ofNonnegativeRational_targetLength_cast data targetLength
      hNonnegative edge
    rw [hzero, Nat.cast_zero] at hcast
    have hScale : (data.rationalRealizationScale targetLength : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (data.rationalRealizationScale_pos targetLength)
    exact (mul_eq_zero.mp hcast.symm).resolve_left hScale
  · intro hzero
    apply Nat.cast_injective (R := ℚ)
    rw [ofNonnegativeRational_targetLength_cast, hzero, mul_zero, Nat.cast_zero]

@[simp]
theorem ofNonnegativeRational_sourceLength_eq_zero_iff
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hNonnegative : ∀ edge, 0 ≤ targetLength edge) (edge : data.SourceEdge) :
    (NonnegativeIntegralRealization.ofNonnegativeRational data targetLength
        hNonnegative).sourceLength edge = 0 ↔
      targetLength edge.1.1 = 0 := by
  have hScale : (data.rationalRealizationScale targetLength : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (data.rationalRealizationScale_pos targetLength)
  have hIndex : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (data.sourceEdgeIndex_pos edge)
  constructor
  · intro hzero
    have hcast := ofNonnegativeRational_sourceLength_cast data targetLength
      hNonnegative edge
    rw [hzero, Nat.cast_zero] at hcast
    have hSourceZero : data.sourceEdgeLength targetLength edge = 0 :=
      (mul_eq_zero.mp hcast.symm).resolve_left hScale
    simpa [sourceEdgeLength, hIndex] using hSourceZero
  · intro hzero
    apply Nat.cast_injective (R := ℚ)
    rw [ofNonnegativeRational_sourceLength_cast]
    simp [sourceEdgeLength, hzero]

/-- The stored nonnegative source length is exactly the rational source-edge
formula after casting. -/
theorem sourceEdgeLength_eq
    (realization : data.NonnegativeIntegralRealization)
    (edge : data.SourceEdge) :
    data.sourceEdgeLength
        (fun targetEdge ↦ realization.targetLength targetEdge) edge =
      realization.sourceLength edge := by
  have hIndex : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (data.sourceEdgeIndex_pos edge)
  have hDilation :
      (data.sourceEdgeIndex edge : ℚ) *
          (realization.sourceLength edge : ℚ) =
        (realization.targetLength edge.1.1 : ℚ) := by
    exact_mod_cast realization.dilation_length edge
  unfold GluingDatum.sourceEdgeLength
  apply (div_eq_iff hIndex).2
  simpa [mul_comm] using hDilation.symm

/-- The rational path formula recovers the sum of stored nonnegative source
lengths, including zero occurrences. -/
theorem sourcePathLength_eq
    (realization : data.NonnegativeIntegralRealization)
    (path : List data.SourceEdge) :
    data.sourcePathLength
        (fun targetEdge ↦ realization.targetLength targetEdge) path =
      (path.map (fun edge ↦ (realization.sourceLength edge : ℚ))).sum := by
  induction path with
  | nil => simp [GluingDatum.sourcePathLength]
  | cons edge rest ih =>
      change
        data.sourceEdgeLength
            (fun targetEdge ↦ realization.targetLength targetEdge) edge +
          data.sourcePathLength
            (fun targetEdge ↦ realization.targetLength targetEdge) rest =
        (realization.sourceLength edge : ℚ) +
          (rest.map
            (fun sourceEdge ↦
              (realization.sourceLength sourceEdge : ℚ))).sum
      rw [realization.sourceEdgeLength_eq, ih]

end NonnegativeIntegralRealization

/-- Evaluating a length matrix on a nonnegative realization gives the exact
sum of its possibly-zero source segment lengths along every displayed stable
path. -/
theorem LengthMatrixPresentation.matrix_mulVec_nonnegativeRealization
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (realization : data.NonnegativeIntegralRealization)
    (sourceRow : coordinate) :
    (LengthMatrixPresentation.matrix presentation).mulVec
        (fun column ↦
          (realization.targetLength (presentation.targetEdge column) : ℚ))
        sourceRow =
      ((presentation.path sourceRow).map
        (fun edge ↦ (realization.sourceLength edge : ℚ))).sum := by
  rw [LengthMatrixPresentation.matrix_mulVec presentation]
  simpa using realization.sourcePathLength_eq (presentation.path sourceRow)

end GluingDatum

end DraismaVargas.Infrastructure
