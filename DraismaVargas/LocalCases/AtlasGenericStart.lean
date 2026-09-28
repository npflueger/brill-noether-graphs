import DraismaVargas.LocalCases.WallProgress

/-!
# One generic source-metric start for the finite matrix atlas

For a nonsingular chart matrix `M`, put `f = M⁻¹ * finish`.  Distinct negative
coordinates `i`, `j` of `f` collide along the source-metric segment from
`start` to `finish` exactly on the linear wall

```text
(M⁻¹ * start) i * f j - (M⁻¹ * start) j * f i = 0.
```

This file proves that wall proper without taking properness as a receipt.  The
witness source metric is `M * eᵢ`: nonsingularity pulls it back to `eᵢ`, so the
wall evaluates to the negative, hence nonzero, coordinate `f j`.  Equivalently,
the two relevant rows of `M⁻¹` cannot be proportional.

The walls are then assembled over the finite universal `MatrixAtlas.chart`.
The final avoidance theorem is deliberately parametrized by an arbitrary
nonempty rational region cut out by strict affine inequalities; the seed
construction supplies that region and its positive base point.  Its caller is
`CaterpillarGenericSeed.exists_genericInitialState`, which uses the actual
uniform caterpillar chart and needs no separate hypothesis on the seed region.
-/

namespace DraismaVargas.LocalCases.AtlasGenericStart

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.FiniteAtlasMarch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1. Pull a negative-coordinate collision wall back to source metrics -/

/-- The equation cutting out one coordinate wall of a chart, written in the
source-metric vector rather than in chart coordinates. -/
noncomputable def chartCoordinateWall
    (matrix : Matrix coordinate coordinate ℚ) (i : coordinate) :
    RationalAffineWall coordinate where
  coefficient k := matrix⁻¹ i k
  constant := 0

@[simp]
theorem eval_chartCoordinateWall
    (matrix : Matrix coordinate coordinate ℚ) (i : coordinate)
    (source : coordinate → ℚ) :
    (chartCoordinateWall matrix i).eval source =
      chartCoordinates matrix source i := by
  simp [chartCoordinateWall, RationalAffineWall.eval, chartCoordinates,
    Matrix.mulVec, dotProduct]

/-- The source-metric equation for a collision between two distinct negative
coordinates of `matrix⁻¹ * finish`.

Unlike `negativeCollisionWall`, whose variable is already a chart-coordinate
vector, this wall's variable is the stable source metric. -/
noncomputable def chartNegativeCollisionWall
    (matrix : Matrix coordinate coordinate ℚ) (finish : coordinate → ℚ)
    (pair : DistinctNegativePair (chartCoordinates matrix finish)) :
    RationalAffineWall coordinate where
  coefficient k :=
    chartCoordinates matrix finish pair.val.2.val * matrix⁻¹ pair.val.1.val k -
      chartCoordinates matrix finish pair.val.1.val * matrix⁻¹ pair.val.2.val k
  constant := 0

/-- Evaluation of the pulled-back wall is the expected `2 × 2` minor of the
canonical chart coordinates. -/
theorem eval_chartNegativeCollisionWall
    (matrix : Matrix coordinate coordinate ℚ) (finish start : coordinate → ℚ)
    (pair : DistinctNegativePair (chartCoordinates matrix finish)) :
    (chartNegativeCollisionWall matrix finish pair).eval start =
      chartCoordinates matrix finish pair.val.2.val *
          chartCoordinates matrix start pair.val.1.val -
        chartCoordinates matrix finish pair.val.1.val *
          chartCoordinates matrix start pair.val.2.val := by
  classical
  unfold chartNegativeCollisionWall RationalAffineWall.eval chartCoordinates
  simp only [Matrix.mulVec, dotProduct, add_zero]
  calc
    ∑ k, (matrix⁻¹.mulVec finish pair.val.2.val * matrix⁻¹ pair.val.1.val k -
          matrix⁻¹.mulVec finish pair.val.1.val * matrix⁻¹ pair.val.2.val k) * start k =
        ∑ k, (matrix⁻¹.mulVec finish pair.val.2.val *
            (matrix⁻¹ pair.val.1.val k * start k) -
          matrix⁻¹.mulVec finish pair.val.1.val *
            (matrix⁻¹ pair.val.2.val k * start k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = matrix⁻¹.mulVec finish pair.val.2.val *
          (∑ k, matrix⁻¹ pair.val.1.val k * start k) -
        matrix⁻¹.mulVec finish pair.val.1.val *
          (∑ k, matrix⁻¹ pair.val.2.val k * start k) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- **Collision walls are proper, one chart.**  For a nonsingular square rational matrix, every
collision equation attached to two distinct negative endpoint coordinates is
proper as a wall in the *source metric*.

The proof uses invertibility rather than a properness hypothesis: evaluating
at the image of the first standard basis vector gives the second (negative)
endpoint coordinate. -/
theorem chartNegativeCollisionWall_proper
    (matrix : Matrix coordinate coordinate ℚ) (hdet : matrix.det ≠ 0)
    (finish : coordinate → ℚ)
    (pair : DistinctNegativePair (chartCoordinates matrix finish)) :
    (chartNegativeCollisionWall matrix finish pair).Proper := by
  classical
  let first : coordinate := pair.val.1.val
  let second : coordinate := pair.val.2.val
  let basis : coordinate → ℚ := fun k ↦ if k = first then 1 else 0
  let source : coordinate → ℚ := matrix.mulVec basis
  have hcoordinates : chartCoordinates matrix source = basis := by
    exact chartCoordinates_eq_of_mulVec_eq matrix hdet rfl
  have hne : first ≠ second := by
    intro heq
    exact pair.property (Subtype.ext heq)
  have hne' : second ≠ first := Ne.symm hne
  refine ⟨source, ?_⟩
  rw [eval_chartNegativeCollisionWall, hcoordinates]
  have hnegative : chartCoordinates matrix finish second ≠ 0 :=
    ne_of_lt pair.val.2.property
  simpa [basis, first, second, hne, hne'] using hnegative

/-! ## 2. The finite family over the universal atlas -/

/-- A collision event is a chart together with an ordered pair of distinct
negative coordinates of the fixed finish metric in that chart.  This type is
finite without enumerating the (very large) universal atlas. -/
abbrev AtlasCollisionIndex (coordinate : Type*) [Fintype coordinate]
    [DecidableEq coordinate] (degree : ℕ) (finish : coordinate → ℚ) :=
  Σ label : MatrixAtlas.chart coordinate degree,
    DistinctNegativePair
      (chartCoordinates (MatrixAtlas.atlasMatrix label) finish)

/-- The source-metric collision wall indexed by one universal-atlas event. -/
noncomputable def atlasCollisionWall (degree : ℕ) (finish : coordinate → ℚ)
    (event : AtlasCollisionIndex coordinate degree finish) :
    RationalAffineWall coordinate :=
  chartNegativeCollisionWall (MatrixAtlas.atlasMatrix event.1) finish event.2

/-- **Collision walls are proper, finite atlas.**  Every exceptional collision wall in the universal
matrix atlas is proper.  Nonsingularity is the proof stored in the chart label,
not an additional receipt. -/
theorem atlasCollisionWall_proper (degree : ℕ) (finish : coordinate → ℚ)
    (event : AtlasCollisionIndex coordinate degree finish) :
    (atlasCollisionWall degree finish event).Proper :=
  chartNegativeCollisionWall_proper (MatrixAtlas.atlasMatrix event.1)
    (MatrixAtlas.atlasMatrix_det_ne_zero event.1) finish event.2

/-! ## 3. The consumer-facing genericity condition -/

/-- One source start is generic for every chart of the universal atlas: any
two negative finish coordinates with equal crossing minors are equal.  This is
the hypothesis consumed chartwise by
`ClassifierInterface.simpleNegativeCrossings_of_chartGeneric` and
`WallProgress.simpleNegativeCrossings_of_atlasGeneric`. -/
def AtlasGeneric (degree : ℕ) (start finish : coordinate → ℚ) : Prop :=
  ∀ (label : MatrixAtlas.chart coordinate degree) (first second : coordinate),
    chartCoordinates (MatrixAtlas.atlasMatrix label) finish first < 0 →
    chartCoordinates (MatrixAtlas.atlasMatrix label) finish second < 0 →
    chartCoordinates (MatrixAtlas.atlasMatrix label) start first *
        chartCoordinates (MatrixAtlas.atlasMatrix label) finish second =
      chartCoordinates (MatrixAtlas.atlasMatrix label) start second *
        chartCoordinates (MatrixAtlas.atlasMatrix label) finish first →
    first = second

/-- Avoiding the indexed atlas walls implies the exact chartwise genericity
condition used by the march. -/
theorem atlasGeneric_of_avoids (degree : ℕ) (start finish : coordinate → ℚ)
    (havoid : ∀ event : AtlasCollisionIndex coordinate degree finish,
      (atlasCollisionWall degree finish event).eval start ≠ 0) :
    AtlasGeneric degree start finish := by
  intro label first second hfirst hsecond heq
  by_contra hne
  let firstIndex : NegativeIndex
      (chartCoordinates (MatrixAtlas.atlasMatrix label) finish) :=
    ⟨first, hfirst⟩
  let secondIndex : NegativeIndex
      (chartCoordinates (MatrixAtlas.atlasMatrix label) finish) :=
    ⟨second, hsecond⟩
  have hsubtype : firstIndex ≠ secondIndex := by
    intro h
    exact hne (congrArg Subtype.val h)
  let pair : DistinctNegativePair
      (chartCoordinates (MatrixAtlas.atlasMatrix label) finish) :=
    ⟨(firstIndex, secondIndex), hsubtype⟩
  have hwall := havoid ⟨label, pair⟩
  apply hwall
  change (chartNegativeCollisionWall
    (MatrixAtlas.atlasMatrix label) finish pair).eval start = 0
  rw [eval_chartNegativeCollisionWall]
  dsimp only [pair, firstIndex, secondIndex]
  nlinarith [heq]

/-- An atlas-generic base start supplies `SimpleNegativeCrossings` at every
restart state, through the existing chart-genericity transport theorem. -/
theorem AtlasGeneric.simpleNegativeCrossings
    {degree : ℕ} {baseStart baseFinish : coordinate → ℚ}
    (hgeneric : AtlasGeneric degree baseStart baseFinish)
    (current : SemanticAtlasMarch.State degree
      (WallProgress.atlasChartMatrix coordinate degree) baseStart baseFinish) :
    SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish := by
  apply WallProgress.simpleNegativeCrossings_of_atlasGeneric current
  simpa [WallProgress.atlasChartMatrix] using
    hgeneric current.toMatrixState.label

/-- **A simultaneously generic start in a rational region.**  Inside any
inhabited rational region cut out by finitely many strict affine inequalities,
there is a source start that
is simultaneously generic for every matrix-atlas chart.

The base point and positivity receipts are parameters: this theorem does not
construct the universal seed required by the DV induction. -/
theorem exists_atlasGeneric_preserving_positive
    {η : Type*} [Fintype η] (degree : ℕ) (finish : coordinate → ℚ)
    (constraint : η → RationalAffineWall coordinate) (base : coordinate → ℚ)
    (hbase : ∀ l, 0 < (constraint l).eval base) :
    ∃ start : coordinate → ℚ,
      (∀ l, 0 < (constraint l).eval start) ∧
      AtlasGeneric degree start finish := by
  obtain ⟨start, hpositive, havoid⟩ :=
    exists_avoids_preserving_positive (atlasCollisionWall degree finish)
      constraint base (atlasCollisionWall_proper degree finish) hbase
  exact ⟨start, hpositive,
    atlasGeneric_of_avoids degree start finish havoid⟩

/-- **A simultaneously generic start, in seed-chart form.**  A positive rational
source metric in one universal-atlas chart can be perturbed inside that same
open cone so that it is generic for every chart simultaneously, while the
prescribed finish metric remains fixed.

This assumes the atlas label and the positive seed metric; constructing them
uniformly for every required stable graph is the separate task of the seed
construction. -/
theorem exists_positiveInChart_atlasGeneric
    (degree : ℕ) (seedLabel : MatrixAtlas.chart coordinate degree)
    (base finish : coordinate → ℚ)
    (hbase : ∀ i,
      0 < chartCoordinates (MatrixAtlas.atlasMatrix seedLabel) base i) :
    ∃ start : coordinate → ℚ,
      (∀ i, 0 < chartCoordinates
        (MatrixAtlas.atlasMatrix seedLabel) start i) ∧
      AtlasGeneric degree start finish := by
  simpa using exists_atlasGeneric_preserving_positive degree finish
    (chartCoordinateWall (MatrixAtlas.atlasMatrix seedLabel)) base
    (by simpa using hbase)

end DraismaVargas.LocalCases.AtlasGenericStart
