import DraismaVargas.LocalCases.MatrixAtlas
import DraismaVargas.LocalCases.SemanticAtlasMarch

/-!
# Adapters between the source classifier and `SemanticAtlasMarch.PresentedProgress`

The fields of `SemanticAtlasMarch.PresentedProgress` are produced by several
different parts of the construction.  This module contains the short, reusable
adapters between them and the source classifier.  **The classification itself
is not attempted here**, and nothing in this file asserts that a
`PresentedProgress` exists.

Four groups.

* **Reindexing.**  Every presented family in this library is built over
  `coordinate := Option target.edges` (`GlobalW4`, `W4SourceClassification`),
  whereas `PresentedProgress` needs one fixed ambient `coordinate`.
  `reindex` moves a `LengthMatrixPresentation` along a coordinate equivalence;
  its matrix is the corresponding `Matrix.submatrix`, so determinants are
  unchanged and `PresentedFamily.reindex` follows.
* **Presentation congruence.**  The length matrix depends on a presentation
  only through `targetEdge` and the *multiset* of each row, so a canonical
  path family and the stable labelling's path family have the same matrix as
  soon as their rows agree up to permutation.
* **Genericity.**  `PresentedProgress.simpleCrossings` is a genericity
  condition that the march does not propagate.  On a positive cone point it is
  equivalent to the nonvanishing of the `2 × 2` minors
  `start i * finish j - start j * finish i` on pairs of negative endpoint
  coordinates, and along an affine segment that minor scales by `1 - t`.  So
  the condition depends on the chart and on `(baseStart, baseFinish)` only, not
  on the restart time; `simpleNegativeCrossings_of_chartGeneric` is that
  statement for an arbitrary `FiniteAtlasMarch.State`.
* **Atlas registration.**  `MatrixAtlas.encodePresentation` discharges
  `outgoingLabel` and `outgoingMatrix` verbatim, given duplicate-free rows and
  a nonzero determinant *for every member of the family*.  `familyLabel`
  records exactly that, and its docstring explains why the second hypothesis is
  a genuine restriction rather than a formality.
-/

namespace DraismaVargas.LocalCases.ClassifierInterface

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.BalancedGlobal

/-! ## 1.  Reindexing a length-matrix presentation -/

section Reindex

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
variable {coordinate coordinate' : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype coordinate'] [DecidableEq coordinate']

/-- Relabel the coordinates of a length-matrix presentation along an
equivalence.  Rows and columns are relabelled by the same map, which is what
keeps the matrix square and the determinant unchanged. -/
def reindex (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate') :
    data.LengthMatrixPresentation coordinate where
  targetEdge := relabel.trans presentation.targetEdge
  path := fun row ↦ presentation.path (relabel row)

omit [Fintype coordinate] [DecidableEq coordinate] [Fintype coordinate']
  [DecidableEq coordinate'] in
@[simp] theorem reindex_path (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate')
    (row : coordinate) :
    (reindex relabel presentation).path row =
      presentation.path (relabel row) := rfl

omit [Fintype coordinate] [DecidableEq coordinate] [Fintype coordinate']
  [DecidableEq coordinate'] in
@[simp] theorem reindex_targetEdge (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate')
    (column : coordinate) :
    (reindex relabel presentation).targetEdge column =
      presentation.targetEdge (relabel column) := rfl

omit [Fintype coordinate] [Fintype coordinate'] in
/-- Each occurrence coefficient is carried along by the relabelling. -/
theorem coefficient_reindex (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate')
    (edge : data.SourceEdge) (column : coordinate) :
    GluingDatum.LengthMatrixPresentation.coefficient
        (reindex relabel presentation) edge column =
      GluingDatum.LengthMatrixPresentation.coefficient presentation edge
        (relabel column) := by
  by_cases hTarget : presentation.targetEdge (relabel column) = edge.1.1
  · have hLeft :=
      GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
        (reindex relabel presentation) edge column 1 (by simpa using hTarget)
    have hRight :=
      GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
        presentation edge (relabel column) 1 hTarget
    rw [mul_one] at hLeft hRight
    rw [hLeft, hRight]
  · rw [GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
      (reindex relabel presentation) edge column (by simpa using hTarget),
      GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
        presentation edge (relabel column) hTarget]

omit [Fintype coordinate] [Fintype coordinate'] in
/-- **The relabelled length matrix is the corresponding submatrix.** -/
theorem matrix_reindex (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate') :
    GluingDatum.LengthMatrixPresentation.matrix (reindex relabel presentation) =
      (GluingDatum.LengthMatrixPresentation.matrix presentation).submatrix
        relabel relabel := by
  funext row column
  simp only [GluingDatum.LengthMatrixPresentation.matrix,
    GluingDatum.LengthMatrixPresentation.row, reindex_path,
    Matrix.submatrix_apply]
  exact congrArg List.sum
    (List.map_congr_left fun edge _ ↦
      coefficient_reindex relabel presentation edge column)

/-- Relabelling both rows and columns leaves the determinant alone. -/
theorem det_matrix_reindex (relabel : coordinate ≃ coordinate')
    (presentation : data.LengthMatrixPresentation coordinate') :
    (GluingDatum.LengthMatrixPresentation.matrix
        (reindex relabel presentation)).det =
      (GluingDatum.LengthMatrixPresentation.matrix presentation).det := by
  rw [matrix_reindex]
  exact Matrix.det_submatrix_equiv_self relabel _

omit [Fintype coordinate] [DecidableEq coordinate] [Fintype coordinate']
  [DecidableEq coordinate'] in
/-- Duplicate-freeness of the rows, the hypothesis of
`MatrixAtlas.encodePresentation`, is preserved by relabelling. -/
theorem nodup_reindex (relabel : coordinate ≃ coordinate')
    {presentation : data.LengthMatrixPresentation coordinate'}
    (hnodup : ∀ row, (presentation.path row).Nodup) (row : coordinate) :
    ((reindex relabel presentation).path row).Nodup := hnodup _

end Reindex

/-! ## 2.  Reindexing a presented family -/

section FamilyReindex

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {n : ℕ}
variable {coordinate coordinate' : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype coordinate'] [DecidableEq coordinate']

/-- **Move a presented balanced family to a different coordinate labelling.**
The families produced for the valency-four wall (Case `w4` of Draisma--Vargas
Part I) live over `Option target.edges`;
`SemanticAtlasMarch.PresentedProgress` needs them over the ambient
`coordinate` of the march, and the two are related by an equivalence, never by
definitional equality. -/
noncomputable def familyReindex (relabel : coordinate ≃ coordinate')
    (family : PresentedFamily (coordinate := coordinate') n data wall) :
    PresentedFamily (coordinate := coordinate) n data wall where
  candidate := family.candidate
  presentation := fun i ↦ reindex relabel (family.presentation i)
  wallColumn := relabel.symm family.wallColumn
  weight := family.weight
  positiveBalance := by
    refine ⟨family.positiveBalance.1, ?_⟩
    have hdet : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix
        (reindex relabel (family.presentation i))).det =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation i)).det :=
      fun i ↦ det_matrix_reindex relabel (family.presentation i)
    simpa only [hdet] using family.positiveBalance.2
  agreeOffWall := by
    intro first second row column hColumn
    have hNe : relabel column ≠ family.wallColumn := by
      intro hEq
      exact hColumn (by rw [← hEq, Equiv.symm_apply_apply])
    have := family.agreeOffWall first second (relabel row) (relabel column) hNe
    simpa only [matrix_reindex, Matrix.submatrix_apply] using this

@[simp] theorem familyReindex_wallColumn (relabel : coordinate ≃ coordinate')
    (family : PresentedFamily (coordinate := coordinate') n data wall) :
    (familyReindex relabel family).wallColumn =
      relabel.symm family.wallColumn := rfl

@[simp] theorem familyReindex_presentation (relabel : coordinate ≃ coordinate')
    (family : PresentedFamily (coordinate := coordinate') n data wall)
    (i : Fin n) :
    (familyReindex relabel family).presentation i =
      reindex relabel (family.presentation i) := rfl

@[simp] theorem familyReindex_candidate (relabel : coordinate ≃ coordinate')
    (family : PresentedFamily (coordinate := coordinate') n data wall)
    (i : Fin n) :
    (familyReindex relabel family).candidate i = family.candidate i := rfl

end FamilyReindex

/-! ## 3.  The length matrix sees only the row multisets -/

section Congr

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] in
/-- Two presentations with the same target labelling assign the same
coefficient to every occurrence. -/
theorem coefficient_congr
    {first second : data.LengthMatrixPresentation coordinate}
    (hTarget : first.targetEdge = second.targetEdge)
    (edge : data.SourceEdge) (column : coordinate) :
    GluingDatum.LengthMatrixPresentation.coefficient first edge column =
      GluingDatum.LengthMatrixPresentation.coefficient second edge column := by
  by_cases hEdge : second.targetEdge column = edge.1.1
  · have hLeft :=
      GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
        first edge column 1 (by rw [hTarget]; exact hEdge)
    have hRight :=
      GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
        second edge column 1 hEdge
    rw [mul_one] at hLeft hRight
    rw [hLeft, hRight]
  · rw [GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
      first edge column (by rw [hTarget]; exact hEdge),
      GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
        second edge column hEdge]

omit [Fintype coordinate] in
/-- **The length matrix depends on a presentation only through `targetEdge`
and the multiset of each row.**  A canonical path family and the stable
labelling's path family therefore have the same matrix as soon as their rows
agree up to permutation; the order inside a row is never seen. -/
theorem matrix_congr_of_perm
    {first second : data.LengthMatrixPresentation coordinate}
    (hTarget : first.targetEdge = second.targetEdge)
    (hPath : ∀ row, (first.path row).Perm (second.path row)) :
    GluingDatum.LengthMatrixPresentation.matrix first =
      GluingDatum.LengthMatrixPresentation.matrix second := by
  funext row column
  simp only [GluingDatum.LengthMatrixPresentation.matrix,
    GluingDatum.LengthMatrixPresentation.row]
  calc ((first.path row).map fun edge ↦
        GluingDatum.LengthMatrixPresentation.coefficient first edge column).sum
      = ((first.path row).map fun edge ↦
          GluingDatum.LengthMatrixPresentation.coefficient second edge
            column).sum :=
        congrArg List.sum (List.map_congr_left fun edge _ ↦
          coefficient_congr hTarget edge column)
    _ = ((second.path row).map fun edge ↦
          GluingDatum.LengthMatrixPresentation.coefficient second edge
            column).sum := ((hPath row).map _).sum_eq

end Congr

/-! ## 4.  `simpleCrossings` is a condition on the chart, not on the state -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Two negative endpoint coordinates have the same crossing time exactly
when their `2 × 2` minor vanishes.**  Positivity of the start point is what
makes both denominators nonzero, so no degenerate case survives. -/
theorem coordinateCrossingTime_eq_iff
    (start finish : ι → ℚ) {first second : ι}
    (hFirstStart : 0 < start first) (hSecondStart : 0 < start second)
    (hFirstFinish : finish first < 0) (hSecondFinish : finish second < 0) :
    coordinateCrossingTime start finish first =
        coordinateCrossingTime start finish second ↔
      start first * finish second = start second * finish first := by
  have hFirst : start first - finish first ≠ 0 := by
    intro hZero; linarith [hFirstStart, hFirstFinish]
  have hSecond : start second - finish second ≠ 0 := by
    intro hZero; linarith [hSecondStart, hSecondFinish]
  rw [coordinateCrossingTime_eq, coordinateCrossingTime_eq,
    div_eq_div_iff hFirst hSecond]
  constructor
  · intro hEq
    have hExpand : start first * start second - start first * finish second
        = start first * start second - start second * finish first := by
      calc start first * start second - start first * finish second
          = start first * (start second - finish second) := by ring
        _ = start second * (start first - finish first) := hEq
        _ = start first * start second - start second * finish first := by ring
    linarith
  · intro hEq
    calc start first * (start second - finish second)
        = start first * start second - start first * finish second := by ring
      _ = start first * start second - start second * finish first := by
          rw [hEq]
      _ = start second * (start first - finish first) := by ring

/-- Nonvanishing of those minors is exactly the genericity hypothesis
`PositiveOrthantExit` needs. -/
theorem simpleNegativeCrossings_of_cross (start finish : ι → ℚ)
    (hStart : ∀ i, 0 < start i)
    (hCross : ∀ first second, finish first < 0 → finish second < 0 →
      start first * finish second = start second * finish first →
      first = second) :
    SimpleNegativeCrossings start finish := by
  intro first hFirst second hSecond hTime
  exact hCross first second hFirst hSecond
    ((coordinateCrossingTime_eq_iff start finish (hStart first) (hStart second)
      hFirst hSecond).1 hTime)

omit [Fintype ι] [DecidableEq ι] in
/-- **The minor scales by `1 - t` along an affine segment.**  Hence the
genericity condition at a restart point is the same condition at the segment's
own start, for every restart time strictly below one. -/
theorem segment_cross (base finish : ι → ℚ) (time : ℚ) (first second : ι) :
    RationalAffineWall.segment base finish time first * finish second -
        RationalAffineWall.segment base finish time second * finish first =
      (1 - time) * (base first * finish second - base second * finish first) := by
  simp only [RationalAffineWall.segment]
  ring

end Generic

/-! ## 5.  The march state's genericity obligation, read off the chart -/

section State

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]

open DraismaVargas.LocalCases.FiniteAtlasMarch

/-- **`PresentedProgress.simpleCrossings` at an arbitrary state reduces to one
condition on the state's chart and on the pair `(baseStart, baseFinish)`.**

The state's own coordinate vectors are the canonical inverse coordinates of
the fixed base deformation, so the wall-time collisions it can exhibit are
exactly the collisions of the canonical start and finish in that chart, and
the restart time drops out.  Since the chart catalogue is finite, this turns a
per-state obligation of the classifier into one genericity choice of
`baseStart` made once, at the seed. -/
theorem simpleNegativeCrossings_of_chartGeneric
    (matrixOf : chart → Matrix coordinate coordinate ℚ)
    {baseStart baseFinish : coordinate → ℚ}
    (state : State matrixOf baseStart baseFinish)
    (hdet : (matrixOf state.label).det ≠ 0)
    (hGeneric : ∀ first second : coordinate,
      chartCoordinates (matrixOf state.label) baseFinish first < 0 →
      chartCoordinates (matrixOf state.label) baseFinish second < 0 →
      chartCoordinates (matrixOf state.label) baseStart first *
          chartCoordinates (matrixOf state.label) baseFinish second =
        chartCoordinates (matrixOf state.label) baseStart second *
          chartCoordinates (matrixOf state.label) baseFinish first →
      first = second) :
    SimpleNegativeCrossings state.currentStart state.currentFinish := by
  set canonicalStart := chartCoordinates (matrixOf state.label) baseStart with
    hCanonicalStart
  set canonicalFinish := chartCoordinates (matrixOf state.label) baseFinish with
    hCanonicalFinish
  have hFinish : state.currentFinish = canonicalFinish :=
    (chartCoordinates_eq_of_mulVec_eq (matrixOf state.label) hdet
      state.currentFinish_map).symm
  have hStart : state.currentStart =
      RationalAffineWall.segment canonicalStart canonicalFinish
        state.restartTime := by
    rw [hCanonicalStart, hCanonicalFinish, ← chartCoordinates_segment]
    exact (chartCoordinates_eq_of_mulVec_eq (matrixOf state.label) hdet
      state.currentStart_map).symm
  refine simpleNegativeCrossings_of_cross _ _ state.currentStart_positive ?_
  intro first second hFirst hSecond hMinor
  apply hGeneric first second (hFinish ▸ hFirst) (hFinish ▸ hSecond)
  have hRemaining : (1 : ℚ) - state.restartTime ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt state.restart_lt_one)
  have hScaled :
      (1 - state.restartTime) *
        (canonicalStart first * canonicalFinish second -
          canonicalStart second * canonicalFinish first) = 0 := by
    rw [← segment_cross canonicalStart canonicalFinish state.restartTime]
    rw [hStart, hFinish] at hMinor
    linarith [hMinor]
  have := mul_eq_zero.mp hScaled
  rcases this with hZero | hZero
  · exact absurd hZero hRemaining
  · linarith [hZero]

end State

/-! ## 6.  Registration in the universal matrix atlas -/

section Registration

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {n : ℕ}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The outgoing chart labels of a presented family.**

This is `PresentedProgress.outgoingLabel` for the universal atlas
`MatrixAtlas.chart`.  Note the two hypotheses: duplicate-free rows for the
entry bound, and a **nonzero determinant for every member of the family** --
not merely for the member the balancing argument selects.  The second is a
real restriction: a balanced family is allowed to contain a degenerate
resolution, and such a member has no atlas label at all. -/
noncomputable def familyLabel
    (family : PresentedFamily (coordinate := coordinate) n data wall)
    (hnodup : ∀ i row, ((family.presentation i).path row).Nodup)
    (hdet : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation i)).det ≠ 0) (i : Fin n) :
    MatrixAtlas.chart coordinate degree :=
  MatrixAtlas.encodePresentation (family.presentation i) (hnodup i) (hdet i)

/-- `PresentedProgress.outgoingMatrix` for the universal atlas. -/
@[simp] theorem atlasMatrix_familyLabel
    (family : PresentedFamily (coordinate := coordinate) n data wall)
    (hnodup : ∀ i row, ((family.presentation i).path row).Nodup)
    (hdet : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation i)).det ≠ 0) (i : Fin n) :
    MatrixAtlas.atlasMatrix (familyLabel family hnodup hdet i) =
      GluingDatum.LengthMatrixPresentation.matrix (family.presentation i) :=
  MatrixAtlas.atlasMatrix_encodePresentation _ _ _

end Registration

end DraismaVargas.LocalCases.ClassifierInterface
