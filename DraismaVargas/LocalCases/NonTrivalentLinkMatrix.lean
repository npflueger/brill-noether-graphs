import Utilities.IntegralGeometry.WallColumnDeterminant
import DraismaVargas.LocalCases.FiniteAtlasMarch

/-!
# The common minor and positive start at a type-changing boundary

Vargas, Part II, Section 5.1, Lemma `change-comb-type` expands along the source row
being contracted: its sole nonzero entry is in the contracting target column.
All resolutions have the same complementary minor. Positive corner entries
therefore transfer nonsingularity and give determinants of the same sign.

For existence, the link into the prescribed next type in Part II's proofs of
the main theorems (Section 4.4) only needs a
positive chart point just beyond its boundary. Add a positive amount to the
vanishing target coordinate; the other coordinates stay positive. This is
not an interior Part I wall, so no opposite-sign balancing argument is used.

These are matrix lemmas. The actual candidates must still supply their row,
column and natural-matrix dictionaries; no source type is inferred here.
-/

namespace DraismaVargas.LocalCases.NonTrivalentLinkMatrix

open DraismaVargas.Infrastructure

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {A B : Matrix coordinate coordinate ℚ} {sourceRow wallColumn : coordinate}

/-- At an open target facet, a vanishing row of a nonnegative length matrix
is supported only on that facet's vanishing target coordinate. -/
theorem row_supported_of_zero_image
    (hNonnegative : ∀ row column, 0 ≤ A row column)
    {z : coordinate → ℚ} (hz : z wallColumn = 0)
    (hOther : ∀ column, column ≠ wallColumn → 0 < z column)
    (hZero : A.mulVec z sourceRow = 0)
    (column : coordinate) (hNe : column ≠ wallColumn) :
    A sourceRow column = 0 := by
  have hZ (c : coordinate) : 0 ≤ z c := by
    by_cases h : c = wallColumn
    · simpa only [h, hz] using (le_refl (0 : ℚ))
    · exact (hOther c h).le
  have hBound := Finset.single_le_sum
    (s := Finset.univ) (f := fun c ↦ A sourceRow c * z c)
    (fun c _ ↦ mul_nonneg (hNonnegative sourceRow c) (hZ c))
    (Finset.mem_univ column)
  change A sourceRow column * z column ≤ A.mulVec z sourceRow at hBound
  rw [hZero] at hBound
  have hProduct : A sourceRow column * z column = 0 :=
    le_antisymm hBound (mul_nonneg (hNonnegative sourceRow column) (hZ column))
  exact (mul_eq_zero.mp hProduct).resolve_right (hOther column hNe).ne'

/-- Expand along a source row supported only on the contracting target edge. -/
theorem det_eq_corner_mul_cofactor
    (hRow : ∀ column, column ≠ wallColumn → A sourceRow column = 0) :
    A.det = A sourceRow wallColumn * A.adjugate wallColumn sourceRow := by
  rw [Matrix.det_eq_sum_mul_adjugate_row A sourceRow]
  apply Finset.sum_eq_single wallColumn
  · intro column _ hNe
    rw [hRow column hNe, zero_mul]
  · simp

/-- The source paper's common-minor identity, expressed using actual corner
coefficients (reciprocals of the contracting indices). -/
theorem corner_mul_det_eq
    (hAgree : AgreeOffColumn A B wallColumn)
    (hRowA : ∀ column, column ≠ wallColumn → A sourceRow column = 0)
    (hRowB : ∀ column, column ≠ wallColumn → B sourceRow column = 0) :
    B sourceRow wallColumn * A.det = A sourceRow wallColumn * B.det := by
  rw [det_eq_corner_mul_cofactor hRowA, det_eq_corner_mul_cofactor hRowB,
    adjugate_wallRow_eq_of_agreeOffColumn hAgree]
  ring

/-- An incoming nonsingular resolution forces the shared minor to be nonzero. -/
theorem commonCofactor_ne_zero
    (hRowA : ∀ column, column ≠ wallColumn → A sourceRow column = 0)
    (hDet : A.det ≠ 0) : A.adjugate wallColumn sourceRow ≠ 0 := by
  intro hZero
  exact hDet (by rw [det_eq_corner_mul_cofactor hRowA, hZero, mul_zero])

theorem det_ne_zero
    (hAgree : AgreeOffColumn A B wallColumn)
    (hRowA : ∀ column, column ≠ wallColumn → A sourceRow column = 0)
    (hRowB : ∀ column, column ≠ wallColumn → B sourceRow column = 0)
    (hDet : A.det ≠ 0) (hCorner : B sourceRow wallColumn ≠ 0) : B.det ≠ 0 := by
  rw [det_eq_corner_mul_cofactor hRowB]
  apply mul_ne_zero hCorner
  rw [← adjugate_wallRow_eq_of_agreeOffColumn hAgree]
  exact commonCofactor_ne_zero hRowA hDet

/-- Nonsingularity transfers from the actual incoming facet equations. The
outgoing supported-row condition follows from agreement off the new column;
it need not be passed as an independent geometric receipt. -/
theorem det_ne_zero_of_common_boundary
    (hAgree : AgreeOffColumn A B wallColumn)
    (hNonnegative : ∀ row column, 0 ≤ A row column)
    {z : coordinate → ℚ} (hz : z wallColumn = 0)
    (hOther : ∀ column, column ≠ wallColumn → 0 < z column)
    (hZero : A.mulVec z sourceRow = 0)
    (hDet : A.det ≠ 0) (hCorner : B sourceRow wallColumn ≠ 0) : B.det ≠ 0 := by
  have hRowA := row_supported_of_zero_image hNonnegative hz hOther hZero
  exact det_ne_zero hAgree hRowA
    (fun column hNe ↦ (hAgree sourceRow column hNe).symm.trans (hRowA column hNe))
    hDet hCorner

/-- Unlike an interior wall exit, the two oriented type cones have the same
determinant sign in the coordinate convention of the common minor. -/
theorem det_mul_pos
    (hAgree : AgreeOffColumn A B wallColumn)
    (hRowA : ∀ column, column ≠ wallColumn → A sourceRow column = 0)
    (hRowB : ∀ column, column ≠ wallColumn → B sourceRow column = 0)
    (hDet : A.det ≠ 0) (hA : 0 < A sourceRow wallColumn)
    (hB : 0 < B sourceRow wallColumn) : 0 < A.det * B.det := by
  have hSquare := sq_pos_of_ne_zero (commonCofactor_ne_zero hRowA hDet)
  rw [det_eq_corner_mul_cofactor hRowA, det_eq_corner_mul_cofactor hRowB,
    ← adjugate_wallRow_eq_of_agreeOffColumn hAgree]
  have hProduct := mul_pos (mul_pos hA hB) hSquare
  nlinarith

/-- A positive chart point in the prescribed outgoing cone, arbitrarily
close to its boundary as the positive parameter tends to zero. -/
def positiveStart (z : coordinate → ℚ) (wallColumn : coordinate) (s : ℚ) :
    coordinate → ℚ := z + s • Pi.single wallColumn 1

omit [Fintype coordinate] in
theorem positiveStart_pos {z : coordinate → ℚ}
    (hz : z wallColumn = 0)
    (hOther : ∀ column, column ≠ wallColumn → 0 < z column)
    {s : ℚ} (hs : 0 < s) (column : coordinate) :
    0 < positiveStart z wallColumn s column := by
  by_cases hColumn : column = wallColumn
  · subst column
    simpa [positiveStart, hz] using hs
  · simpa [positiveStart, Pi.single_apply, hColumn] using hOther column hColumn

/-- The reflected start keeps the common boundary metric and opens precisely
the outgoing column. -/
theorem positiveStart_map (hAgree : AgreeOffColumn A B wallColumn)
    {z : coordinate → ℚ} (hz : z wallColumn = 0) (s : ℚ) :
    B.mulVec (positiveStart z wallColumn s) =
      A.mulVec z + s • B.mulVec (Pi.single wallColumn 1) := by
  rw [positiveStart, Matrix.mulVec_add, Matrix.mulVec_smul,
    mulVec_eq_on_wall hAgree hz]

/-- The outgoing inverse chart really returns this same positive vector. -/
theorem chartCoordinates_positiveStart
    (hAgree : AgreeOffColumn A B wallColumn)
    (hRowA : ∀ column, column ≠ wallColumn → A sourceRow column = 0)
    (hRowB : ∀ column, column ≠ wallColumn → B sourceRow column = 0)
    (hDet : A.det ≠ 0) (hCorner : B sourceRow wallColumn ≠ 0)
    {z : coordinate → ℚ} (hz : z wallColumn = 0) (s : ℚ) :
    FiniteAtlasMarch.chartCoordinates B
      (A.mulVec z + s • B.mulVec (Pi.single wallColumn 1)) =
        positiveStart z wallColumn s :=
  FiniteAtlasMarch.chartCoordinates_eq_of_mulVec_eq B
    (det_ne_zero hAgree hRowA hRowB hDet hCorner) (positiveStart_map hAgree hz s)

end DraismaVargas.LocalCases.NonTrivalentLinkMatrix
