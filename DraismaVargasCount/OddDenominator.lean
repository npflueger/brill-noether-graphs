import DraismaVargasCount.Integrality
import Utilities.IntegralGeometry.DeterminantDenominator

/-!
# Odd multiplicity gives odd denominators after adjusting leaf lengths

This is a 2-local input of the descent of pencils to subdivisions (step 5 of
`Assembly`): at odd multiplicity the target lengths have odd denominators.

The integer matrix constructed in `Count.Integrality` is
`B' = diag(d_i) A diag(1/2 on leaf columns, 1 elsewhere)`.  If `A z = y`
with integral `y`, then `z'`, obtained by doubling the leaf coordinates,
satisfies `B' z' = diag(d_i) y`.  A determinant-denominator lemma
therefore shows that the common denominator of `z'` divides the multiplicity.
Odd multiplicity makes that common denominator odd.

No positivity or genericity is needed: the statement applies on closed faces
as well as open cones.  This is a coordinate denominator, not the scale
of a realized pencil; chip positions and slot moments are treated separately
(`RowPosition`, `SurvivingSlotMap`).
-/

namespace DraismaVargas.Count.OddDenominator

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The vector `z'`: double each leaf-edge length and keep every other length. -/
noncomputable def leafAdjustedCoords
    (presentation : data.LengthMatrixPresentation coordinate)
    (z : coordinate → ℚ) (column : coordinate) : ℚ :=
  if column ∈ leafColumns presentation then 2 * z column else z column

theorem columnScale_mul_leafAdjustedCoords
    (presentation : data.LengthMatrixPresentation coordinate)
    (z : coordinate → ℚ) (column : coordinate) :
    columnScale presentation column * leafAdjustedCoords presentation z column =
      z column := by
  classical
  by_cases h : column ∈ leafColumns presentation
  · simp only [columnScale, leafAdjustedCoords, if_pos h]
    ring
  · simp only [columnScale, leafAdjustedCoords, if_neg h, one_mul]

/-- Column halving and leaf-coordinate doubling cancel inside the length system. -/
theorem clearedMatrix_mulVec_leafAdjustedCoords
    (presentation : data.LengthMatrixPresentation coordinate) (z : coordinate → ℚ) :
    (clearedMatrix presentation).mulVec (leafAdjustedCoords presentation z) =
      fun row ↦ (rowDenominator presentation row : ℚ) * (matrix presentation).mulVec z row := by
  ext row
  simp only [Matrix.mulVec, dotProduct, clearedMatrix_apply, Finset.mul_sum,
    mul_assoc, columnScale_mul_leafAdjustedCoords]

/-- The natural multiplicity is the absolute determinant of the actual integer matrix. -/
theorem fdAbsMultNat_eq_natAbs_det
    (fd : FullDimensionalSourcePresentation data coordinate) :
    fdAbsMultNat fd = (clearedMatrixInt fd).det.natAbs := by
  change (fdSignedMult fd).num.natAbs = _
  rw [fdSignedMult_eq_det_clearedMatrix, Rat.num_intCast]

/-- The adjusted coordinate vector solves an integral system with integral right side. -/
theorem clearedMatrixInt_mulVec_leafAdjustedCoords
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (h : (matrix fd.labelling.presentation).mulVec z = fun row ↦ (y row : ℚ)) :
    ((clearedMatrixInt fd).map (Int.cast : ℤ → ℚ)).mulVec
        (leafAdjustedCoords fd.labelling.presentation z) =
      fun row ↦ (((rowDenominator fd.labelling.presentation row : ℤ) * y row : ℤ) : ℚ) := by
  have hMatrix : (clearedMatrixInt fd).map (Int.cast : ℤ → ℚ) =
      clearedMatrix fd.labelling.presentation := by
    ext row column
    exact clearedMatrixInt_cast fd row column
  rw [hMatrix, clearedMatrix_mulVec_leafAdjustedCoords, h]
  ext row
  simp only [Int.cast_mul, Int.cast_natCast]

/-- The divisibility statement, before imposing oddness: the adjusted common
denominator divides the multiplicity. -/
theorem adjusted_denominator_dvd_multiplicity
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (h : (matrix fd.labelling.presentation).mulVec z = fun row ↦ (y row : ℚ)) :
    commonDenominator Finset.univ (leafAdjustedCoords fd.labelling.presentation z) ∣
      fdAbsMultNat fd := by
  rw [fdAbsMultNat_eq_natAbs_det]
  exact solution_denominator_dvd_det (clearedMatrixInt fd)
    (fun row ↦ (rowDenominator fd.labelling.presentation row : ℤ) * y row)
    (leafAdjustedCoords fd.labelling.presentation z)
    (clearedMatrixInt_mulVec_leafAdjustedCoords fd y z h)

/-- **Odd denominators:** odd multiplicity makes the adjusted common denominator odd. -/
theorem odd_adjusted_denominator
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (h : (matrix fd.labelling.presentation).mulVec z = fun row ↦ (y row : ℚ))
    (hOdd : Odd (fdAbsMultNat fd)) :
    Odd (commonDenominator Finset.univ (leafAdjustedCoords fd.labelling.presentation z)) :=
  hOdd.of_dvd_nat (adjusted_denominator_dvd_multiplicity fd y z h)

/-- Every adjusted coordinate individually has odd denominator. -/
theorem odd_leafAdjustedCoords_den
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (h : (matrix fd.labelling.presentation).mulVec z = fun row ↦ (y row : ℚ))
    (hOdd : Odd (fdAbsMultNat fd)) (column : coordinate) :
    Odd (leafAdjustedCoords fd.labelling.presentation z column).den :=
  (odd_adjusted_denominator fd y z h hOdd).of_dvd_nat
    (den_dvd_commonDenominator Finset.univ _ (Finset.mem_univ column))

/-- An explicit odd grid for all adjusted coordinates, bounded by the multiplicity. -/
theorem exists_odd_adjusted_grid
    (fd : FullDimensionalSourcePresentation data coordinate)
    (y : coordinate → ℤ) (z : coordinate → ℚ)
    (h : (matrix fd.labelling.presentation).mulVec z = fun row ↦ (y row : ℚ))
    (hOdd : Odd (fdAbsMultNat fd)) :
    ∃ N : ℕ, 0 < N ∧ Odd N ∧ N ∣ fdAbsMultNat fd ∧ N ≤ fdAbsMultNat fd ∧
      ∀ column, Integral ((N : ℚ) * leafAdjustedCoords fd.labelling.presentation z column) := by
  have hDvd := adjusted_denominator_dvd_multiplicity fd y z h
  exact ⟨_, commonDenominator_pos _ _, odd_adjusted_denominator fd y z h hOdd, hDvd,
    Nat.le_of_dvd (fdAbsMultNat_pos fd) hDvd,
    fun column ↦ integral_commonDenominator_mul Finset.univ _ (Finset.mem_univ column)⟩

/-- The odd grid on the actual labelled fibre at an integral request.
The core-identification permutation is included in the integral right side. -/
theorem member_exists_odd_adjusted_grid {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p}
    (y : Fin p → ℤ) (member : FibreMember core (fun i ↦ (y i : ℚ)) degree)
    (hOdd : member.HasOddMult) :
    ∃ N : ℕ, 0 < N ∧ Odd N ∧ N ∣ member.oddMult ∧ N ≤ member.oddMult ∧
      ∀ column, Integral ((N : ℚ) *
        leafAdjustedCoords member.fullDim.labelling.presentation member.coords column) :=
  exists_odd_adjusted_grid member.fullDim
    (fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row)))
    member.coords member.realizes ((hasOddMult_iff_odd_fdAbsMultNat member).mp hOdd)

/-- Non-vacuity uniformly on caterpillars: their adjusted coordinates are integral. -/
theorem caterpillar_adjusted_denominator_eq_one (m : ℕ) (y : Fin (6 * m + 3) → ℤ) :
    let member := FibreCaterpillar.caterpillarMember m (fun i ↦ (y i : ℚ))
    commonDenominator Finset.univ
      (leafAdjustedCoords member.fullDim.labelling.presentation member.coords) = 1 := by
  let member := FibreCaterpillar.caterpillarMember m (fun i ↦ (y i : ℚ))
  have hDvd := adjusted_denominator_dvd_multiplicity member.fullDim
    (fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row)))
    member.coords member.realizes
  change _ ∣ fdAbsMultNat (DraismaVargas.LocalCases.CaterpillarRows.fullDim m) at hDvd
  rw [Integrality.fdAbsMultNat_caterpillar] at hDvd
  exact Nat.dvd_one.mp hDvd

end DraismaVargas.Count.OddDenominator
