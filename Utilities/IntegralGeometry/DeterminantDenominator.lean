module

public import Utilities.IntegralGeometry.Denominator
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-!
# Determinants give effective coordinate denominators

After an integral length system has been constructed, its nonzero determinant
bounds the coordinate denominator. Expansion indices still have to be included
in that system: this does not identify a counting multiplicity with a scale.
-/

namespace DraismaVargas.Infrastructure

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cramer's rule clears every coordinate of a solution of an integral system. -/
theorem integral_det_mul_solution (B : Matrix ι ι ℤ) (y : ι → ℤ) (x : ι → ℚ)
    (h : (B.map (Int.cast : ℤ → ℚ)).mulVec x = fun i => (y i : ℚ)) (i : ι) :
    Integral ((B.det : ℚ) * x i) := by
  let A := B.map (Int.cast : ℤ → ℚ)
  have hd := Matrix.det_updateCol_sum A i x
  have hm : (fun a => ∑ j, x j • A a j) = A.mulVec x := by
    ext a
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm, h] at hd
  have hu : A.updateCol i (fun j => (y j : ℚ)) =
      (B.updateCol i y).map (Int.cast : ℤ → ℚ) := by
    ext a b
    by_cases hb : b = i <;> simp [A, hb]
  rw [hu, ← Int.cast_det] at hd
  refine ⟨(B.updateCol i y).det, ?_⟩
  rw [Int.cast_det]
  simpa [A, Int.cast_det, mul_comm] using hd.symm

/-- The determinant's absolute value is a common coordinate denominator. -/
theorem solution_denominator_dvd_det (B : Matrix ι ι ℤ) (y : ι → ℤ) (x : ι → ℚ)
    (h : (B.map (Int.cast : ℤ → ℚ)).mulVec x = fun i => (y i : ℚ)) :
    commonDenominator Finset.univ x ∣ B.det.natAbs := by
  apply commonDenominator_dvd_of_integral
  intro i _
  obtain ⟨a, ha⟩ := integral_det_mul_solution B y x h i
  rcases le_total 0 B.det with hpos | hneg
  · refine ⟨a, ?_⟩
    simpa [Nat.cast_natAbs, abs_of_nonneg hpos] using ha
  · refine ⟨-a, ?_⟩
    simpa [Nat.cast_natAbs, abs_of_nonpos hneg] using congrArg Neg.neg ha

/-- An invertible integral system gives a positive, effective upper bound. -/
theorem solution_denominator_le_det (B : Matrix ι ι ℤ) (y : ι → ℤ) (x : ι → ℚ)
    (h : (B.map (Int.cast : ℤ → ℚ)).mulVec x = fun i => (y i : ℚ))
    (hdet : B.det ≠ 0) : commonDenominator Finset.univ x ≤ B.det.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) (solution_denominator_dvd_det B y x h)

/-- An odd determinant gives an odd coordinate grid, with an explicit bound. -/
theorem solution_has_odd_grid_of_odd_det (B : Matrix ι ι ℤ) (y : ι → ℤ) (x : ι → ℚ)
    (h : (B.map (Int.cast : ℤ → ℚ)).mulVec x = fun i => (y i : ℚ))
    (hodd : Odd B.det.natAbs) :
    ∃ N : ℕ, 0 < N ∧ Odd N ∧ N ≤ B.det.natAbs ∧
      ∀ i, Integral ((N : ℚ) * x i) := by
  have hpos : 0 < B.det.natAbs := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hd := solution_denominator_dvd_det B y x h
  refine ⟨_, commonDenominator_pos Finset.univ x, hodd.of_dvd_nat hd,
    Nat.le_of_dvd hpos hd, ?_⟩
  intro i
  exact integral_commonDenominator_mul Finset.univ x (Finset.mem_univ i)

end DraismaVargas.Infrastructure
