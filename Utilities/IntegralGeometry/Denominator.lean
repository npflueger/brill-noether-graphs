module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact denominators of finite rational families

This file depends only on Mathlib. It computes the least positive grid scale
for a finite rational family, including zero coordinates on closed faces.
This is a denominator of coordinates, not a minimum gonality-witness scale.
-/

namespace DraismaVargas.Infrastructure

/-- A rational coordinate lies on the integral grid. -/
def Integral (q : ℚ) : Prop := ∃ z : ℤ, q = z

/-- An integral multiple is obtained as soon as the denominator divides it. -/
theorem integral_mul_of_den_dvd (q : ℚ) {N : ℕ} (h : q.den ∣ N) :
    Integral ((N : ℚ) * q) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ) * q.num, ?_⟩
  push_cast
  calc
    (q.den : ℚ) * k * q = (k : ℚ) * ((q.den : ℚ) * q) := by ring
    _ = (k : ℚ) * q.num := by rw [Rat.den_mul_eq_num]

/-- Integrality after scaling characterizes divisibility of the denominator. -/
theorem den_dvd_of_integral_mul (q : ℚ) {N : ℕ}
    (h : Integral ((N : ℚ) * q)) : q.den ∣ N := by
  by_cases hN : N = 0
  · simp [hN]
  obtain ⟨z, hz⟩ := h
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hq : q = (z : ℚ) / N := by
    apply (eq_div_iff hNq).mpr
    simpa [mul_comm] using hz
  rw [hq, ← Int.cast_natCast, ← Rat.divInt_eq_div]
  exact_mod_cast Rat.den_dvd z (N : ℤ)

theorem integral_mul_iff (q : ℚ) (N : ℕ) :
    Integral ((N : ℚ) * q) ↔ q.den ∣ N :=
  ⟨den_dvd_of_integral_mul q, integral_mul_of_den_dvd q⟩

/-- The exact coordinate denominator, with value one for the empty family. -/
def commonDenominator {ι : Type*} (s : Finset ι) (q : ι → ℚ) : ℕ :=
  s.lcm fun i => (q i).den

theorem commonDenominator_pos {ι : Type*} (s : Finset ι) (q : ι → ℚ) :
    0 < commonDenominator s q := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (by intro i _; exact (q i).den_ne_zero)

theorem den_dvd_commonDenominator {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    {i : ι} (hi : i ∈ s) : (q i).den ∣ commonDenominator s q :=
  Finset.dvd_lcm hi

theorem commonDenominator_dvd_iff {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    (N : ℕ) : commonDenominator s q ∣ N ↔ ∀ i ∈ s, (q i).den ∣ N :=
  Finset.lcm_dvd_iff

theorem integral_commonDenominator_mul {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    {i : ι} (hi : i ∈ s) : Integral ((commonDenominator s q : ℚ) * q i) :=
  integral_mul_of_den_dvd (q i) (den_dvd_commonDenominator s q hi)

/-- Every positive grid containing the coordinates is a multiple of this one. -/
theorem commonDenominator_dvd_of_integral {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    {N : ℕ} (h : ∀ i ∈ s, Integral ((N : ℚ) * q i)) :
    commonDenominator s q ∣ N :=
  (commonDenominator_dvd_iff s q N).mpr fun i hi => den_dvd_of_integral_mul (q i) (h i hi)

theorem commonDenominator_le_of_integral {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    {N : ℕ} (hN : 0 < N) (h : ∀ i ∈ s, Integral ((N : ℚ) * q i)) :
    commonDenominator s q ≤ N :=
  Nat.le_of_dvd hN (commonDenominator_dvd_of_integral s q h)

theorem integral_mul_int {q : ℚ} (hq : Integral q) (z : ℤ) :
    Integral (q * z) := by
  obtain ⟨a, rfl⟩ := hq
  exact ⟨a * z, (Int.cast_mul _ _).symm⟩

theorem integral_sum {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    (h : ∀ i ∈ s, Integral (q i)) : Integral (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨z, hz⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨w, hw⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨z + w, by simp [Finset.sum_insert ha, hz, hw]⟩

/-- A rational linear map evaluated on an integral vector. -/
def rationalEval {ι κ : Type*} [Fintype κ] (R : ι → κ → ℚ) (y : κ → ℤ) (i : ι) : ℚ :=
  ∑ j, R i j * y j

/-- Clearing matrix coefficients clears its value at every integral input. -/
theorem integral_scaled_eval {ι κ : Type*} [Fintype κ]
    (R : ι → κ → ℚ) (y : κ → ℤ) {N : ℕ}
    (h : ∀ i j, (R i j).den ∣ N) (i : ι) :
    Integral ((N : ℚ) * rationalEval R y i) := by
  unfold rationalEval
  rw [Finset.mul_sum]
  apply integral_sum
  intro j _
  rw [← mul_assoc]
  exact integral_mul_int (integral_mul_of_den_dvd (R i j) (h i j)) (y j)

/-- The coefficient denominator of a finite rational linear map. -/
def coefficientDenominator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → ℚ) : ℕ :=
  commonDenominator Finset.univ (fun ij : ι × κ => R ij.1 ij.2)

theorem coefficientDenominator_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → ℚ) : 0 < coefficientDenominator R :=
  commonDenominator_pos _ _

theorem eval_denominator_dvd_coefficients {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → ℚ) (y : κ → ℤ) :
    commonDenominator Finset.univ (rationalEval R y) ∣ coefficientDenominator R := by
  apply commonDenominator_dvd_of_integral
  intro i _
  apply integral_scaled_eval
  intro a b
  exact den_dvd_commonDenominator Finset.univ
    (fun ij : ι × κ => R ij.1 ij.2) (Finset.mem_univ (a, b))

/-- A certified odd common multiple produces a positive odd coordinate grid. -/
theorem exists_odd_integral_scale {ι : Type*} (s : Finset ι) (q : ι → ℚ)
    {N : ℕ} (hodd : Odd N) (hden : ∀ i ∈ s, (q i).den ∣ N) :
    ∃ k : ℕ, 0 < k ∧ Odd k ∧ k ∣ N ∧ ∀ i ∈ s, Integral ((k : ℚ) * q i) := by
  have hdiv : commonDenominator s q ∣ N := (commonDenominator_dvd_iff s q N).mpr hden
  exact ⟨_, commonDenominator_pos s q, hodd.of_dvd_nat hdiv, hdiv,
    fun _ hi => integral_commonDenominator_mul s q hi⟩

end DraismaVargas.Infrastructure
