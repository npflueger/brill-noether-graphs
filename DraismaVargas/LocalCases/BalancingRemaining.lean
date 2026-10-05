module

public import DraismaVargas.LocalCases.BalancingValencyTwo
public import Mathlib.Tactic

@[expose] public section

/-!
# The Draisma--Vargas local balancing identities (1)--(5) and (10)

This file checks Equations (1)--(5) and (10) of Draisma--Vargas Part I,
Section 6.  Together with `BalancingValencyTwo`, this covers every positive
determinant relation used at the end of the paper's 17-case local analysis.

As in the source, these lemmas isolate the common adjugate-row arithmetic from
the construction of the candidate gluing data.  They are all parameterized by
the sheet-block sizes, so none is a bounded-genus computation.
-/

namespace DraismaVargas.LocalCases.BalancingRemaining

open DraismaVargas.LocalCases.BalancingValencyTwo
open Finset

/-! ## Equation (1): four-valent wall vertex -/

/-- The three four-valent resolutions have unit weights.  The source's local
edge accounting supplies exactly the displayed sum hypothesis. -/
theorem balance_w4 {value : Fin 3 → ℚ} (hbalance : ∑ i, value i = 0) :
    PositiveBalance ![1, 1, 1] value := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · calc
      ∑ i, ![1, 1, 1] i * value i = ∑ i, value i := by
        apply Finset.sum_congr rfl
        intro i _
        fin_cases i <;> norm_num
      _ = 0 := hbalance

/-- Equation (1)'s global determinant sum is the sum of its blockwise
`w4-nd2` and `w4-nd3` identities.  This is the finite-sum interchange in the
last display of source Case `{w4}`: each candidate determinant is decomposed
over wall blocks, each block's three candidate contributions recover its wall
contribution, and the wall contributions sum to zero. -/
theorem w4_sum_eq_zero_of_block_contributions
    {block : Type*} [Fintype block]
    (candidateValue : Fin 3 → ℚ)
    (candidateContribution : block → Fin 3 → ℚ)
    (wallContribution : block → ℚ)
    (hcandidate : ∀ candidate,
      candidateValue candidate =
        ∑ sourceBlock, candidateContribution sourceBlock candidate)
    (hblock : ∀ sourceBlock,
      ∑ candidate, candidateContribution sourceBlock candidate =
        wallContribution sourceBlock)
    (hwall : ∑ sourceBlock, wallContribution sourceBlock = 0) :
    ∑ candidate, candidateValue candidate = 0 := by
  classical
  calc
    ∑ candidate, candidateValue candidate =
        ∑ candidate, ∑ sourceBlock,
          candidateContribution sourceBlock candidate := by
            apply Finset.sum_congr rfl
            intro candidate _
            exact hcandidate candidate
    _ = ∑ sourceBlock, ∑ candidate,
        candidateContribution sourceBlock candidate := by
          exact Finset.sum_comm
    _ = ∑ sourceBlock, wallContribution sourceBlock := by
          apply Finset.sum_congr rfl
          intro sourceBlock _
          exact hblock sourceBlock
    _ = 0 := hwall

/-- Blockwise W4 contribution identities therefore give the positive
unit-weight determinant balance consumed by the global continuation. -/
theorem balance_w4_of_block_contributions
    {block : Type*} [Fintype block]
    (candidateValue : Fin 3 → ℚ)
    (candidateContribution : block → Fin 3 → ℚ)
    (wallContribution : block → ℚ)
    (hcandidate : ∀ candidate,
      candidateValue candidate =
        ∑ sourceBlock, candidateContribution sourceBlock candidate)
    (hblock : ∀ sourceBlock,
      ∑ candidate, candidateContribution sourceBlock candidate =
        wallContribution sourceBlock)
    (hwall : ∑ sourceBlock, wallContribution sourceBlock = 0) :
    PositiveBalance ![1, 1, 1] candidateValue :=
  balance_w4 (w4_sum_eq_zero_of_block_contributions candidateValue
    candidateContribution wallContribution hcandidate hblock hwall)

/-! ## Equation (2): `w3-r1-nd3-t2-(a=k4)` -/

/-- The four-resolution balance at a trivalent wall vertex when the largest
block has size `k₂+k₃`. -/
theorem balance_w3_a_eq_k4
    {k₂ k₃ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ}
    (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0) :
    PositiveBalance
      ![1, k₂ + k₃ - 1, k₂ + 1, k₃ + 1]
      ![c₂ / k₂ + c₃ / k₃ + s₄,
        c₄ / (k₂ + k₃ - 1) + s₄,
        c₂ / (k₂ + 1) + s₂,
        c₃ / (k₃ + 1) + s₃] := by
  have hk₂₀ : k₂ ≠ 0 := by linarith
  have hk₃₀ : k₃ ≠ 0 := by linarith
  have hksum : k₂ + k₃ ≠ 0 := by linarith
  have hksub : k₂ + k₃ - 1 ≠ 0 := by linarith
  have hk₂p1 : k₂ + 1 ≠ 0 := by linarith
  have hk₃p1 : k₃ + 1 ≠ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    calc
      c₂ / k₂ + c₃ / k₃ + s₄ +
          ((k₂ + k₃ - 1) * (c₄ / (k₂ + k₃ - 1) + s₄) +
            ((k₂ + 1) * (c₂ / (k₂ + 1) + s₂) +
              (k₃ + 1) * (c₃ / (k₃ + 1) + s₃))) =
        (k₂ + 1) * (c₂ / k₂ + s₂) +
          ((k₃ + 1) * (c₃ / k₃ + s₃) +
            (k₂ + k₃) * (c₄ / (k₂ + k₃) + s₄)) := by
              field_simp [hk₂₀, hk₃₀, hksum, hksub, hk₂p1, hk₃p1]
              ring
      _ = 0 := by rw [h₂, h₃, h₄]; ring

/-! ## Equation (3): `w3-r1-nd3-t2-(a>k4)` -/

/-- One pair of resolutions obtained by changing a block of size `k` by one. -/
theorem balance_shift_pair {k c s : ℚ} (hk : 1 < k) (hwall : c / k + s = 0) :
    PositiveBalance ![k - 1, k + 1]
      ![c / (k - 1) + s, c / (k + 1) + s] := by
  have hk0 : k ≠ 0 := by linarith
  have hkm1 : k - 1 ≠ 0 := by linarith
  have hkp1 : k + 1 ≠ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    calc
      (k - 1) * (c / (k - 1) + s) + (k + 1) * (c / (k + 1) + s) =
          2 * k * (c / k + s) := by
            field_simp [hk0, hkm1, hkp1]
            ring
      _ = 0 := by rw [hwall]; ring

/-- Equation (3): the three independent branch choices are the sum of three
copies of `balance_shift_pair`. -/
theorem balance_w3_a_gt_k4
    {k₂ k₃ k₄ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ}
    (hk₂ : 1 < k₂) (hk₃ : 1 < k₃) (hk₄ : 1 < k₄)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / k₄ + s₄ = 0) :
    PositiveBalance
      ![k₄ - 1, k₄ + 1, k₂ - 1, k₂ + 1, k₃ - 1, k₃ + 1]
      ![c₄ / (k₄ - 1) + s₄, c₄ / (k₄ + 1) + s₄,
        c₂ / (k₂ - 1) + s₂, c₂ / (k₂ + 1) + s₂,
        c₃ / (k₃ - 1) + s₃, c₃ / (k₃ + 1) + s₃] := by
  have hbalance₂ := (balance_shift_pair hk₂ h₂).2
  have hbalance₃ := (balance_shift_pair hk₃ h₃).2
  have hbalance₄ := (balance_shift_pair hk₄ h₄).2
  simp [Fin.sum_univ_succ] at hbalance₂ hbalance₃ hbalance₄
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    linarith

/-! ## Equations (4), (5), and (10): two-resolution swaps -/

/-- Equation (4), case `w3-r1-nd3-t3`: the two candidates cross the two
wall-column contributions. -/
theorem balance_w3_nd3_t3
    {k₂ k₃ c₂ c₃ c₄ s₃ s₄ : ℚ}
    (h₃ : c₂ / k₂ + c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0) :
    PositiveBalance ![1, 1]
      ![c₄ / (k₂ + k₃) + s₃,
        c₂ / k₂ + c₃ / k₃ + s₄] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · simp [Fin.sum_univ_succ]
    linarith

/-- Equation (5), case `w3-r1-nd2`. -/
theorem balance_w3_nd2 {k c s₃ s₄ : ℚ}
    (h₃ : c / k + s₃ = 0) (h₄ : c / (k + 1) + s₄ = 0) :
    PositiveBalance ![1, 1]
      ![c / (k + 1) + s₃, c / k + s₄] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · simp [Fin.sum_univ_succ]
    linarith

/-- Equation (10), case `w2-r1`: after summing the two change-one wall
vertices, the two candidate determinants balance with unit weights. -/
theorem balance_w2_r1 {first second : ℚ} (h : first + second = 0) :
    PositiveBalance ![1, 1] ![first, second] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · simpa [Fin.sum_univ_succ] using h

end DraismaVargas.LocalCases.BalancingRemaining
