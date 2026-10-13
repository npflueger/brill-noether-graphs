module

public import Demazure.AspPerm

@[expose] public section

/-!
# Window permutations

A finite permutation `σ` of `Fin n`, placed on the integer window `[o, o + n)`, is an ASP
permutation of `ℤ` that fixes every integer outside the window: `windowPerm σ o`. Every finite
permutation of `ℤ` of shift zero is of this form (up to the choice of window); for example the
one-line permutation `140253` (values `0`-indexed) is `windowPerm σ 0` with
`σ = [1, 4, 0, 2, 5, 3]`.

This file holds only the definition and its elementary properties; the computable slipface,
the inversion count and the corner box lemma are in `Utilities.Transmission.WindowSlipface`.
-/

namespace Utilities.Window

/-- The function of a window permutation: `σ` on `[o, o + n)`, the identity elsewhere. -/
def windowFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (x : ℤ) : ℤ :=
  if h : o ≤ x ∧ x < o + n then o + ((σ ⟨(x - o).toNat, by omega⟩ : Fin n) : ℕ) else x

theorem windowFun_of_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {x : ℤ}
    (h : o ≤ x ∧ x < o + n) :
    windowFun σ o x = o + ((σ ⟨(x - o).toNat, by omega⟩ : Fin n) : ℕ) := by
  rw [windowFun, dite_eq_left h]

theorem windowFun_of_not_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {x : ℤ}
    (h : ¬ (o ≤ x ∧ x < o + n)) : windowFun σ o x = x := by
  rw [windowFun, dite_eq_right h]

/-- On a window point, `windowFun` is `o + σ k` for the index `k`. -/
theorem windowFun_index {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) (k : Fin n) :
    windowFun σ o (o + (k : ℕ)) = o + ((σ k : Fin n) : ℕ) := by
  have h : o ≤ o + ((k : ℕ) : ℤ) ∧ o + ((k : ℕ) : ℤ) < o + n := by
    constructor
    · omega
    · have := k.isLt; omega
  rw [windowFun_of_mem σ o h]
  congr 3
  apply Fin.ext
  simp

theorem windowFun_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) {x : ℤ}
    (h : o ≤ x ∧ x < o + n) : o ≤ windowFun σ o x ∧ windowFun σ o x < o + n := by
  rw [windowFun_of_mem σ o h]
  have := (σ ⟨(x - o).toNat, by omega⟩).isLt
  omega

theorem windowFun_leftInverse {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    Function.LeftInverse (windowFun σ⁻¹ o) (windowFun σ o) := by
  intro x
  by_cases h : o ≤ x ∧ x < o + n
  · obtain ⟨k, rfl⟩ : ∃ k : Fin n, x = o + (k : ℕ) :=
      ⟨⟨(x - o).toNat, by omega⟩, by simp only; omega⟩
    rw [windowFun_index, windowFun_index]
    simp
  · rw [windowFun_of_not_mem σ o h, windowFun_of_not_mem σ⁻¹ o h]

theorem windowFun_bijective {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    Function.Bijective (windowFun σ o) := by
  refine ⟨(windowFun_leftInverse σ o).injective, ?_⟩
  have h := windowFun_leftInverse σ⁻¹ o
  rw [inv_inv] at h
  exact h.surjective

theorem windowFun_asp {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) :
    is_asp (windowFun σ o) := by
  apply Set.Finite.subset (Set.finite_Ico o (o + n))
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  by_contra hmem
  rw [Set.mem_Ico] at hmem
  rw [windowFun_of_not_mem σ o hmem] at hx
  nlinarith [mul_self_nonneg x]

/-- **The window permutation**: `σ` on `[o, o + n)`, the identity elsewhere. -/
def windowPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (o : ℤ) : AspPerm where
  func := windowFun σ o
  bijective := windowFun_bijective σ o
  asp := windowFun_asp σ o

@[simp] theorem windowPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (o x : ℤ) :
    windowPerm σ o x = windowFun σ o x := rfl

end Utilities.Window
