module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The drop lemma: the determinant of a merged matrix

Pure linear algebra, the row-and-column operation behind the drop of an unramified mark. Let `A` be
a square matrix of size `p + 1` and `B` one of size `p` obtained from it by **merging two rows**
`r₁, r₂` (the row `i₀` of `B` is `A r₁ + A r₂`, the other rows of `B` are the other rows of `A`) and
**deleting a column** `c₁`, where column `c₁` agrees with another column `c₂` except in the rows
`r₁`, `r₂`, where it differs by `μ` and `-μ`. Replace row `r₂` by `r₁ + r₂` and then column `c₁` by
`c₁ - c₂`: the new column is `μ e_{r₁}`, and the minor at `(r₁, c₁)` is `B` up to permutations of
rows and columns. So `|det A| = |μ| |det B|` (`abs_det_eq_of_merge`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open Matrix

/-- **The determinant of a merged matrix.** `θ` lists the rows of `A` other than `r₁` (the row
`i₀` of `B` sits at `r₂`), `κ` the columns other than `c₁`. -/
theorem abs_det_eq_of_merge {p : ℕ} (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℚ)
    (B : Matrix (Fin p) (Fin p) ℚ) {r₁ r₂ c₁ c₂ : Fin (p + 1)} (hr : r₁ ≠ r₂) (hc : c₂ ≠ c₁)
    (θ : Fin p ≃ {r // r ≠ r₁}) (κ : Fin p ≃ {c // c ≠ c₁}) {i₀ : Fin p} (hi₀ : (θ i₀).1 = r₂)
    (μ : ℚ)
    (hB : ∀ i j, B i j = A (θ i).1 (κ j).1 + if i = i₀ then A r₁ (κ j).1 else 0)
    (hCol : ∀ r, A r c₁ - A r c₂ = μ * ((if r = r₁ then 1 else 0) - (if r = r₂ then 1 else 0))) :
    |A.det| = |μ| * |B.det| := by
  -- the row operation
  set A₁ : Matrix (Fin (p + 1)) (Fin (p + 1)) ℚ := updateRow A r₂ (A r₂ + A r₁) with hA₁
  have hdet₁ : A₁.det = A.det := det_updateRow_add_self A hr.symm
  -- the column operation
  set A₂ : Matrix (Fin (p + 1)) (Fin (p + 1)) ℚ :=
    updateCol A₁ c₁ fun k ↦ A₁ k c₁ + (-1 : ℚ) • A₁ k c₂ with hA₂
  have hdet₂ : A₂.det = A₁.det := det_updateCol_add_smul_self A₁ hc.symm (-1)
  -- the entries of `A₂` off column `c₁` are those of `A₁`
  have hA₂off : ∀ r c, c ≠ c₁ → A₂ r c = A₁ r c := by
    intro r c hc'
    simp [hA₂, updateCol_ne hc']
  -- the new column is `μ e_{r₁}`
  have hA₂col : ∀ r, A₂ r c₁ = if r = r₁ then μ else 0 := by
    intro r
    simp only [hA₂, updateCol_self, smul_eq_mul, neg_one_mul]
    have h1 := hCol r₁
    rw [ite_eq_left rfl, ite_eq_right hr] at h1
    by_cases h₂ : r = r₂
    · rw [h₂]
      have h2 := hCol r₂
      rw [ite_eq_right (Ne.symm hr), ite_eq_left rfl] at h2
      simp only [hA₁, updateRow_self, Pi.add_apply]
      rw [ite_eq_right (Ne.symm hr)]
      linarith
    · simp only [hA₁, updateRow_ne h₂]
      have h3 := hCol r
      rw [ite_eq_right h₂] at h3
      by_cases h₁ : r = r₁
      · rw [h₁] at h3 ⊢
        rw [ite_eq_left rfl] at h3 ⊢
        linarith
      · rw [ite_eq_right h₁] at h3 ⊢
        linarith

  -- Laplace along column `c₁`
  have hLaplace : A₂.det = (-1) ^ (r₁ + c₁ : ℕ) * μ *
      (A₂.submatrix r₁.succAbove c₁.succAbove).det := by
    rw [det_succ_column A₂ c₁, Finset.sum_eq_single r₁]
    · rw [hA₂col, ite_eq_left rfl]
    · intro r _ hne
      rw [hA₂col, ite_eq_right hne]
      ring
    · intro h
      exact absurd (Finset.mem_univ r₁) h
  -- the minor is `B`, reindexed
  set σ : Fin p ≃ Fin p := θ.trans (finSuccAboveEquiv r₁).symm with hσ
  set τ : Fin p ≃ Fin p := κ.trans (finSuccAboveEquiv c₁).symm with hτ
  have hσ' : ∀ i, r₁.succAbove (σ i) = (θ i).1 := by
    intro i
    have h := (finSuccAboveEquiv r₁).apply_symm_apply (θ i)
    rw [finSuccAboveEquiv_apply] at h
    exact congrArg Subtype.val h
  have hτ' : ∀ j, c₁.succAbove (τ j) = (κ j).1 := by
    intro j
    have h := (finSuccAboveEquiv c₁).apply_symm_apply (κ j)
    rw [finSuccAboveEquiv_apply] at h
    exact congrArg Subtype.val h
  have hBminor : B = (A₂.submatrix r₁.succAbove c₁.succAbove).submatrix σ τ := by
    funext i j
    rw [submatrix_apply, submatrix_apply, hσ', hτ', hA₂off _ _ (κ j).2, hB]
    by_cases hi : i = i₀
    · subst hi
      rw [hi₀, ite_eq_left rfl]
      simp only [hA₁, updateRow_self, Pi.add_apply]
    · rw [ite_eq_right hi, add_zero]
      have hne : (θ i).1 ≠ r₂ := by
        intro h
        exact hi (θ.injective (Subtype.ext (h.trans hi₀.symm)))
      simp only [hA₁, updateRow_ne hne]
  have hAbsB : |B.det| = |(A₂.submatrix r₁.succAbove c₁.succAbove).det| := by
    rw [hBminor]
    exact abs_det_submatrix_equiv_equiv σ τ _
  rw [← hdet₁, ← hdet₂, hLaplace, hAbsB, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]

end DraismaVargas.Count.MarkedCountGeneral
