module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
# Determinants of matrices with sparse columns

Three facts about square matrices over `ℚ` whose columns have few nonzero entries:

* `card_le_of_cols_supported`: in a nonsingular matrix, the columns supported on a set `R` of
  rows number at most `#R`;
* `abs_det_eq_of_doubled_columns`: if three columns have the single nonzero entry `2`, in three
  distinct rows, then `|det M| = 8 |det M'|`, where `M'` deletes those rows and columns;
* `abs_det_refine`: the effect on `|det|` of refining a length-type matrix at one point, which
  splits one row and one column in two (`|det M| = |δ| · |det B|`).

`abs_det_submatrix_equiv` (reindexing changes the determinant only by a sign) and
`card_compl_range_add_three` are the bookkeeping they use. Together they compute the determinant
of the length matrix of a tropical morphism with a tripod glued in
(`Research/genus-six-brill-noether-rank.md`, §5.3).
-/

namespace Utilities.DeterminantExpansion

/-! ## Columns supported on few rows -/

/-- **Columns of a nonsingular matrix supported on a set of rows `R` number at most `#R`.**
They are linearly independent, and restricting them to `R` keeps them independent. -/
theorem card_le_of_cols_supported {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : M.det ≠ 0) (C R : Finset ι)
    (h : ∀ c ∈ C, ∀ r ∉ R, M r c = 0) : C.card ≤ R.card := by
  classical
  let v : C → (R → ℚ) := fun c r ↦ M r c
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    let g' : ι → ℚ := fun j ↦ if hj : j ∈ C then g ⟨j, hj⟩ else 0
    have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hM
    rw [Fintype.linearIndependent_iff] at hcols
    have hkey : ∀ r, ∑ j, g' j * M r j = ∑ c : C, g c * M r c := by
      intro r
      rw [← Finset.sum_subset (Finset.subset_univ C) (fun j _ hj ↦ by simp [g', hj]),
        ← Finset.sum_coe_sort C]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp [g', c.2]
    have hsum : ∑ j, g' j • M.col j = 0 := by
      funext r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
        Pi.zero_apply]
      rw [hkey r]
      by_cases hr : r ∈ R
      · have := congrFun hg ⟨r, hr⟩
        simpa [Finset.sum_apply, v] using this
      · exact Finset.sum_eq_zero fun c _ ↦ by rw [h c c.2 r hr, mul_zero]
    have := hcols g' hsum c.1
    simpa [g', c.2] using this
  have := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at this

/-! ## Expanding along doubled columns, and one refinement step -/

/-- Reindexing rows and columns by two bijections changes the determinant only by a sign. -/
theorem abs_det_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι ι ℚ) (f g : κ ≃ ι) :
    |(M.submatrix f g).det| = |M.det| := by
  have h : M.submatrix f g = (M.submatrix f f).submatrix id (g.trans f.symm) := by
    ext i j
    simp
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self, abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (g.trans f.symm)) with hs | hs <;> simp [hs]

/-- **Expanding along three columns of the form `2 e_r`.** If the columns
`c k` of a square matrix have the single non-zero entry `2`, in the rows `r k`, then
`|det M| = 8 |det M'|`, where `M'` deletes those rows and columns (matched by any bijection). -/
theorem abs_det_eq_of_doubled_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (r c : Fin 3 → ι) (hr : Function.Injective r)
    (hc : Function.Injective c) (hcol : ∀ i k, M i (c k) = if i = r k then 2 else 0)
    (e : {i // i ∉ Set.range r} ≃ {j // j ∉ Set.range c}) :
    |M.det| = 8 * |(M.submatrix (fun i : {i // i ∉ Set.range r} ↦ i.1)
      (fun i ↦ (e i).1)).det| := by
  classical
  let σr : Fin 3 ⊕ {i // i ∉ Set.range r} ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.sumCompl (· ∈ Set.range r))
  let σc : Fin 3 ⊕ {i // i ∉ Set.range r} ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective c hc) e).trans (Equiv.sumCompl (· ∈ Set.range c))
  have hblocks : M.submatrix σr σc = Matrix.fromBlocks (Matrix.diagonal fun _ ↦ (2 : ℚ))
      (Matrix.of fun k j ↦ M (r k) (e j).1) 0
      (M.submatrix (fun i : {i // i ∉ Set.range r} ↦ i.1) (fun i ↦ (e i).1)) := by
    ext (k | i) (l | j)
    · simp [σr, σc, hcol, Matrix.diagonal, hr.eq_iff]
    · simp [σr, σc]
    · have hne : ∀ k, i.1 ≠ r k := fun k h ↦ i.2 ⟨k, h.symm⟩
      simp [σr, σc, hcol, hne]
    · simp [σr, σc]
  rw [← abs_det_submatrix_equiv M σr σc, hblocks, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_diagonal, abs_mul]
  norm_num


/-- `Unit ⊕ ι ≃ Option ι`, sending the point to `some a` and `a` to `none`. -/
def splitEquiv {ι : Type} [DecidableEq ι] (a : ι) : Unit ⊕ ι ≃ Option ι :=
  ((Equiv.sumComm Unit ι).trans (Equiv.optionEquivSumPUnit ι).symm).trans
    (Equiv.swap none (some a))

@[simp] theorem splitEquiv_inl {ι : Type} [DecidableEq ι] (a : ι) (u : Unit) :
    splitEquiv a (Sum.inl u) = some a := by
  simp [splitEquiv, Equiv.optionEquivSumPUnit]

theorem splitEquiv_inr {ι : Type} [DecidableEq ι] (a r : ι) :
    splitEquiv a (Sum.inr r) = if r = a then none else some r := by
  by_cases h : r = a
  · subst h; simp [splitEquiv, Equiv.optionEquivSumPUnit]
  · simp [splitEquiv, Equiv.optionEquivSumPUnit, h, Equiv.swap_apply_of_ne_of_ne]

/-- **One refinement step.** Let `M` refine `B` at one point:
the row `h` of `B` is split into the pieces `some h` and `none` of `M`, and the column `t` into
`some t` and `none`; every other row passes over the two halves of `t` alike, and the two pieces
together are the old row, agreeing on the two halves. Then `|det M| = |δ| · |det B|`, where
`δ = M (some h) (some t) - M (some h) none` is `1/a` for a split at a point of index `a`
(`1` on a hairpin). Proof: add the piece `some h` to the piece `none` (the old row), subtract the
column `none` from the column `some t`; that column is then `δ` times a unit vector, and the
complementary minor is `B`. -/
theorem abs_det_refine {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℚ)
    (M : Matrix (Option ι) (Option ι) ℚ) (h t : ι)
    (hother : ∀ r, r ≠ h → M (some r) (some t) = M (some r) none)
    (hsum : M (some h) (some t) + M none (some t) = M (some h) none + M none none)
    (hrow : ∀ c, B h c = M (some h) (some c) + M none (some c))
    (hB : ∀ r, r ≠ h → ∀ c, B r c = M (some r) (some c)) :
    |M.det| = |M (some h) (some t) - M (some h) none| * |B.det| := by
  set M₁ := M.updateRow none (M none + M (some h)) with hM₁
  have h₁ : M₁.det = M.det := Matrix.det_updateRow_add_self M (by simp)
  set M₂ := M₁.updateCol (some t) (fun k ↦ M₁ k (some t) + (-1 : ℚ) • M₁ k none) with hM₂
  have h₂ : M₂.det = M₁.det := Matrix.det_updateCol_add_smul_self M₁ (by simp) (-1)
  have hblocks : M₂.submatrix (splitEquiv h) (splitEquiv t) = Matrix.fromBlocks
      (Matrix.of fun _ _ ↦ M (some h) (some t) - M (some h) none)
      (Matrix.of fun _ c ↦ M₂ (some h) (splitEquiv t (Sum.inr c))) 0 B := by
    ext (u | r) (v | c)
    · simp [M₂, M₁, Matrix.updateCol_apply, Matrix.updateRow_apply, sub_eq_add_neg]
    · simp
    · by_cases hr : r = h
      · subst hr
        simp [M₂, M₁, splitEquiv_inr, Matrix.updateRow_apply]
        linarith
      · simp [M₂, M₁, splitEquiv_inr, hr, Matrix.updateRow_apply, hother r hr]
    · have hcol : splitEquiv t (Sum.inr c) ≠ some t := by
        rw [splitEquiv_inr]
        split_ifs with hc
        · simp
        · exact fun h' ↦ hc (Option.some_injective _ h')
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, M₂,
        Matrix.updateCol_ne hcol]
      by_cases hr : r = h <;> by_cases hc : c = t
      · subst hr hc
        simp [M₁, splitEquiv_inr, Matrix.updateRow_apply, hrow]
        linarith
      · subst hr
        simp [M₁, splitEquiv_inr, hc, Matrix.updateRow_apply, hrow, add_comm]
      · subst hc
        simp [M₁, splitEquiv_inr, hr, Matrix.updateRow_apply, hB r hr, hother r hr]
      · simp [M₁, splitEquiv_inr, hr, hc, Matrix.updateRow_apply, hB r hr]
  rw [← h₁, ← h₂, ← abs_det_submatrix_equiv M₂ (splitEquiv h) (splitEquiv t), hblocks,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, abs_mul]
  rfl

/-- The complement of three distinct indices. -/
theorem card_compl_range_add_three {ι : Type*} [Fintype ι] [DecidableEq ι] (r : Fin 3 → ι)
    (hr : Function.Injective r) : Fintype.card {i // i ∉ Set.range r} + 3 = Fintype.card ι := by
  classical
  have h := Fintype.card_congr (Equiv.sumCompl (· ∈ Set.range r))
  rw [Fintype.card_sum] at h
  have h3 : Fintype.card {i // i ∈ Set.range r} = 3 := by
    convert (Fintype.card_congr (Equiv.ofInjective r hr).symm).trans (Fintype.card_fin 3)
  calc Fintype.card {i // i ∉ Set.range r} + 3 =
        Fintype.card {a // a ∈ Set.range r} + Fintype.card {a // a ∉ Set.range r} := by
          rw [h3, add_comm]
    _ = Fintype.card ι := h

end Utilities.DeterminantExpansion
