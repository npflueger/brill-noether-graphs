module

public import DraismaVargasCount.UnitWeightBalance
public import DraismaVargas.LocalCases.W3FourRegrownColumnSeam

@[expose] public section

/-!
# Equation (2): arithmetic assembly on Figure 28's honest matrices

Equation (2) of Draisma--Vargas Part I (arXiv:1909.12924) is the balance in case
`{w3-r1-nd3-t2-(a=k4)}`, over the four members of that paper's Figure 28.
The unchanged member has factor one; the three single-row perturbations have
factors `k₄-1`, `k₂+1`, `k₃+1`. Denominator hypotheses below are requested only
on determinant support. `W3FourCountBalance` supplies them from actual members.
-/

namespace DraismaVargas.Count.W3FourMultiplicityBalance

open DraismaVargas.Infrastructure GluingDatum TargetExpansion
open DraismaVargas.LocalCases W4StableSource StableSourceMatrix
open W3FourClosure W3FourStableGraph W3FourHonestBalance W3FourRegrownColumnSeam
open TrivalentWeight UnitWeightBalance

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {geometry : FourStarGeometry data wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable (receipts : Figure28Receipts data wall geometry)

noncomputable def oldEntry (row : Option target.edges) (column : target.edges) : ℚ :=
  columnSum (receipts.rows.oldPath row) column

noncomputable def rowDen (row : Option target.edges) : ℕ :=
  commonDenominator Finset.univ (oldEntry receipts row)

noncomputable def baseProduct : ℕ := ∏ row, rowDen receipts row

noncomputable def memberMatrix (position : Fin 4) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  LengthMatrixPresentation.matrix (receipts.presentation position)

theorem matrix_some (position : Fin 4) (row : Option target.edges) (column : target.edges) :
    memberMatrix receipts position row (some column) = oldEntry receipts row column :=
  MemberColumn.matrix_some_eq receipts.member receipts.rows.oldPath position row column

theorem denominatorProduct_eq (position : Fin 4) :
    denominatorProduct (receipts.presentation position) =
      ∏ row, Nat.lcm (memberMatrix receipts position row none).den (rowDen receipts row) := by
  unfold denominatorProduct rowDen rowDenominator
  apply Finset.prod_congr rfl
  intro row _
  rw [commonDenominator_option]
  congr 1
  exact congrArg (commonDenominator Finset.univ) (funext (matrix_some receipts position row))

theorem oldEntry_den_dvd (row : Option target.edges) (column : target.edges) :
    (oldEntry receipts row column).den ∣ rowDen receipts row :=
  den_dvd_commonDenominator _ _ (Finset.mem_univ column)

noncomputable def term (row selected : Option target.edges) (index : ℕ) : ℚ :=
  if row = selected then 1 / (index : ℚ) else 0

theorem matrix_one (row : Option target.edges) :
    memberMatrix receipts 0 row none =
      term row receipts.rows.rowGrow (indexGrow geometry) +
      term row receipts.rows.rowOther (indexOther geometry) +
      (oldEntry receipts row geometry.largestTarget -
        term row receipts.rows.rowLargest (indexLargest geometry)) := by
  rw [memberMatrix, Figure28Receipts.presentation, MemberColumn.matrix_none_eq,
    MemberColumn.selectedNewSum, receipts.selected_one, receipts.background_one,
    receipts.rows.selected_largest]
  simp only [List.map_append, List.sum_append, single, term]
  split_ifs <;> simp [receipts.index_one_grow, receipts.index_one_other, oldEntry]

/-- The remaining three positions have one reciprocal correction each. -/
noncomputable def affectedRow : Fin 3 → Option target.edges :=
  ![receipts.rows.rowLargest, receipts.rows.rowGrow, receipts.rows.rowOther]

noncomputable def oldColumn : Fin 3 → target.edges :=
  ![geometry.largestTarget, geometry.growTarget, geometry.otherTarget]

noncomputable def index : Fin 3 → ℕ :=
  ![indexLargest geometry, indexGrow geometry, indexOther geometry]

noncomputable def factor : Fin 3 → ℕ :=
  ![indexLargest geometry - 1, indexGrow geometry + 1, indexOther geometry + 1]

def correctionSign : Fin 3 → ℤ := ![1, -1, -1]

theorem index_pos (position : Fin 3) : 0 < index (geometry := geometry) position := by
  fin_cases position <;> exact SheetPartition.blockCard_pos _ _

theorem factor_pos (position : Fin 3) : 0 < factor (geometry := geometry) position := by
  have h := indexLargest_eq geometry
  have hG : 0 < indexGrow geometry := SheetPartition.blockCard_pos _ _
  have hO : 0 < indexOther geometry := SheetPartition.blockCard_pos _ _
  fin_cases position
  · change 0 < indexLargest geometry - 1
    omega
  · exact Nat.succ_pos _
  · exact Nat.succ_pos _

theorem factor_coprime (position : Fin 3) :
    Nat.Coprime (factor (geometry := geometry) position) (index (geometry := geometry) position) := by
  fin_cases position
  · change Nat.Coprime (indexLargest geometry - 1) (indexLargest geometry)
    have h : indexLargest geometry - 1 + 1 = indexLargest geometry := by
      have := index_pos (geometry := geometry) 0
      change 0 < indexLargest geometry at this
      omega
    rw [← h]
    simp
  · exact Nat.Coprime.symm (by simp [factor, index])
  · exact Nat.Coprime.symm (by simp [factor, index])

theorem matrix_two (row : Option target.edges) :
    memberMatrix receipts 1 row none = oldEntry receipts row geometry.largestTarget +
      if row = receipts.rows.rowLargest then
        1 / ((indexLargest geometry : ℚ) * (indexLargest geometry - 1 : ℕ)) else 0 := by
  have hCast : ((indexLargest geometry - 1 : ℕ) : ℚ) = (indexLargest geometry : ℚ) - 1 := by
    rw [Nat.cast_sub (by have := index_pos (geometry := geometry) 0; exact this), Nat.cast_one]
  have hNew : newIndex (receipts.member 1).candidate geometry.growAnchor =
      indexLargest geometry - 1 := by
    have := receipts.index_two
    rw [← indexLargest_eq geometry] at this
    omega
  have h0 : (indexLargest geometry : ℚ) ≠ 0 := by
    exact_mod_cast (index_pos (geometry := geometry) 0).ne'
  have h1 : (indexLargest geometry : ℚ) - 1 ≠ 0 := by
    rw [← hCast]
    exact_mod_cast (factor_pos (geometry := geometry) 0).ne'
  rw [memberMatrix, Figure28Receipts.presentation, MemberColumn.matrix_none_eq,
    MemberColumn.selectedNewSum, receipts.selected_two, receipts.background_two,
    receipts.rows.selected_largest]
  by_cases hr : row = receipts.rows.rowLargest
  · simp [single, hr, hNew, hCast, oldEntry]
    field_simp
    ring
  · simp [single, hr, oldEntry]

theorem matrix_three (row : Option target.edges) :
    memberMatrix receipts 2 row none = oldEntry receipts row geometry.growTarget +
      if row = receipts.rows.rowGrow then
        -1 / ((indexGrow geometry : ℚ) * (indexGrow geometry + 1 : ℕ)) else 0 := by
  have h0 : (indexGrow geometry : ℚ) ≠ 0 := by
    exact_mod_cast (SheetPartition.blockCard_pos
      (data.edgePartition geometry.growTarget) geometry.growAnchor).ne'
  have h1 : (indexGrow geometry : ℚ) + 1 ≠ 0 := by positivity
  rw [memberMatrix, Figure28Receipts.presentation, MemberColumn.matrix_none_eq,
    MemberColumn.selectedNewSum, receipts.selected_three, receipts.background_three,
    receipts.rows.selected_grow]
  by_cases hr : row = receipts.rows.rowGrow
  · simp [single, hr, receipts.index_three, oldEntry]
    field_simp
    ring
  · simp [single, hr, oldEntry]

theorem matrix_four (row : Option target.edges) :
    memberMatrix receipts 3 row none = oldEntry receipts row geometry.otherTarget +
      if row = receipts.rows.rowOther then
        -1 / ((indexOther geometry : ℚ) * (indexOther geometry + 1 : ℕ)) else 0 := by
  have h0 : (indexOther geometry : ℚ) ≠ 0 := by
    exact_mod_cast (SheetPartition.blockCard_pos
      (data.edgePartition geometry.otherTarget) geometry.otherAnchor).ne'
  have h1 : (indexOther geometry : ℚ) + 1 ≠ 0 := by positivity
  rw [memberMatrix, Figure28Receipts.presentation, MemberColumn.matrix_none_eq,
    MemberColumn.selectedNewSum, receipts.selected_four, receipts.background_four,
    receipts.rows.selected_other]
  by_cases hr : row = receipts.rows.rowOther
  · simp [single, hr, receipts.index_four, oldEntry]
    field_simp
    ring
  · simp [single, hr, oldEntry]

theorem matrix_perturbed (position : Fin 3) (row : Option target.edges) :
    memberMatrix receipts position.succ row none =
      oldEntry receipts row (oldColumn (geometry := geometry) position) +
        if row = affectedRow receipts position then
          (correctionSign position : ℚ) /
            ((index (geometry := geometry) position : ℚ) *
              (factor (geometry := geometry) position : ℚ)) else 0 := by
  fin_cases position
  · simpa [affectedRow, oldColumn, index, factor, correctionSign] using matrix_two receipts row
  · simpa [affectedRow, oldColumn, index, factor, correctionSign] using matrix_three receipts row
  · simpa [affectedRow, oldColumn, index, factor, correctionSign] using matrix_four receipts row

theorem term_den_dvd (row selected : Option target.edges) (k d : ℕ)
    (h : row = selected → k ∣ d) : (term row selected k).den ∣ d := by
  unfold term
  split_ifs with he
  · exact (den_one_div_natCast k).trans (h he)
  · simp

theorem denominatorProduct_one
    (hGrow : indexGrow geometry ∣ rowDen receipts receipts.rows.rowGrow)
    (hOther : indexOther geometry ∣ rowDen receipts receipts.rows.rowOther)
    (hLargest : indexLargest geometry ∣ rowDen receipts receipts.rows.rowLargest) :
    denominatorProduct (receipts.presentation 0) = baseProduct receipts := by
  rw [denominatorProduct_eq]
  apply Finset.prod_congr rfl
  intro row _
  apply lcm_den_eq_right
  rw [matrix_one]
  apply den_add_dvd
  · exact den_add_dvd
      (term_den_dvd _ _ _ _ (by rintro rfl; exact hGrow))
      (term_den_dvd _ _ _ _ (by rintro rfl; exact hOther))
  · rw [sub_eq_add_neg]
    apply den_add_dvd (oldEntry_den_dvd receipts row _)
    rw [den_neg]
    exact term_den_dvd _ _ _ _ (by rintro rfl; exact hLargest)

theorem denominatorProduct_perturbed (position : Fin 3)
    (hSharp : rowDen receipts (affectedRow receipts position) = index (geometry := geometry) position) :
    denominatorProduct (receipts.presentation position.succ) =
      factor (geometry := geometry) position * baseProduct receipts := by
  rw [denominatorProduct_eq]
  have hTerm (row : Option target.edges) :
      Nat.lcm (memberMatrix receipts position.succ row none).den (rowDen receipts row) =
        (if row = affectedRow receipts position then factor (geometry := geometry) position else 1) *
          rowDen receipts row := by
    rw [matrix_perturbed]
    by_cases h : row = affectedRow receipts position
    · subst row
      simp only [eq_self, ite_true]
      exact lcm_den_add_unit_inv (oldEntry receipts (affectedRow receipts position))
        (oldColumn (geometry := geometry) position) (index_pos position) (factor_pos position)
        (by fin_cases position <;> simp [correctionSign])
        (by change _ ∣ rowDen receipts _; rw [hSharp])
        (by change Nat.Coprime _ (rowDen receipts _); rw [hSharp]; exact factor_coprime position)
    · simp only [ite_eq_right h, add_zero, one_mul]
      exact lcm_den_eq_right (oldEntry_den_dvd receipts row _)
  rw [Finset.prod_congr rfl fun row _ ↦ hTerm row, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (affectedRow receipts position)
      (fun _ ↦ factor (geometry := geometry) position), ite_eq_left (Finset.mem_univ _)]
  rfl

noncomputable def weight : Fin 4 → ℕ :=
  ![1, indexLargest geometry - 1, indexGrow geometry + 1, indexOther geometry + 1]

theorem weight_det_sum :
    ∑ p, (weight (geometry := geometry) p : ℚ) * (memberMatrix receipts p).det = 0 := by
  have h := receipts.gaugeFamily.positiveBalance.2
  have hWeights : (fun p ↦ (weight (geometry := geometry) p : ℚ)) =
      receipts.gaugeFamily.weight := by
    funext p
    have hG : 0 < indexGrow geometry := SheetPartition.blockCard_pos _ _
    have hO : 0 < indexOther geometry := SheetPartition.blockCard_pos _ _
    fin_cases p
    · rfl
    · change ((indexLargest geometry - 1 : ℕ) : ℚ) =
        (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1
      rw [indexLargest_eq, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    · norm_num [weight, Figure28Receipts.gaugeFamily, equationTwoGaugeFamily]
    · norm_num [weight, Figure28Receipts.gaugeFamily, equationTwoGaugeFamily]
  change ∑ p, receipts.gaugeFamily.weight p * (memberMatrix receipts p).det = 0 at h
  rw [← hWeights] at h
  exact h

theorem sum_signedMult_eq_zero_of_receipts
    (hLeaf : ∀ p, leafCount (graph target wall (receipts.member p).candidate.right) = leafCount target)
    (hLower : (memberMatrix receipts 0).det ≠ 0 →
      indexGrow geometry ∣ rowDen receipts receipts.rows.rowGrow ∧
      indexOther geometry ∣ rowDen receipts receipts.rows.rowOther ∧
      indexLargest geometry ∣ rowDen receipts receipts.rows.rowLargest)
    (hSharp : ∀ p : Fin 3, (memberMatrix receipts p.succ).det ≠ 0 →
      rowDen receipts (affectedRow receipts p) = index (geometry := geometry) p) :
    ∑ p, signedMult (receipts.presentation p) = 0 := by
  have hDen (p : Fin 4) (hDet : (memberMatrix receipts p).det ≠ 0) :
      denominatorProduct (receipts.presentation p) = weight (geometry := geometry) p * baseProduct receipts := by
    induction p using Fin.cases with
    | zero =>
      simpa [weight] using denominatorProduct_one receipts (hLower hDet).1
        (hLower hDet).2.1 (hLower hDet).2.2
    | succ q =>
      simpa only [weight, factor, Matrix.cons_val_succ] using
        denominatorProduct_perturbed receipts q (hSharp q hDet)
  have hTerm (p : Fin 4) : signedMult (receipts.presentation p) =
      (baseProduct receipts : ℚ) / 2 ^ leafCount target *
        ((weight (geometry := geometry) p : ℚ) * (memberMatrix receipts p).det) := by
    unfold signedMult
    rw [hLeaf]
    change _ * (memberMatrix receipts p).det = _
    by_cases h : (memberMatrix receipts p).det = 0
    · rw [h]; ring
    · rw [hDen p h]; push_cast; ring
  rw [Finset.sum_congr rfl fun p _ ↦ hTerm p, ← Finset.mul_sum, weight_det_sum, mul_zero]

end DraismaVargas.Count.W3FourMultiplicityBalance
