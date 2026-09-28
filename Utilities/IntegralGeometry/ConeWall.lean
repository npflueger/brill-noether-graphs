import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Rational algebra at a one-column cone wall

Only Mathlib is used. These are the common-column and determinant-sign steps
of the deformation argument of Draisma--Vargas Part I (arXiv:1909.12924), in
which a tropical morphism is carried across a codimension-one wall of the
moduli space; constructing a valid outgoing gluing datum is a separate
combinatorial obligation, not an assumption hidden by this file.
-/

namespace DraismaVargas.Infrastructure

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Compatible resolutions have the same length columns off the collapsed edge. -/
def AgreeOffColumn (A B : Matrix ι ι ℚ) (k : ι) : Prop :=
  ∀ i j, j ≠ k → A i j = B i j

/-- Both resolutions send a wall vector to the same stable metric. -/
theorem mulVec_eq_on_wall {A B : Matrix ι ι ℚ} {k : ι}
    (h : AgreeOffColumn A B k) {z : ι → ℚ} (hz : z k = 0) :
    A.mulVec z = B.mulVec z := by
  ext i
  change (∑ j, A i j * z j) = ∑ j, B i j * z j
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = k
  · simp [hj, hz]
  · rw [h i j hj]

/-- Replacing the changing column gives the same Cramer numerator. -/
theorem cramer_eq_of_agreeOffColumn {A B : Matrix ι ι ℚ} {k : ι}
    (h : AgreeOffColumn A B k) (y : ι → ℚ) :
    Matrix.cramer A y k = Matrix.cramer B y k := by
  simp only [Matrix.cramer_apply]
  congr 1
  ext i j
  by_cases hj : j = k
  · simp [hj]
  · simp [hj, h i j hj]

/-- The determinant-times-crossing-coordinate identity requires only actual
solutions of the two linear systems, not a choice of inverse. -/
theorem determinant_coordinate_eq {A B : Matrix ι ι ℚ} {k : ι}
    (h : AgreeOffColumn A B k) {u v : ι → ℚ}
    (huv : A.mulVec u = B.mulVec v) :
    A.det * u k = B.det * v k := by
  have hA := Matrix.det_updateCol_sum A k u
  have hB := Matrix.det_updateCol_sum B k v
  have hc := cramer_eq_of_agreeOffColumn h (A.mulVec u)
  have hm (M : Matrix ι ι ℚ) (w : ι → ℚ) :
      (fun i => ∑ j, w j • M i j) = M.mulVec w := by
    ext i
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hm] at hA hB
  simp only [smul_eq_mul] at hA hB
  simp only [Matrix.cramer_apply] at hc
  rw [← huv] at hB
  rw [hA, hB] at hc
  nlinarith [hc]

/-- Opposite determinant signs turn a negative incoming coordinate positive. -/
theorem crossing_coordinate_pos {a b u v : ℚ}
    (hsign : a * b < 0) (hcoord : a * u = b * v) (hu : u < 0) : 0 < v := by
  by_contra hv
  have hv' : v ≤ 0 := le_of_not_gt hv
  rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hp := mul_neg_of_pos_of_neg ha hu
    have hn := mul_nonneg_of_nonpos_of_nonpos (le_of_lt hb) hv'
    linarith
  · have hp := mul_pos_of_neg_of_neg ha hu
    have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) hv'
    linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A positive balancing relation forces a determinant of the opposite sign.
Only enough valid candidates for a balancing relation are needed; this makes
no claim that the candidates enumerate all resolutions. -/
theorem exists_opposite_of_balancing (s : Finset ι) (weight value : ι → ℚ)
    (hw : ∀ i ∈ s, 0 < weight i) (hbalance : ∑ i ∈ s, weight i * value i = 0)
    {k : ι} (hk : k ∈ s) (hvalue : value k ≠ 0) :
    ∃ j ∈ s, value k * value j < 0 := by
  by_contra h
  push Not at h
  have hnonneg : ∀ j ∈ s, 0 ≤ weight j * (value k * value j) := by
    intro j hj
    exact mul_nonneg (le_of_lt (hw j hj)) (h j hj)
  have hpos : 0 < ∑ j ∈ s, weight j * (value k * value j) := by
    apply Finset.sum_pos' hnonneg
    exact ⟨k, hk, mul_pos (hw k hk) (mul_self_pos.mpr hvalue)⟩
  have heq : (∑ j ∈ s, weight j * (value k * value j)) =
      value k * (∑ j ∈ s, weight j * value j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, hbalance, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

omit [Fintype ι] [DecidableEq ι] in
/-- A finite family of positive coordinates, or zero coordinates with positive
outgoing derivative, stays positive for an explicit sufficiently small step.
The proof uses finite minima and rational inequalities, not topology. -/
theorem exists_positive_step (s : Finset ι) (z v : ι → ℚ)
    (h : ∀ i ∈ s, 0 < z i ∨ (z i = 0 ∧ 0 < v i)) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ → ∀ i ∈ s, 0 < z i + t * v i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hstep⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have haStep : ∃ ε : ℚ, 0 < ε ∧ ∀ t : ℚ, 0 < t → t ≤ ε → 0 < z a + t * v a := by
      rcases h a (Finset.mem_insert_self _ _) with hz | ⟨hz, hv⟩
      · have hd : 0 < |v a| + 1 := by positivity
        refine ⟨z a / (|v a| + 1), div_pos hz hd, ?_⟩
        intro t ht hbound
        have hb := (le_div_iff₀ hd).mp hbound
        have hv := mul_le_mul_of_nonneg_left (neg_abs_le (v a)) ht.le
        nlinarith
      · exact ⟨1, by norm_num, fun t ht _ => by simpa [hz] using mul_pos ht hv⟩
    obtain ⟨ε, hε, haStep⟩ := haStep
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro t ht hbound i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact haStep t ht (hbound.trans (min_le_right _ _))
    · exact hstep t ht (hbound.trans (min_le_left _ _)) i hi

/-- The entire local rational deformation step, given a compatible outgoing
matrix. Supplying that matrix is the combinatorial part of the Draisma--Vargas
argument, which this file does not address. -/
theorem crosses_into_positive_cone {A B : Matrix ι ι ℚ} {k : ι}
    (h : AgreeOffColumn A B k) (hsign : A.det * B.det < 0)
    {z u v : ι → ℚ} (hz : z k = 0) (hzpos : ∀ i, i ≠ k → 0 < z i)
    (huv : A.mulVec u = B.mulVec v) (hu : u k < 0) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
      (∀ i, 0 < (z + t • v) i) ∧
      B.mulVec (z + t • v) = A.mulVec z + t • A.mulVec u := by
  have hv : 0 < v k := crossing_coordinate_pos hsign (determinant_coordinate_eq h huv) hu
  obtain ⟨δ, hδ, hstep⟩ := exists_positive_step Finset.univ z v (by
    intro i _
    by_cases hi : i = k
    · exact Or.inr ⟨hi ▸ hz, hi ▸ hv⟩
    · exact Or.inl (hzpos i hi))
  refine ⟨δ, hδ, ?_⟩
  intro t ht hbound
  constructor
  · intro i
    exact hstep t ht hbound i (Finset.mem_univ i)
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← mulVec_eq_on_wall h hz, ← huv]

end DraismaVargas.Infrastructure
