module

public import DraismaVargasCount.W2PIncomingDenominator
public import DraismaVargas.LocalCases.W2PArbitraryExit

@[expose] public section

/-!
# Equation (9): signed multiplicity balance for the actual W2P family

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-P}`, Figure 35 and
Equation (9).  The three factors are `k₁+1`, `k₂+1`, and `k₃-1 = k₁+k₂`.
All targets preserve the leaf count. The final theorem starts with one
identified full-dimensional member and derives sharp incoming denominators
only for nonsingular outgoing members; singular members contribute zero.
The third member `M⁽³⁾` (Base II.1.P) is `W2PSourceCandidates.thirdMember`, built on the
Figure 35 shape `W2PSourceCandidates.leftSplitResolution`, which preserves the source genus.
-/

namespace DraismaVargas.Count.W2PMultiplicityBalance

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix FullDimensionalSource
open W2PSourceCandidates W2PCommonBalance
open TrivalentWeight UnitWeightBalance

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

/-- The one incoming row perturbed by each member. -/
noncomputable def affectedRow : Fin 3 → StablePath data :=
  ![firstRow profile, secondRow profile, thirdRow profile]

noncomputable def incomingIndex : Fin 3 → ℕ :=
  ![data.sourceEdgeIndex profile.first.1, data.sourceEdgeIndex profile.second.1,
    data.sourceEdgeIndex profile.third.1]

/-- Equation (9)'s natural denominator factors. -/
noncomputable def factor : Fin 3 → ℕ :=
  ![data.sourceEdgeIndex profile.first.1 + 1, data.sourceEdgeIndex profile.second.1 + 1,
    data.sourceEdgeIndex profile.third.1 - 1]

noncomputable def oldColumn : Fin 3 → target.edges :=
  ![star.edge profile.doubleLabel, star.edge profile.doubleLabel, star.edge profile.singleLabel]

/-- Merging decreases the reciprocal; detachment increases it. -/
def correctionSign : Fin 3 → ℤ := ![-1, -1, 1]

theorem incomingIndex_pos (position : Fin 3) : 0 < incomingIndex profile position := by
  fin_cases position <;> exact sourceEdgeIndex_pos data _

theorem factor_pos (shape : Shape profile) (position : Fin 3) : 0 < factor profile position := by
  have hFirst := sourceEdgeIndex_pos data profile.first.1
  have hThird := shape.third_index
  fin_cases position
  · exact Nat.succ_pos _
  · exact Nat.succ_pos _
  · change 0 < data.sourceEdgeIndex profile.third.1 - 1
    omega

theorem correctionSign_unit (position : Fin 3) :
    correctionSign position = 1 ∨ correctionSign position = -1 := by
  fin_cases position <;> simp [correctionSign]

/-- No distinctness of the three affected stable rows is required. -/
theorem newColumn_eq (input : W2SourceInput data star) (shape : Shape profile)
    (position : Fin 3) (path : StablePath data) :
    newColumn profile position path = StableSourceMatrix.matrix data path (oldColumn profile position) +
      if path = affectedRow profile position then
        (correctionSign position : ℚ) /
          ((incomingIndex profile position : ℚ) * (factor profile position : ℚ)) else 0 := by
  classical
  have hFirst : (0 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) :=
    by exact_mod_cast sourceEdgeIndex_pos data profile.first.1
  have hSecond : (0 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) :=
    by exact_mod_cast sourceEdgeIndex_pos data profile.second.1
  have hThird : (1 : ℚ) < (data.sourceEdgeIndex profile.third.1 : ℚ) := by
    have := third_index_cast profile shape
    linarith
  have hThirdCast : ((data.sourceEdgeIndex profile.third.1 - 1 : ℕ) : ℚ) =
      (data.sourceEdgeIndex profile.third.1 : ℚ) - 1 := by
    rw [Nat.cast_sub (by have := shape.third_index; omega), Nat.cast_one]
  have hFirstNe : (data.sourceEdgeIndex profile.first.1 : ℚ) ≠ 0 := ne_of_gt hFirst
  have hSecondNe : (data.sourceEdgeIndex profile.second.1 : ℚ) ≠ 0 := ne_of_gt hSecond
  have hFirstAddNe : (data.sourceEdgeIndex profile.first.1 : ℚ) + 1 ≠ 0 := by linarith
  have hSecondAddNe : (data.sourceEdgeIndex profile.second.1 : ℚ) + 1 ≠ 0 := by linarith
  have hThirdNe : (data.sourceEdgeIndex profile.third.1 : ℚ) ≠ 0 := by linarith
  have hThirdSubNe : (data.sourceEdgeIndex profile.third.1 : ℚ) - 1 ≠ 0 := by linarith
  fin_cases position
  · change firstNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) +
        if path = firstRow profile then
          -1 / ((data.sourceEdgeIndex profile.first.1 : ℚ) *
            ((data.sourceEdgeIndex profile.first.1 + 1 : ℕ) : ℚ)) else 0
    rw [firstNewColumn, Nat.cast_add, Nat.cast_one, double_matrix_decomposition]
    split_ifs <;> field_simp <;> ring
  · change secondNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) +
        if path = secondRow profile then
          -1 / ((data.sourceEdgeIndex profile.second.1 : ℚ) *
            ((data.sourceEdgeIndex profile.second.1 + 1 : ℕ) : ℚ)) else 0
    rw [secondNewColumn, Nat.cast_add, Nat.cast_one, double_matrix_decomposition]
    split_ifs <;> field_simp <;> ring
  · change thirdNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.singleLabel) +
        if path = thirdRow profile then
          1 / ((data.sourceEdgeIndex profile.third.1 : ℚ) *
            ((data.sourceEdgeIndex profile.third.1 - 1 : ℕ) : ℚ)) else 0
    rw [thirdNewColumn, single_matrix_decomposition, hThirdCast]
    rw [background_sum_eq profile input path profile.singleLabel profile.doubleLabel]
    have hSum : (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) =
          (data.sourceEdgeIndex profile.third.1 : ℚ) - 1 := by
      have := third_index_cast profile shape
      linarith
    rw [hSum]
    split_ifs <;> field_simp <;> ring

theorem factor_coprime (shape : Shape profile) (position : Fin 3) :
    Nat.Coprime (factor profile position) (incomingIndex profile position) := by
  fin_cases position
  · change Nat.Coprime (data.sourceEdgeIndex profile.first.1 + 1)
      (data.sourceEdgeIndex profile.first.1)
    exact Nat.Coprime.symm (by simp)
  · change Nat.Coprime (data.sourceEdgeIndex profile.second.1 + 1)
      (data.sourceEdgeIndex profile.second.1)
    exact Nat.Coprime.symm (by simp)
  · change Nat.Coprime (data.sourceEdgeIndex profile.third.1 - 1)
      (data.sourceEdgeIndex profile.third.1)
    have hEq : data.sourceEdgeIndex profile.third.1 - 1 + 1 =
        data.sourceEdgeIndex profile.third.1 := by have := shape.third_index; omega
    rw [← hEq]
    simp

section Denominators

variable {profile} {shape : Shape profile} (input : W2SourceInput data star)
  (limit : LimitColumns profile shape)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)

include input in
/-- One sharp incoming row determines the whole denominator-product factor. -/
theorem denominatorProduct_eq_factor (position : Fin 3)
    (hSharp : incomingRowDenominator data (affectedRow profile position) =
      incomingIndex profile position) :
    denominatorProduct (limit.labelling initial position).presentation =
      factor profile position * incomingDenominatorProduct data := by
  classical
  rw [denominatorProduct_of_commonMatrix (limit.labelling initial position)
    (limit.sourceCoordinates initial) (LimitColumns.targetCoordinates initial)
    (limit.commonMatrix position) (limit.squareMatrix_common initial position)
    (limit.commonMatrix_retained position)]
  have hTerm (path : StablePath data) :
      Nat.lcm (limit.commonMatrix position path none).den (incomingRowDenominator data path) =
        (if path = affectedRow profile position then factor profile position else 1) *
          incomingRowDenominator data path := by
    rw [limit.commonMatrix_new, newColumn_eq profile input shape]
    by_cases hPath : path = affectedRow profile position
    · subst path
      simp only [eq_self, ite_true]
      exact lcm_den_add_unit_inv (fun place ↦ StableSourceMatrix.matrix data
        (affectedRow profile position) place) (oldColumn profile position)
        (incomingIndex_pos profile position) (factor_pos profile shape position)
        (correctionSign_unit position) (by
          change incomingIndex profile position ∣ incomingRowDenominator data (affectedRow profile position)
          rw [hSharp])
        (by change Nat.Coprime _ (incomingRowDenominator data _); rw [hSharp];
            exact factor_coprime profile shape position)
    · simp only [ite_eq_right hPath, add_zero, one_mul]
      exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (affectedRow profile position) (fun _ ↦ factor profile position),
    ite_eq_left (Finset.mem_univ _)]
  rfl

end Denominators

variable {profile}

theorem leafCount_member (shape : Shape profile) (position : Fin 3) :
    leafCount (graph target wall (members profile shape position).right) = leafCount target := by
  fin_cases position
  · exact leafCount_graph_of_divalent_split wall _
      (firstMember_target_valencies shape).1 (firstMember_target_valencies shape).2
  · exact leafCount_graph_of_divalent_split wall _
      (secondMember_target_valencies shape).1 (secondMember_target_valencies shape).2
  · exact leafCount_graph_of_divalent_split wall _
      (thirdMember_target_valencies shape).1 (thirdMember_target_valencies shape).2

theorem sum_factor_det_eq_zero (input : W2SourceInput data star) (shape : Shape profile)
    (limit : LimitColumns profile shape)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    ∑ position : Fin 3,
      (factor profile position : ℚ) * (limit.squareMatrix initial position).det = 0 := by
  rw [Fin.sum_univ_three]
  change ((data.sourceEdgeIndex profile.first.1 + 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 0).det +
    ((data.sourceEdgeIndex profile.second.1 + 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 1).det +
    ((data.sourceEdgeIndex profile.third.1 - 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 2).det = 0
  rw [shape.third_index, Nat.add_sub_cancel]
  push_cast
  exact limit.determinant_balance input initial

/-- Arithmetic assembly, requesting sharpness only on determinant support. -/
theorem sum_signedMult_eq_zero_of_conditional_sharp
    (input : W2SourceInput data star) (shape : Shape profile)
    (limit : LimitColumns profile shape)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (hSharp : ∀ position : Fin 3, (limit.squareMatrix initial position).det ≠ 0 →
      incomingRowDenominator data (affectedRow profile position) = incomingIndex profile position) :
    ∑ position : Fin 3, signedMult (limit.labelling initial position).presentation = 0 := by
  have hTerm (position : Fin 3) : signedMult (limit.labelling initial position).presentation =
      (incomingDenominatorProduct data : ℚ) / 2 ^ leafCount target *
        ((factor profile position : ℚ) * (limit.squareMatrix initial position).det) := by
    change (denominatorProduct (limit.labelling initial position).presentation : ℚ) /
        2 ^ leafCount (graph target wall (members profile shape position).right) *
          (limit.squareMatrix initial position).det = _
    rw [leafCount_member shape position]
    by_cases hDet : (limit.squareMatrix initial position).det = 0
    · rw [hDet]
      ring
    · rw [denominatorProduct_eq_factor input limit initial position (hSharp position hDet)]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun position _ ↦ hTerm position, ← Finset.mul_sum,
    sum_factor_det_eq_zero input shape limit initial, mul_zero]

/-- **Equation (9), on all three actual Figure 35 members.** One identified
full-dimensional incoming member suffices. No outgoing nonsingularity,
row-distinctness, or sharp-denominator receipts are assumed. -/
theorem sum_signedMult_eq_zero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (members profile shape incoming).datum coordinate) :
    ∑ position : Fin 3, signedMult
      (W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD position).presentation = 0 := by
  apply sum_signedMult_eq_zero_of_conditional_sharp input shape
    (W2PLimitMatrix.limitColumns input shape)
    (W2PArbitraryExit.initialLabelling input shape incoming incomingFD)
  intro position hDet
  have fd := W2PArbitraryExit.outgoingPresentation input shape hConnected hGenus
    incoming position incomingFD hDet
  fin_cases position
  · exact W2PIncomingDenominator.incomingRowDenominator_first input shape fd
  · exact W2PIncomingDenominator.incomingRowDenominator_second input shape fd
  · exact W2PIncomingDenominator.incomingRowDenominator_third input shape fd

end DraismaVargas.Count.W2PMultiplicityBalance
