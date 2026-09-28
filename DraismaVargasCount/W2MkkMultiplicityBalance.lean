import DraismaVargasCount.UnitWeightBalance
import DraismaVargas.LocalCases.W2MkkLimitColumns

/-!
# Denominator factors and multiplicity balance for Equation (8)

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  All three Figure 34 targets preserve the number of leaves.  Each regrown
column changes one incoming row by a unit reciprocal product: the factors
are `k₁-1`, `k₂-1`, and `k₃+1 = k₁+k₂`.  The balance below is on the actual
constructed family, in both orientations.  It retains the explicitly named
sharp incoming row denominators, only for members of nonzero determinant.
Those three sharp denominators are derived from an incoming presentation in
`W2MkkIncomingDenominator` (`incomingRowDenominator_member_eq`, `sum_signedMult_eq_zero`).
-/

namespace DraismaVargas.Count.W2MkkMultiplicityBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open W2MkkSourceCandidates W2MkkCommonBalance W2MkkLimitColumns
open TrivalentWeight UnitWeightBalance

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

/-- The perturbed incoming row at each position. -/
noncomputable def affectedRow : Fin 3 → StablePath data :=
  ![firstRow profile, secondRow profile, thirdRow profile]

/-- The incoming index on that row. -/
noncomputable def incomingIndex : Fin 3 → ℕ :=
  ![data.sourceEdgeIndex profile.first.1, data.sourceEdgeIndex profile.second.1,
    data.sourceEdgeIndex profile.third.1]

/-- The multiplicity factor contributed by the perturbed row. -/
noncomputable def factor : Fin 3 → ℕ :=
  ![data.sourceEdgeIndex profile.first.1 - 1, data.sourceEdgeIndex profile.second.1 - 1,
    data.sourceEdgeIndex profile.third.1 + 1]

/-- The old column used for each single-entry correction. -/
noncomputable def oldColumn : Fin 3 → target.edges :=
  ![star.edge profile.doubleLabel, star.edge profile.doubleLabel, star.edge profile.singleLabel]

/-- Detachment increases the reciprocal; joining decreases it. -/
def correctionSign : Fin 3 → ℤ := ![1, 1, -1]

theorem incomingIndex_pos (position : Fin 3) : 0 < incomingIndex profile position := by
  fin_cases position <;> exact sourceEdgeIndex_pos data _

theorem factor_pos (shape : Shape profile) (position : Fin 3) : 0 < factor profile position := by
  have hFirst := shape.one_lt_first
  have hSecond := shape.one_lt_second
  fin_cases position
  · change 0 < data.sourceEdgeIndex profile.first.1 - 1
    omega
  · change 0 < data.sourceEdgeIndex profile.second.1 - 1
    omega
  · exact Nat.succ_pos _

theorem correctionSign_unit (position : Fin 3) :
    correctionSign position = 1 ∨ correctionSign position = -1 := by
  fin_cases position <;> simp [correctionSign]

/-- The three literal new columns are single-row perturbations of old ones. -/
theorem newColumn_eq (input : W2SourceInput data star) (shape : Shape profile)
    (position : Fin 3) (path : StablePath data) :
    newColumn profile position path = StableSourceMatrix.matrix data path (oldColumn profile position) +
      if path = affectedRow profile position then
        (correctionSign position : ℚ) /
          ((incomingIndex profile position : ℚ) * (factor profile position : ℚ)) else 0 := by
  classical
  have hFirst : (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) :=
    by exact_mod_cast shape.one_lt_first
  have hSecond : (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) :=
    by exact_mod_cast shape.one_lt_second
  have hThird : (0 : ℚ) < (data.sourceEdgeIndex profile.third.1 : ℚ) :=
    by exact_mod_cast sourceEdgeIndex_pos data profile.third.1
  have hFirstCast : ((data.sourceEdgeIndex profile.first.1 - 1 : ℕ) : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) - 1 := by
    rw [Nat.cast_sub (by have := shape.one_lt_first; omega), Nat.cast_one]
  have hSecondCast : ((data.sourceEdgeIndex profile.second.1 - 1 : ℕ) : ℚ) =
      (data.sourceEdgeIndex profile.second.1 : ℚ) - 1 := by
    rw [Nat.cast_sub (by have := shape.one_lt_second; omega), Nat.cast_one]
  have hFirstNe : (data.sourceEdgeIndex profile.first.1 : ℚ) ≠ 0 := by linarith
  have hSecondNe : (data.sourceEdgeIndex profile.second.1 : ℚ) ≠ 0 := by linarith
  have hFirstSubNe : (data.sourceEdgeIndex profile.first.1 : ℚ) - 1 ≠ 0 := by linarith
  have hSecondSubNe : (data.sourceEdgeIndex profile.second.1 : ℚ) - 1 ≠ 0 := by linarith
  have hThirdNe : (data.sourceEdgeIndex profile.third.1 : ℚ) ≠ 0 := ne_of_gt hThird
  have hThirdAddNe : (data.sourceEdgeIndex profile.third.1 : ℚ) + 1 ≠ 0 := by linarith
  fin_cases position
  · change firstNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) +
        if path = firstRow profile then
          1 / ((data.sourceEdgeIndex profile.first.1 : ℚ) *
            ((data.sourceEdgeIndex profile.first.1 - 1 : ℕ) : ℚ)) else 0
    rw [firstNewColumn, hFirstCast, double_matrix_decomposition]
    split_ifs <;> field_simp <;> ring
  · change secondNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) +
        if path = secondRow profile then
          1 / ((data.sourceEdgeIndex profile.second.1 : ℚ) *
            ((data.sourceEdgeIndex profile.second.1 - 1 : ℕ) : ℚ)) else 0
    rw [secondNewColumn, hSecondCast, double_matrix_decomposition]
    split_ifs <;> field_simp <;> ring
  · change thirdNewColumn profile path =
      StableSourceMatrix.matrix data path (star.edge profile.singleLabel) +
        if path = thirdRow profile then
          -1 / ((data.sourceEdgeIndex profile.third.1 : ℚ) *
            ((data.sourceEdgeIndex profile.third.1 + 1 : ℕ) : ℚ)) else 0
    rw [thirdNewColumn, single_matrix_decomposition, Nat.cast_add, Nat.cast_one]
    rw [background_sum_eq profile input path profile.singleLabel profile.doubleLabel]
    have hThirdCast : (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) =
          (data.sourceEdgeIndex profile.third.1 : ℚ) + 1 := by
      have h := third_index_cast profile shape
      linarith
    rw [hThirdCast]
    split_ifs <;> field_simp <;> ring

/-- Consecutive indices are coprime, so a sharp incoming denominator supplies
the exact arithmetic condition required by the reciprocal correction. -/
theorem factor_coprime (shape : Shape profile) (position : Fin 3) :
    Nat.Coprime (factor profile position) (incomingIndex profile position) := by
  have hFirst := shape.one_lt_first
  have hSecond := shape.one_lt_second
  fin_cases position
  · change Nat.Coprime (data.sourceEdgeIndex profile.first.1 - 1)
      (data.sourceEdgeIndex profile.first.1)
    have hEq : data.sourceEdgeIndex profile.first.1 - 1 + 1 =
        data.sourceEdgeIndex profile.first.1 := by omega
    rw [← hEq]
    simp
  · change Nat.Coprime (data.sourceEdgeIndex profile.second.1 - 1)
      (data.sourceEdgeIndex profile.second.1)
    have hEq : data.sourceEdgeIndex profile.second.1 - 1 + 1 =
        data.sourceEdgeIndex profile.second.1 := by omega
    rw [← hEq]
    simp
  · change Nat.Coprime (data.sourceEdgeIndex profile.third.1 + 1)
      (data.sourceEdgeIndex profile.third.1)
    exact Nat.Coprime.symm (by simp)

section Denominators

variable {profile} {shape : Shape profile} (input : W2SourceInput data star)
  (limit : LimitColumns profile shape)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)

include input in
/-- The complete denominator-product factor, without row-distinctness assumptions. -/
theorem denominatorProduct_eq_factor (position : Fin 3)
    (hSharp : incomingRowDenominator data (affectedRow profile position) =
      incomingIndex profile position) :
    denominatorProduct (limit.labelling initial position).presentation =
      factor profile position * incomingDenominatorProduct data := by
  classical
  rw [denominatorProduct_of_commonMatrix (limit.labelling initial position)
    (limit.sourceCoordinates initial) (limit.targetCoordinates initial)
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
    · simp only [if_neg hPath, add_zero, one_mul]
      exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (affectedRow profile position) (fun _ ↦ factor profile position),
    if_pos (Finset.mem_univ _)]
  rfl

end Denominators

variable {profile}

/-- Every actual Figure 34 member splits the wall into two divalent target
vertices, including the remote member in each orientation. -/
theorem leafCount_member (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (position : Fin 3) :
    leafCount (graph target wall
      ((limitColumns input shape detach distinguished hConnected hGenus).member position).right) =
        leafCount target := by
  have hLocal (d : DetachData profile) :
      leafCount (graph target wall (localMember input shape d).right) = leafCount target :=
    leafCount_graph_of_divalent_split wall _ (detach_target_valencies shape d).1
      (detach_target_valencies shape d).2
  have hRemote (other : Fin degree)
      (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
      leafCount (graph target wall (remoteMember input shape other hOther).right) =
        leafCount target :=
    leafCount_graph_of_divalent_split wall _
      (detach_target_valencies (W2MkkTransport.swapShape shape input.valid.1 other hOther)
        (remoteDetach input shape other hOther)).1
      (detach_target_valencies (W2MkkTransport.swapShape shape input.valid.1 other hOther)
        (remoteDetach input shape other hOther)).2
  have hJoined : leafCount (graph target wall (joinedMember input shape distinguished).right) =
      leafCount target :=
    leafCount_graph_of_divalent_split wall _ (joined_target_valencies profile distinguished).1
      (joined_target_valencies profile distinguished).2
  unfold limitColumns
  split
  · fin_cases position
    · exact hLocal _
    · exact hRemote _ _
    · exact hJoined
  · fin_cases position
    · exact hRemote _ _
    · exact hLocal _
    · exact hJoined

/-- Equation (8)'s natural factors recover exactly its rational determinant
weights; the third equality is the profile's cardinality identity. -/
theorem sum_factor_det_eq_zero (input : W2SourceInput data star) (shape : Shape profile)
    (limit : LimitColumns profile shape)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    ∑ position : Fin 3,
      (factor profile position : ℚ) * (limit.squareMatrix initial position).det = 0 := by
  rw [Fin.sum_univ_three]
  change ((data.sourceEdgeIndex profile.first.1 - 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 0).det +
    ((data.sourceEdgeIndex profile.second.1 - 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 1).det +
    ((data.sourceEdgeIndex profile.third.1 + 1 : ℕ) : ℚ) *
      (limit.squareMatrix initial 2).det = 0
  rw [shape.third_index, Nat.cast_sub (by have := shape.one_lt_first; omega),
    Nat.cast_sub (by have := shape.one_lt_second; omega), Nat.cast_one, Nat.cast_add]
  exact limit.determinant_balance input initial

/-- Signed multiplicities balance on the actual constructed family, with
sharp denominators needed only at positions contributing nonzero determinant.
The sharp denominators remain hypotheses here; `W2MkkIncomingDenominator.sum_signedMult_eq_zero`
derives them from the incoming chart. -/
theorem sum_signedMult_eq_zero_of_conditional_sharp
    (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hConnected hGenus).member 0).datum coordinate)
    (hSharp : ∀ position : Fin 3,
      ((limitColumns input shape detach distinguished hConnected hGenus).squareMatrix
        initial position).det ≠ 0 →
      incomingRowDenominator data (affectedRow profile position) = incomingIndex profile position) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape detach distinguished hConnected hGenus).labelling
        initial position).presentation = 0 := by
  let limit := limitColumns input shape detach distinguished hConnected hGenus
  have hTerm (position : Fin 3) : signedMult (limit.labelling initial position).presentation =
      (incomingDenominatorProduct data : ℚ) / 2 ^ leafCount target *
        ((factor profile position : ℚ) * (limit.squareMatrix initial position).det) := by
    change (denominatorProduct (limit.labelling initial position).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member position).right) *
          (limit.squareMatrix initial position).det = _
    rw [leafCount_member input shape detach distinguished hConnected hGenus position]
    by_cases hDet : (limit.squareMatrix initial position).det = 0
    · rw [hDet]
      ring
    · rw [denominatorProduct_eq_factor input limit initial position (hSharp position hDet)]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun position _ ↦ hTerm position, ← Finset.mul_sum,
    sum_factor_det_eq_zero input shape limit initial, mul_zero]

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The same conditional balance with the source-derived canonical labelling. -/
theorem sum_signedMult_canonical_eq_zero_of_conditional_sharp
    (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSharp : ∀ position : Fin 3,
      ((limitColumns input shape detach distinguished hConnected hGenus).squareMatrix
        ((limitColumns input shape detach distinguished hConnected hGenus).canonicalInitialLabelling input)
          position).det ≠ 0 →
      incomingRowDenominator data (affectedRow profile position) = incomingIndex profile position) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape detach distinguished hConnected hGenus).labelling
        ((limitColumns input shape detach distinguished hConnected hGenus).canonicalInitialLabelling input)
          position).presentation = 0 :=
  sum_signedMult_eq_zero_of_conditional_sharp input shape detach distinguished hConnected hGenus
    ((limitColumns input shape detach distinguished hConnected hGenus).canonicalInitialLabelling input) hSharp

end DraismaVargas.Count.W2MkkMultiplicityBalance
