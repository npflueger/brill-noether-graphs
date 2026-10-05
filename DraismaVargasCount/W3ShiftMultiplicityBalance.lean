module

public import DraismaVargasCount.W3ShiftIncomingDenominator
public import DraismaVargas.LocalCases.W3ShiftStableIncidence

@[expose] public section

/-!
# Multiplicity balance for one Equation (3) shift pair

For a shrink/grow pair as in Figure 29 of Draisma--Vargas Part I (arXiv:1909.12924),
in case `{w3-r1-nd3-t2-(a>k4)}`, the regrown column changes the incoming
moving row by `1/(k(k-1))` or `-1/(k(k+1))`.  The actual full-dimensional
member supplies the sharp incoming denominator `k`, so the two denominator
products acquire factors `k-1` and `k+1`.  These cancel the corresponding
determinant denominators.  Both target expansions preserve the leaf count.

This proves the signed-multiplicity balance for one actual shift pair.  The
full Equation (3) is the sum of three separately constructed such pairs.
-/

namespace DraismaVargas.Count.W3ShiftMultiplicityBalance

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableSourceMatrix FullDimensionalSource
open ThirdEquation W3ShiftSourceCandidates W3ShiftGraphData
open W3ShiftHonestBalance W3ShiftLimitRows
open TrivalentWeight UnitWeightBalance

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star} {shift : ShiftProfile input}

noncomputable def incomingIndex : ℕ := data.sourceEdgeIndex shift.moving.1

noncomputable def factor : Fin 2 → ℕ :=
  ![incomingIndex (shift := shift) - 1, incomingIndex (shift := shift) + 1]

def correctionSign : Fin 2 → ℤ := ![1, -1]

theorem incomingIndex_pos : 0 < incomingIndex (shift := shift) :=
  sourceEdgeIndex_pos data shift.moving.1

theorem factor_pos (position : Fin 2) : 0 < factor (shift := shift) position := by
  have hk := shift.two_le_moving
  fin_cases position
  · change 0 < data.sourceEdgeIndex shift.moving.1 - 1
    omega
  · exact Nat.succ_pos _

theorem correctionSign_unit (position : Fin 2) :
    correctionSign position = 1 ∨ correctionSign position = -1 := by
  fin_cases position <;> simp [correctionSign]

theorem factor_coprime (position : Fin 2) :
    Nat.Coprime (factor (shift := shift) position) (incomingIndex (shift := shift)) := by
  have hk := shift.two_le_moving
  fin_cases position
  · change Nat.Coprime (data.sourceEdgeIndex shift.moving.1 - 1)
      (data.sourceEdgeIndex shift.moving.1)
    have hEq : data.sourceEdgeIndex shift.moving.1 - 1 + 1 =
        data.sourceEdgeIndex shift.moving.1 := by omega
    rw [← hEq]
    simp
  · change Nat.Coprime (data.sourceEdgeIndex shift.moving.1 + 1)
      (data.sourceEdgeIndex shift.moving.1)
    exact Nat.Coprime.symm (by simp)

section Pair

variable (shrink : ShrinkData shift) (hValid : data.Valid)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (shiftMembers shrink 0).datum coordinate)

/-- The shrink column is the old moving column plus `1/(k(k-1))`. -/
theorem newColumn_zero (path : StablePath data) :
    commonMatrix shrink hValid 0 path none =
      StableSourceMatrix.matrix data path shift.movingTarget +
        if path = movingRow shift then
          (1 : ℚ) / ((incomingIndex (shift := shift) : ℚ) *
            ((incomingIndex (shift := shift) - 1 : ℕ) : ℚ)) else 0 := by
  have hkNat : 1 < data.sourceEdgeIndex shift.moving.1 := by
    have := shift.two_le_moving
    omega
  have hk : (1 : ℚ) < data.sourceEdgeIndex shift.moving.1 := by exact_mod_cast hkNat
  have hk0 : (data.sourceEdgeIndex shift.moving.1 : ℚ) ≠ 0 := by linarith
  have hkm : (data.sourceEdgeIndex shift.moving.1 : ℚ) - 1 ≠ 0 := by linarith
  simp only [incomingIndex]
  rw [commonMatrix_wall_zero, matrix_moving_split shift
    (Shrink.wall_rel_remainder shrink)]
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [movingIndex]
  split_ifs <;> (try field_simp) <;> ring

/-- The grow column is the old moving column minus `1/(k(k+1))`. -/
theorem newColumn_one (path : StablePath data) :
    commonMatrix shrink hValid 1 path none =
      StableSourceMatrix.matrix data path shift.movingTarget +
        if path = movingRow shift then
          (-1 : ℚ) / ((incomingIndex (shift := shift) : ℚ) *
            ((incomingIndex (shift := shift) + 1 : ℕ) : ℚ)) else 0 := by
  have hk0 : (incomingIndex (shift := shift) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (incomingIndex_pos (shift := shift)))
  simp only [incomingIndex] at hk0 ⊢
  rw [commonMatrix_wall_one, matrix_moving_split shift
    (Shrink.wall_rel_remainder shrink), Nat.cast_add, Nat.cast_one]
  simp only [movingIndex]
  split_ifs <;> (try field_simp) <;> ring

/-- Each new column is the old moving column plus one unit reciprocal
correction, supported on the moving row. -/
theorem newColumn_eq (position : Fin 2) (path : StablePath data) :
    commonMatrix shrink hValid position path none =
      StableSourceMatrix.matrix data path shift.movingTarget +
        if path = movingRow shift then
          (correctionSign position : ℚ) /
            ((incomingIndex (shift := shift) : ℚ) *
              (factor (shift := shift) position : ℚ)) else 0 := by
  fin_cases position
  · simpa [factor, correctionSign] using newColumn_zero shrink hValid path
  · simpa [factor, correctionSign] using newColumn_one shrink hValid path

/-- The exact denominator-product factor for either member. -/
theorem denominatorProduct_eq_factor (position : Fin 2)
    (hSharp : incomingRowDenominator data (movingRow shift) =
      incomingIndex (shift := shift)) :
    denominatorProduct (labelling shrink hValid initial position).presentation =
      factor (shift := shift) position * incomingDenominatorProduct data := by
  classical
  rw [denominatorProduct_of_commonMatrix (labelling shrink hValid initial position)
    (sourceCoordinates shrink hValid initial) (targetCoordinates shrink initial)
    (commonMatrix shrink hValid position) (squareMatrix_common shrink hValid initial position)
    (commonMatrix_retained shrink hValid position)]
  have hTerm (path : StablePath data) :
      Nat.lcm (commonMatrix shrink hValid position path none).den
          (incomingRowDenominator data path) =
        (if path = movingRow shift then factor (shift := shift) position else 1) *
          incomingRowDenominator data path := by
    rw [newColumn_eq shrink hValid position]
    by_cases hPath : path = movingRow shift
    · subst path
      simp only [eq_self, ite_true]
      exact lcm_den_add_unit_inv
        (fun place ↦ StableSourceMatrix.matrix data (movingRow shift) place)
        shift.movingTarget incomingIndex_pos (factor_pos position)
        (correctionSign_unit position)
        (by change incomingIndex (shift := shift) ∣ incomingRowDenominator data (movingRow shift)
            rw [hSharp])
        (by change Nat.Coprime _ (incomingRowDenominator data _)
            rw [hSharp]
            exact factor_coprime position)
    · simp only [ite_eq_right hPath, add_zero, one_mul]
      exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (movingRow shift)
      (fun _ ↦ factor (shift := shift) position), ite_eq_left (Finset.mem_univ _)]
  rfl

/-- Every member datum in the pair keeps old wall edges on both sides. -/
theorem leafCount_memberData (member : MemberData shift) :
    leafCount (graph target wall member.candidate.right) = leafCount target := by
  refine leafCount_graph_candidate wall member.candidate ?_ ?_
  · refine ⟨shift.movingTarget, ?_⟩
    rw [mem_wallEdgesAssigned]
    refine ⟨?_, member.right_moving⟩
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using shift.movingTarget_mem
  · refine ⟨shift.firstTarget, ?_⟩
    rw [mem_wallEdgesAssigned]
    refine ⟨?_, member.right_first⟩
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using shift.firstTarget_mem

/-- Both actual split targets preserve the incoming target's leaf count. -/
theorem leafCount_member (position : Fin 2) :
    leafCount (graph target wall (shiftMembers shrink position).right) = leafCount target := by
  fin_cases position
  · exact leafCount_memberData (shrinkMember shrink)
  · exact leafCount_memberData (growMember shift)

/-- The natural factors cancel the two closed determinant denominators. -/
theorem sum_factor_det_eq_zero :
    ∑ position : Fin 2, (factor (shift := shift) position : ℚ) *
      (squareMatrix shrink hValid initial position).det = 0 := by
  rw [Fin.sum_univ_two]
  simp only [factor, Matrix.cons_val_zero, Matrix.cons_val_one, incomingIndex]
  rw [det_closed_zero shrink hValid initial, det_closed_one shrink hValid initial]
  have hkNat : 1 < data.sourceEdgeIndex shift.moving.1 := by
    have := shift.two_le_moving
    omega
  have hk : (1 : ℚ) < data.sourceEdgeIndex shift.moving.1 := by exact_mod_cast hkNat
  have hk0 : (data.sourceEdgeIndex shift.moving.1 : ℚ) ≠ 0 := by linarith
  have hkm : (data.sourceEdgeIndex shift.moving.1 : ℚ) - 1 ≠ 0 := by linarith
  have hkp : (data.sourceEdgeIndex shift.moving.1 : ℚ) + 1 ≠ 0 := by linarith
  rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_add, Nat.cast_one]
  change ((data.sourceEdgeIndex shift.moving.1 : ℚ) - 1) *
      (wallContribution shrink hValid initial /
        ((data.sourceEdgeIndex shift.moving.1 : ℚ) *
          ((data.sourceEdgeIndex shift.moving.1 : ℚ) - 1))) +
    ((data.sourceEdgeIndex shift.moving.1 : ℚ) + 1) *
      -(wallContribution shrink hValid initial /
        ((data.sourceEdgeIndex shift.moving.1 : ℚ) *
          ((data.sourceEdgeIndex shift.moving.1 : ℚ) + 1))) = 0
  field_simp
  ring

/-- The arithmetic balance in any honest pair coordinates. Its callers
derive this denominator from an actual full-dimensional member. -/
theorem sum_signedMult_eq_zero_of_sharp
    (hSharp : incomingRowDenominator data (movingRow shift) =
      incomingIndex (shift := shift)) :
    ∑ position : Fin 2,
      signedMult (labelling shrink hValid initial position).presentation = 0 := by
  have hTerm (position : Fin 2) :
      signedMult (labelling shrink hValid initial position).presentation =
        (incomingDenominatorProduct data : ℚ) / 2 ^ leafCount target *
          ((factor (shift := shift) position : ℚ) *
            (squareMatrix shrink hValid initial position).det) := by
    change (denominatorProduct (labelling shrink hValid initial position).presentation : ℚ) /
        2 ^ leafCount (graph target wall (shiftMembers shrink position).right) *
          (squareMatrix shrink hValid initial position).det = _
    rw [leafCount_member shrink position,
      denominatorProduct_eq_factor shrink hValid initial position hSharp]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun position _ ↦ hTerm position, ← Finset.mul_sum,
    sum_factor_det_eq_zero shrink hValid initial, mul_zero]

/-- One actual Figure 29 pair has zero total signed multiplicity. -/
theorem sum_signedMult_eq_zero
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (shiftMembers shrink incoming).datum coordinate) :
    ∑ position : Fin 2,
      signedMult (W3ShiftStableIncidence.outgoingLabelling shrink hValid incoming
        incomingFD position).presentation = 0 := by
  apply sum_signedMult_eq_zero_of_sharp shrink hValid
    (W3ShiftStableIncidence.initialLabelling shrink hValid incoming incomingFD)
  fin_cases incoming
  · exact W3ShiftIncomingDenominator.incomingRowDenominator_of_shrink shrink incomingFD
  · exact W3ShiftIncomingDenominator.incomingRowDenominator_of_grow incomingFD

end Pair

end DraismaVargas.Count.W3ShiftMultiplicityBalance
