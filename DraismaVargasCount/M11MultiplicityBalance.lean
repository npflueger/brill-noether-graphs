module

public import DraismaVargasCount.UnitWeightBalance
public import DraismaVargas.LocalCases.M11CommonBalance

@[expose] public section

/-!
# Multiplicity factors for Equation (6), M11

This file computes the multiplicity factors in Draisma–Vargas Part I, Equation (6)
(Case `{w2-r2-nd3-M-11}`, Figure 32).  The determinant weights are `(1, 1, 4)`.
Each split member adds one target leaf and has integral regrown column, so its
multiplicity factor is
`D₀ / 2^(l(T₀)+1)`.  The joined member adds no leaf and changes just the third
row by a half.  If that incoming row denominator is odd, its denominator
product doubles, giving exactly four times the split factor.

All three leaf counts and the two split denominator products below are proved on
the candidates themselves.  The balance `sum_signedMult_eq_zero_of_conditional_odd`
keeps one explicitly named hypothesis: the incoming third-row denominator is coprime
to two whenever the joined member has nonzero determinant.  That hypothesis is not
derived from the wall input here; `DraismaVargasCount.M11IncomingDenominator` proves
that this denominator is one, and so completes the balance of Equation (6).
-/

namespace DraismaVargas.Count.M11MultiplicityBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11CommonBalance M11SourceCandidates
open TrivalentWeight UnitWeightBalance

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The original split creates one leaf. -/
theorem leafCount_zero :
    leafCount (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget =
      leafCount target + 1 :=
  leafCount_graph_of_leaf_split wall _
    (firstSplit_target_valencies input profile hCard).1
    (firstSplit_target_valencies input profile hCard).2

/-- The remote split has the same target valencies and creates one leaf. -/
theorem leafCount_one :
    leafCount (M11RemoteCandidates.candidates input profile hCard 1).outgoingTarget =
      leafCount target + 1 :=
  leafCount_graph_of_leaf_split wall _
    (M11RemoteCandidates.secondSplit_target_valencies input profile hCard).1
    (M11RemoteCandidates.secondSplit_target_valencies input profile hCard).2

/-- Both copies of the joined wall are divalent, so no leaf changes. -/
theorem leafCount_two :
    leafCount (M11RemoteCandidates.candidates input profile hCard 2).outgoingTarget =
      leafCount target :=
  leafCount_graph_of_divalent_split wall _
    (joined_target_valencies data star block hCard).1
    (joined_target_valencies data star block hCard).2

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)

/-- Read the family's denominator products in its constructed common coordinates. -/
theorem denominatorProduct_eq_prod (position : Fin 3) :
    denominatorProduct (labelling input profile hCard initial position).presentation =
      ∏ path : StablePath data,
        Nat.lcm (commonMatrix input profile hCard position path none).den
          (incomingRowDenominator data path) :=
  denominatorProduct_of_commonMatrix (labelling input profile hCard initial position)
    (sourceCoordinates input profile hCard initial) (targetCoordinates input profile hCard initial)
    (commonMatrix input profile hCard position)
    (squareMatrix_common input profile hCard initial position)
    (commonMatrix_retained input profile hCard position)

/-- The first split's new column is integral, hence changes no denominator. -/
theorem denominatorProduct_zero :
    denominatorProduct (labelling input profile hCard initial 0).presentation =
      incomingDenominatorProduct data := by
  classical
  rw [denominatorProduct_eq_prod]
  apply Finset.prod_congr rfl
  intro path _
  have hNew : commonMatrix input profile hCard 0 path none =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0 :=
    M11SplitLimitMatrix.matrix_new input profile hCard path
  rw [hNew]
  split_ifs <;> norm_num

/-- The branch-swapped split also changes no denominator. -/
theorem denominatorProduct_one
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    denominatorProduct (labelling input profile hCard initial 1).presentation =
      incomingDenominatorProduct data := by
  classical
  rw [denominatorProduct_eq_prod]
  apply Finset.prod_congr rfl
  intro path _
  have hNew : commonMatrix input profile hCard 1 path none =
      if path = (M11BranchSeparation.oppositeDouble profile hCard).stablePath then 2 else 0 :=
    M11RemoteLimitMatrix.matrix_new input profile hCard hConnected hGenus path
  rw [hNew]
  split_ifs <;> norm_num

/-- The joined denominator product doubles if the affected incoming row has
odd denominator.  No other row denominator is evaluated. -/
theorem denominatorProduct_two
    (hOdd : Nat.Coprime 2 (incomingRowDenominator data
      (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩))) :
    denominatorProduct (labelling input profile hCard initial 2).presentation =
      2 * incomingDenominatorProduct data := by
  classical
  let third : StablePath data :=
    NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩
  rw [denominatorProduct_eq_prod]
  have hTerm (path : StablePath data) :
      Nat.lcm (commonMatrix input profile hCard 2 path none).den
          (incomingRowDenominator data path) =
        (if path = third then 2 else 1) * incomingRowDenominator data path := by
    have hNew : commonMatrix input profile hCard 2 path none =
        StableSourceMatrix.matrix data path (star.edge profile.singleLabel) -
          (if path = third then (1 / 2 : ℚ) else 0) :=
      M11JoinedBackgroundMatrix.matrix_new_eq_old_sub_half input profile hCard path
    rw [hNew]
    by_cases hPath : path = third
    · subst path
      simp only [eq_self, ite_true]
      simpa only [incomingRowDenominator, Nat.cast_one, Nat.cast_ofNat, Int.cast_neg,
        Int.cast_one, one_mul, neg_div, one_div, sub_eq_add_neg] using lcm_den_add_unit_inv
        (fun place ↦ StableSourceMatrix.matrix data third place)
        (star.edge profile.singleLabel) (a := 1) (b := 2) (c := -1)
        (by decide) (by decide) (Or.inr rfl) (one_dvd _) hOdd
    · simp only [ite_eq_right hPath, sub_zero, one_mul]
      exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ third (fun _ ↦ 2), ite_eq_left (Finset.mem_univ _)]
  rfl

/-- Equation (6)'s multiplicity balance, with the odd-denominator hypothesis
required only when the joined member contributes. -/
theorem sum_signedMult_eq_zero_of_conditional_odd
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hOdd : (squareMatrix input profile hCard initial 2).det ≠ 0 →
      Nat.Coprime 2 (incomingRowDenominator data
        (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩))) :
    ∑ position : Fin 3,
      signedMult (labelling input profile hCard initial position).presentation = 0 := by
  rw [Fin.sum_univ_three]
  have hBalance := determinant_balance input profile hCard initial hConnected hGenus
  change (denominatorProduct (labelling input profile hCard initial 0).presentation : ℚ) /
      2 ^ leafCount (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget *
        (squareMatrix input profile hCard initial 0).det +
    (denominatorProduct (labelling input profile hCard initial 1).presentation : ℚ) /
      2 ^ leafCount (M11RemoteCandidates.candidates input profile hCard 1).outgoingTarget *
        (squareMatrix input profile hCard initial 1).det +
    (denominatorProduct (labelling input profile hCard initial 2).presentation : ℚ) /
      2 ^ leafCount (M11RemoteCandidates.candidates input profile hCard 2).outgoingTarget *
        (squareMatrix input profile hCard initial 2).det = 0
  rw [denominatorProduct_zero, denominatorProduct_one input profile hCard initial hConnected hGenus,
    leafCount_zero, leafCount_one, leafCount_two]
  by_cases hDet : (squareMatrix input profile hCard initial 2).det = 0
  · rw [hDet, mul_zero, add_zero]
    rw [hDet, mul_zero, add_zero] at hBalance
    rw [← mul_add, hBalance, mul_zero]
  · rw [denominatorProduct_two input profile hCard initial (hOdd hDet)]
    push_cast
    rw [pow_succ]
    field_simp
    nlinarith [hBalance]

end Square

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The conditional Equation (6) balance in the canonical coordinates. -/
theorem sum_signedMult_canonical_eq_zero_of_conditional_odd
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hOdd : (canonicalMatrix input profile hCard 2).det ≠ 0 →
      Nat.Coprime 2 (incomingRowDenominator data
        (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩))) :
    ∑ position : Fin 3, signedMult
      (labelling input profile hCard (canonicalInitialLabelling input profile hCard)
        position).presentation = 0 :=
  sum_signedMult_eq_zero_of_conditional_odd input profile hCard
    (canonicalInitialLabelling input profile hCard) hConnected hGenus hOdd

end DraismaVargas.Count.M11MultiplicityBalance
