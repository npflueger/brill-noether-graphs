import Utilities.IntegralGeometry.Denominator
import DraismaVargas.Infrastructure.LengthMatrix

/-!
# Clearing a positive rational gluing realization

A positive rational target metric on a finite gluing datum determines every
source-edge length by division by its sheet-block dilation index.  This file
clears all target and source denominators simultaneously and constructs the
literal positive-natural-number `IntegralRealization` consumed by the Part-I
endpoint.

The scale is deliberately metric-specific: it is the product of the two
finite common denominators.  No determinant bound or minimality claim is used.
-/

namespace DraismaVargas.Infrastructure

/-- The natural number represented by a positive integral rational. -/
noncomputable def positiveIntegralNat (q : ℚ) (hq : Integral q) : ℕ :=
  (Classical.choose hq).toNat

theorem positiveIntegralNat_cast (q : ℚ) (hq : Integral q) (hpos : 0 < q) :
    (positiveIntegralNat q hq : ℚ) = q := by
  let z : ℤ := Classical.choose hq
  have hz : q = (z : ℚ) := Classical.choose_spec hq
  have hzPosQ : (0 : ℚ) < (z : ℚ) := by simpa [← hz] using hpos
  have hzNonneg : 0 ≤ z := by exact_mod_cast hzPosQ.le
  change ((z.toNat : ℕ) : ℚ) = q
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hzNonneg, ← hz]

theorem positiveIntegralNat_pos (q : ℚ) (hq : Integral q) (hpos : 0 < q) :
    0 < positiveIntegralNat q hq := by
  by_contra h
  have hzero : positiveIntegralNat q hq = 0 := Nat.eq_zero_of_not_pos h
  have hcast := positiveIntegralNat_cast q hq hpos
  rw [hzero, Nat.cast_zero] at hcast
  linarith

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- A common scale for all rational target lengths and all induced rational
source-edge lengths. -/
noncomputable def rationalRealizationScale (data : GluingDatum target degree)
    (targetLength : target.edges → ℚ) : ℕ :=
  commonDenominator Finset.univ targetLength *
    commonDenominator Finset.univ (data.sourceEdgeLength targetLength)

theorem rationalRealizationScale_pos (data : GluingDatum target degree)
    (targetLength : target.edges → ℚ) :
    0 < data.rationalRealizationScale targetLength :=
  Nat.mul_pos (commonDenominator_pos _ _) (commonDenominator_pos _ _)

theorem integral_rationalRealizationScale_target
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (edge : target.edges) :
    Integral ((data.rationalRealizationScale targetLength : ℚ) *
      targetLength edge) := by
  apply integral_mul_of_den_dvd
  unfold rationalRealizationScale
  exact dvd_mul_of_dvd_left
    (den_dvd_commonDenominator Finset.univ targetLength
      (Finset.mem_univ edge)) _

theorem integral_rationalRealizationScale_source
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (edge : data.SourceEdge) :
    Integral ((data.rationalRealizationScale targetLength : ℚ) *
      data.sourceEdgeLength targetLength edge) := by
  apply integral_mul_of_den_dvd
  unfold rationalRealizationScale
  exact dvd_mul_of_dvd_right
    (den_dvd_commonDenominator Finset.univ
      (data.sourceEdgeLength targetLength) (Finset.mem_univ edge)) _

/-- Clear a strictly positive rational target metric and all induced source
lengths to a genuine positive integral gluing realization. -/
noncomputable def IntegralRealization.ofPositiveRational
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hPositive : ∀ edge, 0 < targetLength edge) : data.IntegralRealization where
  targetLength := fun edge ↦
    positiveIntegralNat
      ((data.rationalRealizationScale targetLength : ℚ) * targetLength edge)
      (data.integral_rationalRealizationScale_target targetLength edge)
  targetLength_pos := by
    intro edge
    apply positiveIntegralNat_pos
    exact mul_pos (by exact_mod_cast
      data.rationalRealizationScale_pos targetLength) (hPositive edge)
  sourceLength := fun edge ↦
    positiveIntegralNat
      ((data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge)
      (data.integral_rationalRealizationScale_source targetLength edge)
  sourceLength_pos := by
    intro edge
    apply positiveIntegralNat_pos
    apply mul_pos
    · exact_mod_cast data.rationalRealizationScale_pos targetLength
    · exact div_pos (hPositive edge.1.1) (by
        exact_mod_cast data.sourceEdgeIndex_pos edge)
  dilation_length := by
    intro edge
    have hScaleQ : (0 : ℚ) < data.rationalRealizationScale targetLength := by
      exact_mod_cast data.rationalRealizationScale_pos targetLength
    have hSourcePositive :
        0 < (data.rationalRealizationScale targetLength : ℚ) *
          data.sourceEdgeLength targetLength edge := by
      exact mul_pos hScaleQ (div_pos (hPositive edge.1.1) (by
        exact_mod_cast data.sourceEdgeIndex_pos edge))
    have hTargetPositive :
        0 < (data.rationalRealizationScale targetLength : ℚ) *
          targetLength edge.1.1 :=
      mul_pos hScaleQ (hPositive edge.1.1)
    have hSourceCast := positiveIntegralNat_cast
      ((data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge)
      (data.integral_rationalRealizationScale_source targetLength edge)
      hSourcePositive
    have hTargetCast := positiveIntegralNat_cast
      ((data.rationalRealizationScale targetLength : ℚ) *
        targetLength edge.1.1)
      (data.integral_rationalRealizationScale_target targetLength edge.1.1)
      hTargetPositive
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_mul, hSourceCast, hTargetCast]
    unfold sourceEdgeLength
    have hIndex : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (data.sourceEdgeIndex_pos edge)
    field_simp [hIndex]

namespace IntegralRealization

@[simp]
theorem ofPositiveRational_targetLength_cast
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hPositive : ∀ edge, 0 < targetLength edge) (edge : target.edges) :
    ((IntegralRealization.ofPositiveRational data targetLength hPositive).targetLength
        edge : ℚ) =
      (data.rationalRealizationScale targetLength : ℚ) * targetLength edge :=
  positiveIntegralNat_cast _ _
    (mul_pos (by exact_mod_cast data.rationalRealizationScale_pos targetLength)
      (hPositive edge))

@[simp]
theorem ofPositiveRational_sourceLength_cast
    (data : GluingDatum target degree) (targetLength : target.edges → ℚ)
    (hPositive : ∀ edge, 0 < targetLength edge) (edge : data.SourceEdge) :
    ((IntegralRealization.ofPositiveRational data targetLength hPositive).sourceLength
        edge : ℚ) =
      (data.rationalRealizationScale targetLength : ℚ) *
        data.sourceEdgeLength targetLength edge :=
  positiveIntegralNat_cast _ _
    (mul_pos (by exact_mod_cast data.rationalRealizationScale_pos targetLength)
      (div_pos (hPositive edge.1.1) (by
        exact_mod_cast data.sourceEdgeIndex_pos edge)))

end IntegralRealization

end GluingDatum

end DraismaVargas.Infrastructure
