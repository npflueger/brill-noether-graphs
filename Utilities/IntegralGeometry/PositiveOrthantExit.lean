module

public import Utilities.IntegralGeometry.RationalGenericStart

@[expose] public section

/-!
# The first exit from a positive rational orthant

Inside one full-dimensional cone of the Draisma--Vargas deformation argument
(Draisma--Vargas Part I, arXiv:1909.12924), the target-length segment pulls
back to an affine segment of cone coordinates.  If its endpoint is outside the
closed positive orthant, some coordinate is negative.  This file chooses the
least crossing time among exactly those negative endpoint coordinates and
proves:

* the time lies strictly between zero and one;
* the selected coordinate is zero there;
* every other coordinate is still strictly positive;
* every coordinate was positive at every earlier nonnegative time.

Only pairwise distinct crossing times among the negative endpoint coordinates
are required.  Coordinates which vanish at the final endpoint may therefore
do so simultaneously; this matters when the endpoint lies on a closed face.
-/

namespace DraismaVargas.Infrastructure

open RationalAffineWall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RationalAffineWall

/-- The affine wall defined by vanishing of one coordinate. -/
def coordinateWall (i : ι) : RationalAffineWall ι where
  coefficient j := if j = i then 1 else 0
  constant := 0

@[simp]
theorem eval_coordinateWall (i : ι) (x : ι → ℚ) :
    (coordinateWall i).eval x = x i := by
  classical
  simp [coordinateWall, eval]

/-- Exact time at which coordinate `i` vanishes along an affine segment. -/
def coordinateCrossingTime (start finish : ι → ℚ) (i : ι) : ℚ :=
  (coordinateWall i).crossingTime start finish

@[simp]
theorem coordinateCrossingTime_eq (start finish : ι → ℚ) (i : ι) :
    coordinateCrossingTime start finish i =
      start i / (start i - finish i) := by
  simp [coordinateCrossingTime, crossingTime]

/-- The exact genericity condition needed for an interior orthant exit:
negative endpoint coordinates have pairwise distinct crossing times. -/
def SimpleNegativeCrossings (start finish : ι → ℚ) : Prop :=
  ∀ first, finish first < 0 → ∀ second, finish second < 0 →
    coordinateCrossingTime start finish first =
      coordinateCrossingTime start finish second →
    first = second

/-- Negative endpoint coordinates, the only coordinates which can cause an
interior exit from the positive orthant. -/
abbrev NegativeIndex (finish : ι → ℚ) := {i : ι // finish i < 0}

/-- Ordered distinct pairs of negative endpoint coordinates. -/
abbrev DistinctNegativePair (finish : ι → ℚ) :=
  {pair : NegativeIndex finish × NegativeIndex finish // pair.1 ≠ pair.2}

/-- The pairwise collision wall attached to two negative coordinates. -/
def negativeCollisionWall (finish : ι → ℚ)
    (pair : DistinctNegativePair finish) : RationalAffineWall ι :=
  collisionWall (coordinateWall pair.val.1.val)
    (coordinateWall pair.val.2.val) finish

/-- Collision equations for distinct negative endpoint coordinates are always
proper: the coefficient at the first coordinate is the negative value of the
second endpoint coordinate. -/
theorem negativeCollisionWall_proper (finish : ι → ℚ)
    (pair : DistinctNegativePair finish) :
    (negativeCollisionWall finish pair).Proper := by
  have hindex : pair.val.1.val ≠ pair.val.2.val := by
    intro heq
    exact pair.property (Subtype.ext heq)
  unfold negativeCollisionWall
  apply collisionWall_proper_of_coefficient_ne_zero
    (i := pair.val.1.val)
  simp only [eval_coordinateWall]
  simpa [coordinateWall, hindex] using ne_of_lt pair.val.2.property

/-- Every positive rational point can be perturbed within the positive
orthant so that all interior exit times toward a fixed endpoint are distinct. -/
theorem exists_positive_simpleNegativeCrossings (base finish : ι → ℚ)
    (hbase : ∀ i, 0 < base i) :
    ∃ start : ι → ℚ,
      (∀ i, 0 < start i) ∧ SimpleNegativeCrossings start finish := by
  obtain ⟨start, hpositive, havoid⟩ :=
    exists_avoids_preserving_positive (negativeCollisionWall finish)
      coordinateWall base (negativeCollisionWall_proper finish)
      (by simpa using hbase)
  refine ⟨start, by simpa using hpositive, ?_⟩
  intro first hfirst second hsecond heq
  by_contra hne
  let firstIndex : NegativeIndex finish := ⟨first, hfirst⟩
  let secondIndex : NegativeIndex finish := ⟨second, hsecond⟩
  have hsubtype : firstIndex ≠ secondIndex := by
    intro h
    exact hne (congrArg Subtype.val h)
  let pair : DistinctNegativePair finish :=
    ⟨(firstIndex, secondIndex), hsubtype⟩
  have hcollision := havoid pair
  dsimp [negativeCollisionWall, pair, firstIndex, secondIndex] at hcollision
  apply hcollision
  apply eval_collisionWall_eq_zero_of_crossingTime_eq
  · simp only [eval_coordinateWall]
    have hs : 0 < start first := by simpa using hpositive first
    linarith
  · simp only [eval_coordinateWall]
    have hs : 0 < start second := by simpa using hpositive second
    linarith
  · exact heq

/-- If the endpoint is outside the closed positive orthant, a simple rational
segment has a unique first wall event with all other coordinates positive. -/
theorem exists_first_positiveOrthant_exit (start finish : ι → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish) :
    ∃ wall : ι, ∃ time : ℚ,
      0 < time ∧ time < 1 ∧
      segment start finish time wall = 0 ∧
      (∀ i, i ≠ wall → 0 < segment start finish time i) ∧
      ∀ t : ℚ, 0 ≤ t → t < time →
        ∀ i, 0 < segment start finish t i := by
  classical
  let exiting : Finset ι := Finset.univ.filter fun i => finish i < 0
  have hexiting : exiting.Nonempty := by
    obtain ⟨i, hi⟩ := houtside
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨wall, hwall, hleast⟩ :=
    exiting.exists_min_image (coordinateCrossingTime start finish) hexiting
  have hwallNeg : finish wall < 0 := (Finset.mem_filter.mp hwall).2
  let time := coordinateCrossingTime start finish wall
  have htimePos : 0 < time := by
    exact crossingTime_pos (coordinateWall wall) start finish
      (by simpa using hstart wall) (by simpa using hwallNeg)
  have htimeLt : time < 1 := by
    exact crossingTime_lt_one (coordinateWall wall) start finish
      (by simpa using hstart wall) (by simpa using hwallNeg)
  have hwallZero : segment start finish time wall = 0 := by
    have hdiff : (coordinateWall wall).eval start ≠
        (coordinateWall wall).eval finish := by
      simp only [eval_coordinateWall]
      linarith [hstart wall, hwallNeg]
    change segment start finish
      ((coordinateWall wall).crossingTime start finish) wall = 0
    simpa only [eval_coordinateWall] using
      eval_segment_crossingTime_eq_zero (coordinateWall wall) start finish hdiff
  refine ⟨wall, time, htimePos, htimeLt, hwallZero, ?_, ?_⟩
  · intro i hiWall
    by_cases hiNeg : finish i < 0
    · have hiMem : i ∈ exiting :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiNeg⟩
      have hle := hleast i hiMem
      have hne : coordinateCrossingTime start finish wall ≠
          coordinateCrossingTime start finish i := by
        intro heq
        exact hiWall (hsimple wall hwallNeg i hiNeg heq).symm
      have hlt : time < coordinateCrossingTime start finish i := by
        exact lt_of_le_of_ne hle hne
      simpa [coordinateCrossingTime] using
        eval_segment_pos_before_crossing (coordinateWall i) start finish
          (by simpa using hstart i) (by simpa using hiNeg) hlt
    · have hiNonneg : 0 ≤ finish i := le_of_not_gt hiNeg
      have hstartPart : 0 < (1 - time) * start i :=
        mul_pos (sub_pos.mpr htimeLt) (hstart i)
      have hfinishPart : 0 ≤ time * finish i :=
        mul_nonneg htimePos.le hiNonneg
      unfold segment
      nlinarith
  · intro t htNonneg htTime i
    have htOne : t < 1 := htTime.trans htimeLt
    by_cases hiNeg : finish i < 0
    · have hiMem : i ∈ exiting :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiNeg⟩
      have hle := hleast i hiMem
      have htCrossing : t < coordinateCrossingTime start finish i :=
        htTime.trans_le hle
      simpa [coordinateCrossingTime] using
        eval_segment_pos_before_crossing (coordinateWall i) start finish
          (by simpa using hstart i) (by simpa using hiNeg) htCrossing
    · have hiNonneg : 0 ≤ finish i := le_of_not_gt hiNeg
      have hstartPart : 0 < (1 - t) * start i :=
        mul_pos (sub_pos.mpr htOne) (hstart i)
      have hfinishPart : 0 ≤ t * finish i :=
        mul_nonneg htNonneg hiNonneg
      unfold segment
      nlinarith

/-- A simple segment from a positive point either ends in the closed orthant,
or has the first interior wall event described above. -/
theorem closedOrthant_or_exists_first_exit (start finish : ι → ℚ)
    (hstart : ∀ i, 0 < start i)
    (hsimple : SimpleNegativeCrossings start finish) :
    (∀ i, 0 ≤ finish i) ∨
      ∃ wall : ι, ∃ time : ℚ,
        0 < time ∧ time < 1 ∧
        segment start finish time wall = 0 ∧
        (∀ i, i ≠ wall → 0 < segment start finish time i) ∧
        ∀ t : ℚ, 0 ≤ t → t < time →
          ∀ i, 0 < segment start finish t i := by
  by_cases hclosed : ∀ i, 0 ≤ finish i
  · exact Or.inl hclosed
  · have houtside : ∃ i, finish i < 0 := by
      simpa only [not_forall, not_le] using hclosed
    exact Or.inr (exists_first_positiveOrthant_exit start finish hstart houtside hsimple)

/-- From any point in the positive orthant and any endpoint outside its
closure, there is a rational positive perturbation whose segment has the
first simple wall event described above. -/
theorem exists_simple_start_and_first_positiveOrthant_exit
    (base finish : ι → ℚ) (hbase : ∀ i, 0 < base i)
    (houtside : ∃ i, finish i < 0) :
    ∃ start : ι → ℚ, (∀ i, 0 < start i) ∧
      ∃ wall : ι, ∃ time : ℚ,
        0 < time ∧ time < 1 ∧
        segment start finish time wall = 0 ∧
        (∀ i, i ≠ wall → 0 < segment start finish time i) ∧
        ∀ t : ℚ, 0 ≤ t → t < time →
          ∀ i, 0 < segment start finish t i := by
  obtain ⟨start, hstart, hsimple⟩ :=
    exists_positive_simpleNegativeCrossings base finish hbase
  exact ⟨start, hstart,
    exists_first_positiveOrthant_exit start finish hstart houtside hsimple⟩

end RationalAffineWall

end DraismaVargas.Infrastructure
