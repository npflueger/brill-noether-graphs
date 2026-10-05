module

public import Mathlib.Tactic

@[expose] public section

/-!
# Exact ordering of rational wall crossings

This file supplies the finite-ordering part of the rational deformation
argument of Draisma--Vargas Part I (arXiv:1909.12924), which moves a tropical
morphism along a segment in a space of edge lengths and crosses walls one at a
time.  Along a rational affine segment, the crossing time of an affine wall is
an explicit rational number.  For a finite indexed wall family, every wall
event therefore belongs to a finite set, and whenever a future event exists
there is a least next one.

The `SimpleAlong` hypothesis below is the precise genericity input these
results need: distinct indexed walls have distinct crossing times.
Constructing a starting point with this property, transporting gluing data
between consecutive events, and treating the closed endpoint are separate
obligations; none is hidden in the results here.
-/

namespace DraismaVargas.Infrastructure

variable {ι κ : Type*}

/-- An affine equation with rational coefficients. -/
structure RationalAffineWall (ι : Type*) where
  coefficient : ι → ℚ
  constant : ℚ

namespace RationalAffineWall

variable [Fintype ι]

/-- Evaluation of a rational affine wall equation. -/
def eval (wall : RationalAffineWall ι) (x : ι → ℚ) : ℚ :=
  ∑ i, wall.coefficient i * x i + wall.constant

/-- The affine segment from `x` to `y`, at rational parameter `t`. -/
def segment (x y : ι → ℚ) (t : ℚ) : ι → ℚ :=
  fun i => x i + t * (y i - x i)

/-- Evaluation along an affine segment is affine in the segment parameter. -/
theorem eval_segment (wall : RationalAffineWall ι) (x y : ι → ℚ) (t : ℚ) :
    wall.eval (segment x y t) =
      wall.eval x + t * (wall.eval y - wall.eval x) := by
  classical
  unfold eval segment
  have hsum :
      (∑ i, wall.coefficient i * (x i + t * (y i - x i))) =
        (∑ i, wall.coefficient i * x i) +
          t * ((∑ i, wall.coefficient i * y i) -
            ∑ i, wall.coefficient i * x i) := by
    calc
      _ = ∑ i, (wall.coefficient i * x i +
          t * (wall.coefficient i * y i - wall.coefficient i * x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  ring

/-- The exact parameter at which a wall crosses a segment whose endpoint
evaluations differ. -/
def crossingTime (wall : RationalAffineWall ι) (x y : ι → ℚ) : ℚ :=
  wall.eval x / (wall.eval x - wall.eval y)

/-- The explicit crossing time lies on the wall. -/
theorem eval_segment_crossingTime_eq_zero (wall : RationalAffineWall ι)
    (x y : ι → ℚ) (hdiff : wall.eval x ≠ wall.eval y) :
    wall.eval (segment x y (wall.crossingTime x y)) = 0 := by
  rw [eval_segment]
  unfold crossingTime
  field_simp [sub_ne_zero.mpr hdiff]
  ring

/-- A wall can vanish at only its explicit crossing time. -/
theorem eq_crossingTime_of_eval_segment_eq_zero (wall : RationalAffineWall ι)
    (x y : ι → ℚ) {t : ℚ} (hdiff : wall.eval x ≠ wall.eval y)
    (ht : wall.eval (segment x y t) = 0) :
    t = wall.crossingTime x y := by
  rw [eval_segment] at ht
  unfold crossingTime
  apply (eq_div_iff (sub_ne_zero.mpr hdiff)).2
  linarith

/-- If a segment starts on the positive side and ends on the negative side,
its crossing time is positive. -/
theorem crossingTime_pos (wall : RationalAffineWall ι) (x y : ι → ℚ)
    (hx : 0 < wall.eval x) (hy : wall.eval y < 0) :
    0 < wall.crossingTime x y := by
  unfold crossingTime
  exact div_pos hx (by linarith)

/-- Under the same sign assumptions, the crossing occurs before the endpoint. -/
theorem crossingTime_lt_one (wall : RationalAffineWall ι) (x y : ι → ℚ)
    (hx : 0 < wall.eval x) (hy : wall.eval y < 0) :
    wall.crossingTime x y < 1 := by
  unfold crossingTime
  apply (div_lt_one (by linarith : 0 < wall.eval x - wall.eval y)).2
  linarith

/-- Evaluation is positive strictly before a positive-to-negative crossing. -/
theorem eval_segment_pos_before_crossing (wall : RationalAffineWall ι)
    (x y : ι → ℚ) (hx : 0 < wall.eval x) (hy : wall.eval y < 0)
    {t : ℚ} (ht : t < wall.crossingTime x y) :
    0 < wall.eval (segment x y t) := by
  rw [eval_segment]
  have hden : 0 < wall.eval x - wall.eval y := by linarith
  have hrewrite :
      wall.eval x + t * (wall.eval y - wall.eval x) =
        (wall.eval x - wall.eval y) * (wall.crossingTime x y - t) := by
    unfold crossingTime
    field_simp [ne_of_gt hden]
    ring
  rw [hrewrite]
  exact mul_pos hden (sub_pos.mpr ht)

/-- Evaluation is negative strictly after a positive-to-negative crossing. -/
theorem eval_segment_neg_after_crossing (wall : RationalAffineWall ι)
    (x y : ι → ℚ) (hx : 0 < wall.eval x) (hy : wall.eval y < 0)
    {t : ℚ} (ht : wall.crossingTime x y < t) :
    wall.eval (segment x y t) < 0 := by
  rw [eval_segment]
  have hden : 0 < wall.eval x - wall.eval y := by linarith
  have hrewrite :
      wall.eval x + t * (wall.eval y - wall.eval x) =
        (wall.eval x - wall.eval y) * (wall.crossingTime x y - t) := by
    unfold crossingTime
    field_simp [ne_of_gt hden]
    ring
  rw [hrewrite]
  exact mul_neg_of_pos_of_neg hden (sub_neg.mpr ht)

section FiniteFamily

variable [Fintype κ]

/-- The finite set of exact crossing times of an indexed wall family. -/
def crossingTimes (walls : κ → RationalAffineWall ι) (x y : ι → ℚ) : Finset ℚ :=
  Finset.univ.image fun k => (walls k).crossingTime x y

/-- Every actual vanishing event occurs at one of the enumerated rational
crossing times. -/
theorem mem_crossingTimes_of_eval_segment_eq_zero
    (walls : κ → RationalAffineWall ι) (x y : ι → ℚ)
    (hdiff : ∀ k, (walls k).eval x ≠ (walls k).eval y)
    {k : κ} {t : ℚ} (ht : (walls k).eval (segment x y t) = 0) :
    t ∈ crossingTimes walls x y := by
  apply Finset.mem_image.mpr
  refine ⟨k, Finset.mem_univ k, ?_⟩
  exact (eq_crossingTime_of_eval_segment_eq_zero (walls k) x y (hdiff k) ht).symm

/-- There are no more distinct wall-event times than indexed walls. -/
theorem card_crossingTimes_le (walls : κ → RationalAffineWall ι) (x y : ι → ℚ) :
    (crossingTimes walls x y).card ≤ Fintype.card κ := by
  simpa [crossingTimes] using
    (Finset.card_image_le (s := (Finset.univ : Finset κ))
      (f := fun k => (walls k).crossingTime x y))

/-- Distinct indexed walls cross at distinct times along this segment.  This
is the exact no-codimension-two condition needed by the finite march. -/
def SimpleAlong (walls : κ → RationalAffineWall ι) (x y : ι → ℚ) : Prop :=
  Function.Injective fun k => (walls k).crossingTime x y

omit [Fintype κ] in
/-- At a simple segment event, the vanishing wall index is unique. -/
theorem wall_eq_of_both_eval_segment_eq_zero
    (walls : κ → RationalAffineWall ι) (x y : ι → ℚ)
    (hdiff : ∀ k, (walls k).eval x ≠ (walls k).eval y)
    (hsimple : SimpleAlong walls x y) {k j : κ} {t : ℚ}
    (hk : (walls k).eval (segment x y t) = 0)
    (hj : (walls j).eval (segment x y t) = 0) :
    k = j := by
  apply hsimple
  change (walls k).crossingTime x y = (walls j).crossingTime x y
  rw [← eq_crossingTime_of_eval_segment_eq_zero (walls k) x y (hdiff k) hk,
    ← eq_crossingTime_of_eval_segment_eq_zero (walls j) x y (hdiff j) hj]

/-- A finite rational wall family always has a least event after the current
parameter, provided that some future event remains. -/
theorem exists_least_crossing_after (walls : κ → RationalAffineWall ι)
    (x y : ι → ℚ) (current : ℚ)
    (hfuture : ∃ k, current < (walls k).crossingTime x y) :
    ∃ k, current < (walls k).crossingTime x y ∧
      ∀ j, current < (walls j).crossingTime x y →
        (walls k).crossingTime x y ≤ (walls j).crossingTime x y := by
  let future : Finset κ :=
    Finset.univ.filter fun k => current < (walls k).crossingTime x y
  have hnonempty : future.Nonempty := by
    obtain ⟨k, hk⟩ := hfuture
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  obtain ⟨k, hk, hmin⟩ :=
    future.exists_min_image (fun j => (walls j).crossingTime x y) hnonempty
  refine ⟨k, (Finset.mem_filter.mp hk).2, ?_⟩
  intro j hj
  exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

end FiniteFamily

end RationalAffineWall

end DraismaVargas.Infrastructure
