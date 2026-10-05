module

public import Utilities.IntegralGeometry.ConeWall
public import Utilities.IntegralGeometry.RationalWallOrder

@[expose] public section

/-!
# Rational generic points in finite open wall regions

The deformation argument of Draisma--Vargas Part I (arXiv:1909.12924) marches
along a segment of edge lengths; the march must start at a rational point which
remains inside the current open cone but avoids finitely many degeneracy
hyperplanes.  This file proves that algebraic fact exactly over `ℚ`.

For a wall family and fixed endpoint, the exceptional equations are:

* equality of a wall's two endpoint evaluations, which would make its explicit
  crossing-time denominator zero;
* equality of the crossing times of two distinct walls, which is itself an
  affine equation in the starting point.

If each such affine equation is proper, finite rational avoidance produces a
start in any nonempty rational region cut out by finitely many strict affine
inequalities.  The resulting segment satisfies `SimpleAlong`.  Proving
properness for the concrete walls of the Draisma--Vargas cone decomposition and
transporting the combinatorial state are separate obligations.
-/

namespace DraismaVargas.Infrastructure

open RationalAffineWall

variable {ι κ η : Type*}

namespace RationalAffineWall

variable [Fintype ι]

/-- An affine wall is proper when it does not vanish at every rational point. -/
def Proper (wall : RationalAffineWall ι) : Prop :=
  ∃ x : ι → ℚ, wall.eval x ≠ 0

/-- A nonzero constant term is an immediate properness witness. -/
theorem proper_of_constant_ne_zero (wall : RationalAffineWall ι)
    (hconstant : wall.constant ≠ 0) : wall.Proper := by
  classical
  refine ⟨fun _ => 0, ?_⟩
  simpa [eval] using hconstant

/-- A nonzero coefficient is an immediate properness witness. -/
theorem proper_of_coefficient_ne_zero (wall : RationalAffineWall ι) {i : ι}
    (hcoefficient : wall.coefficient i ≠ 0) : wall.Proper := by
  classical
  by_cases hconstant : wall.constant ≠ 0
  · exact proper_of_constant_ne_zero wall hconstant
  · refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    simp [eval, not_ne_iff.mp hconstant, hcoefficient]

/-- Scalar multiplication of an affine wall equation. -/
def scale (c : ℚ) (wall : RationalAffineWall ι) : RationalAffineWall ι where
  coefficient i := c * wall.coefficient i
  constant := c * wall.constant

@[simp]
theorem eval_scale (c : ℚ) (wall : RationalAffineWall ι) (x : ι → ℚ) :
    (wall.scale c).eval x = c * wall.eval x := by
  classical
  change (∑ i, (c * wall.coefficient i) * x i) + c * wall.constant =
    c * ((∑ i, wall.coefficient i * x i) + wall.constant)
  calc
    _ = c * (∑ i, wall.coefficient i * x i) + c * wall.constant := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by ring

/-- Difference of two affine wall equations. -/
def sub (first second : RationalAffineWall ι) : RationalAffineWall ι where
  coefficient i := first.coefficient i - second.coefficient i
  constant := first.constant - second.constant

@[simp]
theorem eval_sub (first second : RationalAffineWall ι) (x : ι → ℚ) :
    (first.sub second).eval x = first.eval x - second.eval x := by
  classical
  change (∑ i, (first.coefficient i - second.coefficient i) * x i) +
      (first.constant - second.constant) =
    ((∑ i, first.coefficient i * x i) + first.constant) -
      ((∑ i, second.coefficient i * x i) + second.constant)
  calc
    _ = (∑ i, (first.coefficient i * x i - second.coefficient i * x i)) +
        (first.constant - second.constant) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; ring

/-- The affine equation saying that `wall` has the same value at a variable
start and at the fixed endpoint `target`. -/
def endpointDifference (wall : RationalAffineWall ι) (target : ι → ℚ) :
    RationalAffineWall ι where
  coefficient := wall.coefficient
  constant := wall.constant - wall.eval target

@[simp]
theorem eval_endpointDifference (wall : RationalAffineWall ι)
    (target start : ι → ℚ) :
    (wall.endpointDifference target).eval start = wall.eval start - wall.eval target := by
  unfold endpointDifference eval
  ring

/-- A wall with a nonzero linear coefficient has a proper endpoint-difference
equation at every target. -/
theorem endpointDifference_proper_of_coefficient_ne_zero
    (wall : RationalAffineWall ι) (target : ι → ℚ) {i : ι}
    (hcoefficient : wall.coefficient i ≠ 0) :
    (wall.endpointDifference target).Proper :=
  proper_of_coefficient_ne_zero _ hcoefficient

/-- The affine equation in `start` saying that two walls have the same
crossing time on the segment from `start` to `target`. -/
def collisionWall (first second : RationalAffineWall ι) (target : ι → ℚ) :
    RationalAffineWall ι :=
  (first.scale (second.eval target)).sub (second.scale (first.eval target))

@[simp]
theorem eval_collisionWall (first second : RationalAffineWall ι)
    (target start : ι → ℚ) :
    (collisionWall first second target).eval start =
      second.eval target * first.eval start - first.eval target * second.eval start := by
  simp [collisionWall]

/-- A visibly nonzero collision coefficient certifies that the pairwise
crossing-time collision equation is proper. -/
theorem collisionWall_proper_of_coefficient_ne_zero
    (first second : RationalAffineWall ι) (target : ι → ℚ) {i : ι}
    (hcoefficient :
      second.eval target * first.coefficient i -
        first.eval target * second.coefficient i ≠ 0) :
    (collisionWall first second target).Proper := by
  apply proper_of_coefficient_ne_zero
  simpa [collisionWall, scale, sub] using hcoefficient

/-- A finite family of proper rational affine walls has a common rational
point off every wall. -/
theorem exists_avoids_finset (walls : κ → RationalAffineWall ι) (s : Finset κ)
    (hproper : ∀ k ∈ s, (walls k).Proper) :
    ∃ x : ι → ℚ, ∀ k ∈ s, (walls k).eval x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨x, hx⟩ := ih (fun k hk => hproper k (Finset.mem_insert_of_mem hk))
      obtain ⟨y, hy⟩ := hproper a (Finset.mem_insert_self a s)
      let bad : Finset ℚ :=
        (insert a s).image fun k => (walls k).crossingTime x y
      obtain ⟨t, ht⟩ := bad.exists_notMem
      refine ⟨segment x y t, ?_⟩
      intro k hk hzero
      by_cases hdiff : (walls k).eval x ≠ (walls k).eval y
      · apply ht
        apply Finset.mem_image.mpr
        exact ⟨k, hk,
          (eq_crossingTime_of_eval_segment_eq_zero (walls k) x y hdiff hzero).symm⟩
      · have heq : (walls k).eval x = (walls k).eval y := not_ne_iff.mp hdiff
        have hxk : (walls k).eval x ≠ 0 := by
          rcases Finset.mem_insert.mp hk with rfl | hks
          · rwa [heq]
          · exact hx k hks
        rw [eval_segment, heq, sub_self, mul_zero, add_zero] at hzero
        exact hxk (heq.trans hzero)

/-- Finite proper-wall avoidance can be performed without leaving any given
nonempty rational region defined by finitely many strict affine inequalities. -/
theorem exists_avoids_preserving_positive [Fintype κ] [Fintype η]
    (exceptional : κ → RationalAffineWall ι)
    (constraint : η → RationalAffineWall ι) (base : ι → ℚ)
    (hproper : ∀ k, (exceptional k).Proper)
    (hbase : ∀ l, 0 < (constraint l).eval base) :
    ∃ start : ι → ℚ,
      (∀ l, 0 < (constraint l).eval start) ∧
      ∀ k, (exceptional k).eval start ≠ 0 := by
  classical
  obtain ⟨generic, hgeneric⟩ :=
    exists_avoids_finset exceptional Finset.univ
      (fun k _ => hproper k)
  obtain ⟨δ, hδ, hstep⟩ := exists_positive_step Finset.univ
    (fun l => (constraint l).eval base)
    (fun l => (constraint l).eval generic - (constraint l).eval base)
    (fun l _ => Or.inl (hbase l))
  let bad : Finset ℚ := crossingTimes exceptional base generic
  have hinterval : 0 < min δ 1 := lt_min hδ (by norm_num)
  obtain ⟨t, ht, htbad⟩ := (Set.Ioo_infinite hinterval).exists_notMem_finset bad
  refine ⟨segment base generic t, ?_, ?_⟩
  · intro l
    rw [eval_segment]
    exact hstep t ht.1 (le_trans ht.2.le (min_le_left δ 1)) l (Finset.mem_univ l)
  · intro k hzero
    by_cases hdiff : (exceptional k).eval base ≠ (exceptional k).eval generic
    · apply htbad
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_univ k,
        (eq_crossingTime_of_eval_segment_eq_zero
          (exceptional k) base generic hdiff hzero).symm⟩
    · have heq : (exceptional k).eval base = (exceptional k).eval generic :=
        not_ne_iff.mp hdiff
      rw [eval_segment, heq, sub_self, mul_zero, add_zero] at hzero
      exact hgeneric k (Finset.mem_univ k) (heq ▸ hzero)

/-- Indices for the denominator and pairwise-collision equations which a
generic segment start must avoid. -/
abbrev GenericException (κ : Type*) :=
  κ ⊕ {pair : κ × κ // pair.1 ≠ pair.2}

/-- The denominator equation for one wall, or the collision equation for a
pair of distinct walls. -/
def genericException (walls : κ → RationalAffineWall ι) (target : ι → ℚ) :
    GenericException κ → RationalAffineWall ι
  | Sum.inl k => (walls k).endpointDifference target
  | Sum.inr pair => collisionWall (walls pair.1.1) (walls pair.1.2) target

/-- Equality of two defined crossing times forces the corresponding collision
wall to vanish at the segment start. -/
theorem eval_collisionWall_eq_zero_of_crossingTime_eq
    (first second : RationalAffineWall ι) (target start : ι → ℚ)
    (hfirst : first.eval start ≠ first.eval target)
    (hsecond : second.eval start ≠ second.eval target)
    (heq : first.crossingTime start target = second.crossingTime start target) :
    (collisionWall first second target).eval start = 0 := by
  rw [eval_collisionWall]
  unfold crossingTime at heq
  field_simp [sub_ne_zero.mpr hfirst, sub_ne_zero.mpr hsecond] at heq
  nlinarith [heq]

/-- In any nonempty finite rational open region, proper denominator and
collision equations admit a start whose segment to `target` is simple. -/
theorem exists_simpleAlong_preserving_positive [Fintype κ] [DecidableEq κ]
    [Fintype η] (walls : κ → RationalAffineWall ι) (target : ι → ℚ)
    (constraint : η → RationalAffineWall ι) (base : ι → ℚ)
    (hbase : ∀ l, 0 < (constraint l).eval base)
    (hproper : ∀ e : GenericException κ,
      (genericException walls target e).Proper) :
    ∃ start : ι → ℚ,
      (∀ l, 0 < (constraint l).eval start) ∧
      (∀ k, (walls k).eval start ≠ (walls k).eval target) ∧
      SimpleAlong walls start target := by
  classical
  obtain ⟨start, hconstraint, havoid⟩ :=
    exists_avoids_preserving_positive (genericException walls target)
      constraint base hproper hbase
  have hdiff : ∀ k, (walls k).eval start ≠ (walls k).eval target := by
    intro k
    have h := havoid (Sum.inl k)
    have hsub : (walls k).eval start - (walls k).eval target ≠ 0 := by
      simpa [genericException] using h
    exact sub_ne_zero.mp hsub
  refine ⟨start, hconstraint, hdiff, ?_⟩
  intro first second heq
  by_contra hne
  let pair : {pair : κ × κ // pair.1 ≠ pair.2} := ⟨(first, second), hne⟩
  have hcollision := havoid (Sum.inr pair)
  apply hcollision
  simpa [genericException, pair] using
    eval_collisionWall_eq_zero_of_crossingTime_eq
      (walls first) (walls second) target start (hdiff first) (hdiff second) heq

end RationalAffineWall

end DraismaVargas.Infrastructure
