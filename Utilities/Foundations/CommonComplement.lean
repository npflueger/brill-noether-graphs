module

public import Utilities.Gluing.MarkedTwistDegree

@[expose] public section

/-!
# Effective subtraction and common-complement APIs

This module packages two elementary patterns of residual-chip and transmission
arguments:

* a rank lower bound lets us subtract any effective divisor of the prescribed
  depth and remain winnable;
* the two-complement problem is recorded as a first-class predicate, rather
  than repeatedly unpacking the same pair of canonical winnability conditions.
-/

namespace MarkedGraphs

open Utilities

/-- A rank lower bound supplies a winnability certificate after subtracting any
effective divisor of exactly that depth. -/
theorem winnable_sub_effective_of_rank_ge
    {G : CFGraph} (D A : CFDiv G) (k : ℤ)
    (hRank : rank G D ≥ k) (hAEffective : effective A)
    (hADegree : deg A = k) :
    winnable G (D - A) := by
  have hRankGeq : rank_geq G D k := (rank_geq_iff G D k).mpr hRank
  exact hRankGeq A ⟨hAEffective, hADegree⟩

/-- Two prescribed effective subtractions can be discharged independently from
the corresponding rank bounds.  This is the basic two-depth interface used by
common-splitting arguments. -/
theorem two_depth_winnable_of_rank_ge
    {G : CFGraph} (D A B : CFDiv G) (a b : ℤ)
    (hRankA : rank G D ≥ a) (hRankB : rank G D ≥ b)
    (hAEffective : effective A) (hADegree : deg A = a)
    (hBEffective : effective B) (hBDegree : deg B = b) :
    winnable G (D - A) ∧ winnable G (D - B) := by
  exact ⟨winnable_sub_effective_of_rank_ge D A a hRankA hAEffective hADegree,
    winnable_sub_effective_of_rank_ge D B b hRankB hBEffective hBDegree⟩

/-- A divisor `F` is a common canonical complement for `R` and `S` when it is
effective and both complementary canonical differences remain winnable. -/
def CommonCanonicalComplement
    (G : CFGraph) (R S F : CFDiv G) : Prop :=
  effective F ∧
    winnable G (canonical_divisor G - R - F) ∧
    winnable G (canonical_divisor G - S - F)

/-- Common-complement witnesses are symmetric in the two prescribed divisors. -/
theorem commonCanonicalComplement_symm
    {G : CFGraph} {R S F : CFDiv G} :
    CommonCanonicalComplement G R S F ↔
      CommonCanonicalComplement G S R F := by
  unfold CommonCanonicalComplement
  tauto

/-- The degree-two specialization used by the canonical two-complement problem.
The degree assumptions are included in the predicate so downstream statements
can quantify over witnesses without repeating bookkeeping. -/
def CanonicalTwoComplementWitness
    (G : CFGraph) (R S F : CFDiv G) : Prop :=
  deg R = (genus G : ℤ) - 2 ∧
  deg S = (genus G : ℤ) - 2 ∧
  deg F = 2 ∧
  CommonCanonicalComplement G R S F

/-- Canonical degree-two complement witnesses are symmetric in the two
prescribed divisors. -/
theorem canonicalTwoComplementWitness_symm
    {G : CFGraph} {R S F : CFDiv G} :
    CanonicalTwoComplementWitness G R S F ↔
      CanonicalTwoComplementWitness G S R F := by
  constructor
  · rintro ⟨hR, hS, hF, hCommon⟩
    exact ⟨hS, hR, hF, commonCanonicalComplement_symm.mp hCommon⟩
  · rintro ⟨hS, hR, hF, hCommon⟩
    exact ⟨hR, hS, hF, commonCanonicalComplement_symm.mpr hCommon⟩

/-- A degree-two common-complement witness has complementary canonical
subtractions of degree `g-2`. -/
theorem canonicalTwoComplement_complement_degrees
    {G : CFGraph} {R S F : CFDiv G}
    (h : CanonicalTwoComplementWitness G R S F) :
    deg (canonical_divisor G - R - F) = (genus G : ℤ) - 2 ∧
      deg (canonical_divisor G - S - F) = (genus G : ℤ) - 2 := by
  rcases h with ⟨hR, hS, hF, _⟩
  constructor
  · rw [deg.map_sub, deg.map_sub, degree_of_canonical_divisor, hR, hF]
    ring
  · rw [deg.map_sub, deg.map_sub, degree_of_canonical_divisor, hS, hF]
    ring

end MarkedGraphs
