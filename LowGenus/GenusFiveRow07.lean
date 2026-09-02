import LowGenus.ConfigurationFive
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 07

Row 07 is the length-independent AR configuration-5 row.  Put one chip on
each of `2,3,6,7`.  The chip-free vertices occur in the two symmetric pairs
`0--4` and `1--5`.  On either side, the pair is followed by two parallel paths
to a chip vertex and then by the chip edge `6--7`.

The firing potential below is the integral distance profile implicit in AR's
fifth local picture.  For the outer centre it walks inward from the nearer of
the two boundary sources.  For the inner centre it is the minimum of the two
incoming distances.  Writing the formula with nested minima has two benefits:
it is independent of all edge-length comparisons, and it becomes constant
across every zero-length edge.  Consequently the same script works on every
nonloopy forest face.

The arithmetic itself is core generic and lives in
`LowGenus/ConfigurationFive.lean`: the one-edge ledger,
and the residual-effectivity statement for each of the two nested-min
profiles, stated once against an orientation-agnostic `SlotLedger` and
instantiated here four times -- twice per profile, once in each orientation.
-/

namespace AtanasovRanganathan.GenusFiveRow07

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.CoreOrbitReduction
open Configurations
open Guarding
open GenusFiveCoreAtlas
open ConfigurationFive

def IsChipVertex (v : Fin 8) : Prop :=
  v = 2 ∨ v = 3 ∨ v = 6 ∨ v = 7

instance (v : Fin 8) : Decidable (IsChipVertex v) := by
  unfold IsChipVertex
  infer_instance

def chipWeight (v : Fin 8) : ℤ := if IsChipVertex v then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  by_cases hv : IsChipVertex v <;> simp [chipWeight, hv]

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  d.coreClassDivisor chipWeight

def IsOuterCenter (v : Fin 8) : Prop := v = 0 ∨ v = 1

instance (v : Fin 8) : Decidable (IsOuterCenter v) := by
  unfold IsOuterCenter
  infer_instance

def outer : Fin 8 → Fin 8
  | 0 | 4 => 0
  | 1 | 5 => 1
  | v => v

def inner : Fin 8 → Fin 8
  | 0 | 4 => 4
  | 1 | 5 => 5
  | v => v

def cycleChip : Fin 8 → Fin 8
  | 0 | 4 => 6
  | 1 | 5 => 7
  | v => v

def farChip : Fin 8 → Fin 8
  | 0 | 4 => 7
  | 1 | 5 => 6
  | v => v

def firstOuterArm : Fin 8 → Fin 12
  | 0 | 4 => 0
  | 1 | 5 => 1
  | _ => 0

def secondOuterArm : Fin 8 → Fin 12
  | 0 | 4 => 2
  | 1 | 5 => 3
  | _ => 0

def middleEdge : Fin 8 → Fin 12
  | 0 | 4 => 5
  | 1 | 5 => 6
  | _ => 5

def firstParallel : Fin 8 → Fin 12
  | 0 | 4 => 8
  | 1 | 5 => 10
  | _ => 8

def secondParallel : Fin 8 → Fin 12
  | 0 | 4 => 9
  | 1 | 5 => 11
  | _ => 9

def farEdge (_center : Fin 8) : Fin 12 := 7

def outerArmMin (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (firstOuterArm center))
    (d.length (secondOuterArm center))

def parallelMin (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (firstParallel center))
    (d.length (secondParallel center))

def outerTargetHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (outerArmMin d center)
    (d.length (farEdge center) + parallelMin d center +
      d.length (middleEdge center))

def outerTargetInnerHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (outerTargetHeight d center)
    (d.length (farEdge center) + parallelMin d center)

def outerTargetCycleHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (outerTargetInnerHeight d center) (d.length (farEdge center))

def innerTargetHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (outerArmMin d center + d.length (middleEdge center))
    (d.length (farEdge center) + parallelMin d center)

def innerTargetOuterHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (outerArmMin d center) (innerTargetHeight d center)

def innerTargetCycleHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (farEdge center)) (innerTargetHeight d center)

def outerHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  if IsOuterCenter center then outerTargetHeight d center
  else innerTargetOuterHeight d center

def innerHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  if IsOuterCenter center then outerTargetInnerHeight d center
  else innerTargetHeight d center

def cycleHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  if IsOuterCenter center then outerTargetCycleHeight d center
  else innerTargetCycleHeight d center

def rawPotential (d : DegSpec 8 12) (center v : Fin 8) : ℤ :=
  if v = outer center then -(outerHeight d center : ℤ)
  else if v = inner center then -(innerHeight d center : ℤ)
  else if v = cycleChip center then -(cycleHeight d center : ℤ)
  else 0

/-- Reading the raw profile at the canonical representative makes class
invariance definitional. -/
def firingPotential (d : DegSpec 8 12) (center v : Fin 8) : ℤ :=
  rawPotential d center (d.rep v)

theorem firingPotential_repInvariant (d : DegSpec 8 12) (center : Fin 8) :
    d.RepInvariant (firingPotential d center) := by
  intro v
  simp [firingPotential, d.rep_idem]

@[simp] theorem outerHeight_eq_zero_of_firstArm_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (firstOuterArm center) = 0) :
    outerHeight d center = 0 := by
  by_cases hOuter : IsOuterCenter center <;>
    simp [outerHeight, hOuter, outerTargetHeight, innerTargetOuterHeight,
      innerTargetHeight, outerArmMin, hZero]

@[simp] theorem outerHeight_eq_zero_of_secondArm_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (secondOuterArm center) = 0) :
    outerHeight d center = 0 := by
  by_cases hOuter : IsOuterCenter center <;>
    simp [outerHeight, hOuter, outerTargetHeight, innerTargetOuterHeight,
      innerTargetHeight, outerArmMin, hZero]

@[simp] theorem outerHeight_eq_innerHeight_of_middle_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (middleEdge center) = 0) :
    outerHeight d center = innerHeight d center := by
  by_cases hOuter : IsOuterCenter center
  · simp [outerHeight, innerHeight, hOuter, outerTargetHeight,
      outerTargetInnerHeight, hZero]
  · simp [outerHeight, innerHeight, hOuter, innerTargetOuterHeight,
      innerTargetHeight, hZero]

@[simp] theorem innerHeight_eq_cycleHeight_of_firstParallel_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (firstParallel center) = 0) :
    innerHeight d center = cycleHeight d center := by
  by_cases hOuter : IsOuterCenter center
  · simp [innerHeight, cycleHeight, hOuter, outerTargetInnerHeight,
      outerTargetCycleHeight, parallelMin, hZero]
  · simp [innerHeight, cycleHeight, hOuter, innerTargetHeight,
      innerTargetCycleHeight, parallelMin, hZero]

@[simp] theorem innerHeight_eq_cycleHeight_of_secondParallel_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (secondParallel center) = 0) :
    innerHeight d center = cycleHeight d center := by
  by_cases hOuter : IsOuterCenter center
  · simp [innerHeight, cycleHeight, hOuter, outerTargetInnerHeight,
      outerTargetCycleHeight, parallelMin, hZero]
  · simp [innerHeight, cycleHeight, hOuter, innerTargetHeight,
      innerTargetCycleHeight, parallelMin, hZero]

@[simp] theorem cycleHeight_eq_zero_of_far_zero
    (d : DegSpec 8 12) (center : Fin 8)
    (hZero : d.length (farEdge center) = 0) :
    cycleHeight d center = 0 := by
  by_cases hOuter : IsOuterCenter center <;>
    simp [cycleHeight, hOuter, outerTargetCycleHeight,
      innerTargetCycleHeight, hZero]

theorem rawPotential_eq_of_zero_edge
    (d : DegSpec 8 12) (_hCore : d.core = row07Core)
    {center : Fin 8} (hCenter : ¬IsChipVertex center)
    {e : Fin 12} (hZero : d.length e = 0) :
    rawPotential d center (row07Core.tail e) =
      rawPotential d center (row07Core.head e) := by
  fin_cases center <;> simp [IsChipVertex] at hCenter
  all_goals fin_cases e
  all_goals simp_all [rawPotential, outer, inner, cycleChip, row07Core,
    firstOuterArm, secondOuterArm, middleEdge, firstParallel,
    secondParallel, farEdge]

theorem rawPotential_eq_of_reach
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : ¬IsChipVertex center)
    {u v : Fin 8} (hReach : ReachIn row07Core F u v) :
    rawPotential d center u = rawPotential d center v := by
  induction hReach with
  | refl => rfl
  | @tail a b hPrefix hLast ih =>
      rw [ih]
      obtain ⟨e, he, hab | hab⟩ := hLast
      · rw [← hab.1, ← hab.2]
        exact rawPotential_eq_of_zero_edge d hCore hCenter
          ((hFZero e).mp ((mem_edgeList F e).mp he))
      · rw [← hab.1, ← hab.2]
        exact (rawPotential_eq_of_zero_edge d hCore hCenter
          ((hFZero e).mp ((mem_edgeList F e).mp he))).symm

theorem firingPotential_eq_raw
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : ¬IsChipVertex center) (v : Fin 8) :
    firingPotential d center v = rawPotential d center v := by
  apply rawPotential_eq_of_reach d hCore F hFZero hCenter
  exact (hRepReach (d.rep v) v).mp (d.rep_idem v)

/-! ## Redistributing chips inside contracted classes -/

def firstOuterChip (_center : Fin 8) : Fin 8 := 2
def secondOuterChip (_center : Fin 8) : Fin 8 := 3

export ConfigurationCommon (indicatorWeight transferWeight
  sum_transferWeight_eq_zero sum_indicatorWeight_class
  positiveEndpointContribution positiveEndpointContribution_classSum_eq)

def allocatedWeight (d : DegSpec 8 12) (center vertex : Fin 8) : ℤ :=
  chipWeight vertex +
    (if d.length (firstOuterArm center) = 0 then
      transferWeight (firstOuterChip center) (outer center) vertex else 0) +
    (if d.length (secondOuterArm center) = 0 then
      transferWeight (secondOuterChip center) (outer center) vertex else 0) +
    (if parallelMin d center = 0 then
      transferWeight (cycleChip center) (inner center) vertex else 0) +
    (if d.length (farEdge center) = 0 then
      transferWeight (farChip center) (cycleChip center) vertex else 0)

theorem allocated_class_sum_eq
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (center r : Fin 8) (hCenter : ¬IsChipVertex center) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocatedWeight d center v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  let S := Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r)
  have hFirst : d.length (firstOuterArm center) = 0 →
      d.rep (firstOuterChip center) = d.rep (outer center) := by
    intro hZero
    have h := d.rep_zero (firstOuterArm center) hZero
    fin_cases center <;> simp [IsChipVertex] at hCenter
    all_goals
      simp only [hCore, row07Core, Fin.isValue, firstOuterArm, Fin.zero_eta, Matrix.cons_val_zero,
        firstOuterChip, outer, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk] at h ⊢;
      first | exact h | exact h.symm
  have hSecond : d.length (secondOuterArm center) = 0 →
      d.rep (secondOuterChip center) = d.rep (outer center) := by
    intro hZero
    have h := d.rep_zero (secondOuterArm center) hZero
    fin_cases center <;> simp [IsChipVertex] at hCenter
    all_goals
      simp only [hCore, row07Core, Fin.isValue, secondOuterArm, Fin.zero_eta, Matrix.cons_val,
        secondOuterChip, outer, Fin.mk_one, Fin.reduceFinMk] at h ⊢;
      first | exact h | exact h.symm
  have hParallel : parallelMin d center = 0 →
      d.rep (cycleChip center) = d.rep (inner center) := by
    intro hZero
    have hEither : d.length (firstParallel center) = 0 ∨
        d.length (secondParallel center) = 0 := by
      simpa [parallelMin, Nat.min_eq_zero_iff] using hZero
    rcases hEither with hFirstZero | hSecondZero
    · have h := d.rep_zero (firstParallel center) hFirstZero
      fin_cases center <;> simp [IsChipVertex] at hCenter
      all_goals
        simp only [hCore, row07Core, Fin.isValue, firstParallel, Fin.zero_eta, Matrix.cons_val,
          cycleChip, inner, Fin.mk_one, Fin.reduceFinMk] at h ⊢;
        first | exact h | exact h.symm
    · have h := d.rep_zero (secondParallel center) hSecondZero
      fin_cases center <;> simp [IsChipVertex] at hCenter
      all_goals
        simp only [hCore, row07Core, Fin.isValue, secondParallel, Fin.zero_eta, Matrix.cons_val,
          cycleChip, inner, Fin.mk_one, Fin.reduceFinMk] at h ⊢;
        first | exact h | exact h.symm
  have hFar : d.length (farEdge center) = 0 →
      d.rep (farChip center) = d.rep (cycleChip center) := by
    intro hZero
    have h := d.rep_zero (farEdge center) hZero
    fin_cases center <;> simp [IsChipVertex] at hCenter
    all_goals
      simp only [hCore, row07Core, Fin.isValue, farEdge, Matrix.cons_val, farChip, Fin.zero_eta,
        cycleChip, Fin.mk_one, Fin.reduceFinMk] at h ⊢;
      first | exact h | exact h.symm
  have hConditional (P : Prop) [Decidable P] (source target : Fin 8)
      (hRep : P → d.rep source = d.rep target) :
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          (if P then transferWeight source target v else 0) = 0 := by
    by_cases hP : P
    · simp only [if_pos hP]
      exact sum_transferWeight_eq_zero d (hRep hP) r
    · simp [hP]
  simp only [allocatedWeight, Finset.sum_add_distrib]
  rw [hConditional _ _ _ hFirst, hConditional _ _ _ hSecond,
    hConditional _ _ _ hParallel, hConditional _ _ _ hFar]
  simp

def targetOwner (d : DegSpec 8 12) (center : Fin 8) : Fin 8 :=
  if d.length (middleEdge center) = 0 then
    if outerArmMin d center ≤
        d.length (farEdge center) + parallelMin d center then outer center
    else inner center
  else center

theorem targetOwner_rep_eq_center
    (d : DegSpec 8 12) (hCore : d.core = row07Core) (center : Fin 8)
    (hCenter : ¬IsChipVertex center) :
    d.rep (targetOwner d center) = d.rep center := by
  unfold targetOwner
  split_ifs with hMiddle hSide
  · have h := d.rep_zero (middleEdge center) hMiddle
    fin_cases center <;> simp [IsChipVertex] at hCenter
    all_goals
      simp [hCore, middleEdge, outer, row07Core] at h ⊢
    all_goals exact h
  · have h := d.rep_zero (middleEdge center) hMiddle
    fin_cases center <;> simp [IsChipVertex] at hCenter
    all_goals
      simp only [hCore, row07Core, Fin.isValue, middleEdge, Fin.zero_eta, Matrix.cons_val, inner,
        Fin.mk_one, Fin.reduceFinMk] at h ⊢<;>
      first | exact h | exact h.symm
  · rfl

/-! ## Endpoint accounting on the contracted face -/

def rawHeight (d : DegSpec 8 12) (center v : Fin 8) : ℕ :=
  if v = outer center then outerHeight d center
  else if v = inner center then innerHeight d center
  else if v = cycleChip center then cycleHeight d center
  else 0

theorem rawPotential_eq_neg_rawHeight
    (d : DegSpec 8 12) (center v : Fin 8) :
    rawPotential d center v = -(rawHeight d center v : ℤ) := by
  unfold rawPotential rawHeight
  split_ifs <;> omega

abbrev endpointContribution := @ConfigurationCommon.endpointContribution 8 12
abbrev endpointPair := @ConfigurationCommon.endpointPair 8 12

theorem positiveEndpointContribution_eq_heightForm
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : ¬IsChipVertex center) (v : Fin 8) :
    positiveEndpointContribution d (firingPotential d center) v =
      ∑ e : Fin 12,
        ((if d.core.tail e = v then
            tailContribution (d.length e) (rawHeight d center (d.core.tail e))
              (rawHeight d center (d.core.head e)) else 0) +
        (if d.core.head e = v then
            headContribution (d.length e) (rawHeight d center (d.core.tail e))
              (rawHeight d center (d.core.head e)) else 0)) := by
  have hp : firingPotential d center = rawPotential d center := by
    funext w
    exact firingPotential_eq_raw d hCore F hRepReach hFZero hCenter w
  rw [hp]
  unfold positiveEndpointContribution tailContribution headContribution
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · simp [hZero]
  · have hTail := rawPotential_eq_neg_rawHeight d center (d.core.tail e)
    have hHead := rawPotential_eq_neg_rawHeight d center (d.core.head e)
    have hRise : d.coreRise (rawPotential d center) e =
        (rawHeight d center (d.core.tail e) : ℤ) -
          (rawHeight d center (d.core.head e) : ℤ) := by
      unfold DegSpec.coreRise
      rw [hTail, hHead]
      ring
    simp [hZero, hRise]

def center0Coefficient (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (d.length 0) + zeroChip (d.length 2) -
      (if d.length 5 = 0 then
        if outerArmMin d 0 ≤ d.length 7 + parallelMin d 0 then 1 else 0
      else 1) +
      (tailContribution (d.length 0) (outerHeight d 0) 0 +
        tailContribution (d.length 2) (outerHeight d 0) 0 +
        tailContribution (d.length 5) (outerHeight d 0) (innerHeight d 0))
  else if v = 2 then
    positiveChip (d.length 0) +
      headContribution (d.length 0) (outerHeight d 0) 0
  else if v = 3 then
    positiveChip (d.length 2) +
      headContribution (d.length 2) (outerHeight d 0) 0
  else if v = 4 then
    zeroChip (parallelMin d 0) -
      (if d.length 5 = 0 then
        if outerArmMin d 0 ≤ d.length 7 + parallelMin d 0 then 0 else 1
      else 0) +
      (headContribution (d.length 5) (outerHeight d 0) (innerHeight d 0) +
        tailContribution (d.length 8) (innerHeight d 0) (cycleHeight d 0) +
        tailContribution (d.length 9) (innerHeight d 0) (cycleHeight d 0))
  else if v = 6 then
    positiveChip (parallelMin d 0) + zeroChip (d.length 7) +
      (headContribution (d.length 8) (innerHeight d 0) (cycleHeight d 0) +
        headContribution (d.length 9) (innerHeight d 0) (cycleHeight d 0) +
        tailContribution (d.length 7) (cycleHeight d 0) 0)
  else if v = 7 then
    positiveChip (d.length 7) +
      headContribution (d.length 7) (cycleHeight d 0) 0
  else 0

theorem center0Coefficient_eq
    (d : DegSpec 8 12) (hCore : d.core = row07Core) (v : Fin 8) :
    allocatedWeight d 0 v - indicatorWeight v (targetOwner d 0) +
        ∑ edge : Fin 12,
          ((if d.core.tail edge = v then
              tailContribution (d.length edge)
                (rawHeight d 0 (d.core.tail edge))
                (rawHeight d 0 (d.core.head edge)) else 0) +
          (if d.core.head edge = v then
              headContribution (d.length edge)
                (rawHeight d 0 (d.core.tail edge))
                (rawHeight d 0 (d.core.head edge)) else 0)) =
      center0Coefficient d v := by
  fin_cases v <;>
    by_cases hc : d.length 5 = 0 <;>
    by_cases hs : outerArmMin d 0 ≤ d.length 7 + parallelMin d 0 <;>
    simp only [allocatedWeight, chipWeight, IsChipVertex, Fin.zero_eta, Fin.isValue, Fin.reduceEq,
      or_self, ↓reduceIte, firstOuterArm, transferWeight, indicatorWeight, outer, firstOuterChip,
      sub_zero, zero_add, secondOuterArm, secondOuterChip, inner, cycleChip, sub_self, ite_self,
      add_zero, farEdge, farChip, targetOwner, middleEdge, hc, hs, hCore, row07Core, rawHeight,
      outerHeight, IsOuterCenter, zero_ne_one, or_false, innerHeight, cycleHeight,
      Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, one_ne_zero,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
      Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_const_zero, center0Coefficient,
      zeroChip, add_right_inj, Fin.mk_one, headContribution_same, tailContribution_same,
      Fin.reduceFinMk, zero_sub, Int.reduceNeg, positiveChip, add_left_inj, or_true]<;>
    try split_ifs
  all_goals ring

theorem localResidual_nonneg_center0
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    (v : Fin 8) :
    0 ≤ allocatedWeight d 0 v - indicatorWeight v (targetOwner d 0) +
      positiveEndpointContribution d (firingPotential d 0) v := by
  rw [positiveEndpointContribution_eq_heightForm d hCore F hRepReach hFZero
    (by decide) v]
  rw [center0Coefficient_eq d hCore v]
  have ha : outerArmMin d 0 = min (d.length 0) (d.length 2) := rfl
  have hm : parallelMin d 0 = min (d.length 8) (d.length 9) := rfl
  have ho : outerHeight d 0 =
      min (outerArmMin d 0)
        (d.length 7 + parallelMin d 0 + d.length 5) := rfl
  have hi : innerHeight d 0 =
      min (outerHeight d 0) (d.length 7 + parallelMin d 0) := rfl
  have he : cycleHeight d 0 = min (innerHeight d 0) (d.length 7) := rfl
  fin_cases v
  · exact outerTarget_center_nonneg forward forward ha hm ho hi
  · simp [center0Coefficient]
  · exact forward.positiveChip_add_head_nonneg
      (show outerHeight d 0 ≤ d.length 0 by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show outerHeight d 0 ≤ d.length 2 by omega)
  · exact outerTarget_inner_nonneg hm ho hi he
  · simp [center0Coefficient]
  · exact cycle_nonneg forward hm
      (show cycleHeight d 0 ≤ innerHeight d 0 by omega)
      (show cycleHeight d 0 ≤ d.length 7 by omega)
      (show cycleHeight d 0 = innerHeight d 0 ∨
        cycleHeight d 0 = d.length 7 by omega)
      (show innerHeight d 0 ≤ cycleHeight d 0 + parallelMin d 0
        by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show cycleHeight d 0 ≤ d.length 7 by omega)

/-! The inner centres use the second nested-min profile from AR configuration
5.  The endpoint ledger is unchanged; only the order in which the two
possible incoming routes saturate is reversed. -/

def center4Coefficient (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (d.length 0) + zeroChip (d.length 2) -
      (if d.length 5 = 0 then
        if outerArmMin d 4 ≤ d.length 7 + parallelMin d 4 then 1 else 0
      else 0) +
      (tailContribution (d.length 0) (outerHeight d 4) 0 +
        tailContribution (d.length 2) (outerHeight d 4) 0 +
        tailContribution (d.length 5) (outerHeight d 4) (innerHeight d 4))
  else if v = 2 then
    positiveChip (d.length 0) + headContribution (d.length 0) (outerHeight d 4) 0
  else if v = 3 then
    positiveChip (d.length 2) + headContribution (d.length 2) (outerHeight d 4) 0
  else if v = 4 then
    zeroChip (parallelMin d 4) -
      (if d.length 5 = 0 then
        if outerArmMin d 4 ≤ d.length 7 + parallelMin d 4 then 0 else 1
      else 1) +
      (headContribution (d.length 5) (outerHeight d 4) (innerHeight d 4) +
        tailContribution (d.length 8) (innerHeight d 4) (cycleHeight d 4) +
        tailContribution (d.length 9) (innerHeight d 4) (cycleHeight d 4))
  else if v = 6 then
    positiveChip (parallelMin d 4) + zeroChip (d.length 7) +
      (headContribution (d.length 8) (innerHeight d 4) (cycleHeight d 4) +
        headContribution (d.length 9) (innerHeight d 4) (cycleHeight d 4) +
        tailContribution (d.length 7) (cycleHeight d 4) 0)
  else if v = 7 then
    positiveChip (d.length 7) + headContribution (d.length 7) (cycleHeight d 4) 0
  else 0

theorem center4Coefficient_eq
    (d : DegSpec 8 12) (hCore : d.core = row07Core) (v : Fin 8) :
    allocatedWeight d 4 v - indicatorWeight v (targetOwner d 4) +
        ∑ edge : Fin 12,
          ((if d.core.tail edge = v then
              tailContribution (d.length edge)
                (rawHeight d 4 (d.core.tail edge))
                (rawHeight d 4 (d.core.head edge)) else 0) +
          (if d.core.head edge = v then
              headContribution (d.length edge)
                (rawHeight d 4 (d.core.tail edge))
                (rawHeight d 4 (d.core.head edge)) else 0)) =
      center4Coefficient d v := by
  fin_cases v <;>
    by_cases hc : d.length 5 = 0 <;>
    by_cases hs : outerArmMin d 4 ≤ d.length 7 + parallelMin d 4 <;>
    simp only [allocatedWeight, chipWeight, IsChipVertex, Fin.zero_eta, Fin.isValue, Fin.reduceEq,
      or_self, ↓reduceIte, firstOuterArm, transferWeight, indicatorWeight, outer, firstOuterChip,
      sub_zero, zero_add, secondOuterArm, secondOuterChip, inner, cycleChip, sub_self, ite_self,
      add_zero, farEdge, farChip, targetOwner, middleEdge, hc, hs, hCore, row07Core, rawHeight,
      outerHeight, IsOuterCenter, innerHeight, cycleHeight, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, one_ne_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_const_zero,
      center4Coefficient, zeroChip, add_right_inj, Fin.mk_one, zero_ne_one, headContribution_same,
      tailContribution_same, Fin.reduceFinMk, or_false, zero_sub, Int.reduceNeg, positiveChip,
      add_left_inj, or_true]<;>
    try split_ifs
  all_goals ring

theorem localResidual_nonneg_center4
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    (v : Fin 8) :
    0 ≤ allocatedWeight d 4 v - indicatorWeight v (targetOwner d 4) +
      positiveEndpointContribution d (firingPotential d 4) v := by
  rw [positiveEndpointContribution_eq_heightForm d hCore F hRepReach hFZero
    (by decide) v]
  rw [center4Coefficient_eq d hCore v]
  have ha : outerArmMin d 4 = min (d.length 0) (d.length 2) := rfl
  have hm : parallelMin d 4 = min (d.length 8) (d.length 9) := rfl
  have hi : innerHeight d 4 =
      min (outerArmMin d 4 + d.length 5)
        (d.length 7 + parallelMin d 4) := rfl
  have ho : outerHeight d 4 = min (outerArmMin d 4) (innerHeight d 4) :=
    rfl
  have he : cycleHeight d 4 = min (d.length 7) (innerHeight d 4) := rfl
  fin_cases v
  · exact innerTarget_center_nonneg forward forward ha hm hi ho
  · simp [center4Coefficient]
  · exact forward.positiveChip_add_head_nonneg
      (show outerHeight d 4 ≤ d.length 0 by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show outerHeight d 4 ≤ d.length 2 by omega)
  · exact innerTarget_inner_nonneg hm hi ho he
  · simp [center4Coefficient]
  · exact cycle_nonneg forward hm
      (show cycleHeight d 4 ≤ innerHeight d 4 by omega)
      (show cycleHeight d 4 ≤ d.length 7 by omega)
      (show cycleHeight d 4 = innerHeight d 4 ∨
        cycleHeight d 4 = d.length 7 by omega)
      (show innerHeight d 4 ≤ cycleHeight d 4 + parallelMin d 4
        by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show cycleHeight d 4 ≤ d.length 7 by omega)

/-! ## From the four local readings to the degree-four pencil -/

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]


/-! ## The two base centres

Row 07's chip weight `{2, 3, 6, 7}` is fixed by a group of order two, so the
chip-free vertices fall into two orbits, `{0, 1}` and `{4, 5}`.  One outer
reading and one inner reading are therefore the row's whole content; the
docstrings above already said that the second of each pair is "the same metric
profile with all four boundary arms read in the opposite orientation", and that
sentence is now the proof rather than a remark. -/

/-- The two centres the pictures are actually proved at. -/
def IsBaseCenter (v : Fin 8) : Prop := v = 0 ∨ v = 4

instance (v : Fin 8) : Decidable (IsBaseCenter v) := by
  unfold IsBaseCenter
  infer_instance

theorem baseCenter_not_chip {v : Fin 8} (h : IsBaseCenter v) :
    ¬ IsChipVertex v := by
  rcases h with rfl | rfl <;> decide

theorem localResidual_nonneg
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center) (v : Fin 8) :
    0 ≤ allocatedWeight d center v -
        indicatorWeight v (targetOwner d center) +
      positiveEndpointContribution d (firingPotential d center) v := by
  rcases hCenter with rfl | rfl
  · exact localResidual_nonneg_center0 d hCore F hRepReach hFZero v
  · exact localResidual_nonneg_center4 d hCore F hRepReach hFZero v


theorem residual_effective
    (d : DegSpec 8 12) (hCore : d.core = row07Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row07Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center) :
    effective (rowDivisor d - one_chip (d.coreVertex center) +
      prin d.graph (d.interpolatedScript (firingPotential d center))) := by
  let potential := firingPotential d center
  have hInv : d.RepInvariant potential := firingPotential_repInvariant d center
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    change 0 ≤ rowDivisor d (d.coreVertex r) -
      one_chip (G := d.graph) (d.coreVertex center) (d.coreVertex r) +
      prin d.graph (d.interpolatedScript potential) (d.coreVertex r)
    rw [rowDivisor, d.coreClassDivisor_coreVertex]
    rw [← allocated_class_sum_eq d hCore center r (baseCenter_not_chip hCenter)]
    rw [← positiveEndpointContribution_classSum_eq d potential hInv r]
    have hOwner := targetOwner_rep_eq_center d hCore center
      (baseCenter_not_chip hCenter)
    have hIndicator := sum_indicatorWeight_class d (targetOwner d center) r
    have hOneChip :
        one_chip (G := d.graph) (d.coreVertex center) (d.coreVertex r) =
          ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
            indicatorWeight v (targetOwner d center) := by
      rw [hIndicator]
      simp only [one_chip, d.coreVertex_eq_iff]
      rw [hOwner]
      simp only [eq_comm]
    rw [hOneChip]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro v _hv
    simpa [potential, sub_eq_add_neg, add_assoc] using
      localResidual_nonneg d hCore F hRepReach hFZero hCenter v
  · obtain ⟨edge, offset⟩ := interior
    change 0 ≤ rowDivisor d (d.interiorVertex edge offset) -
      one_chip (G := d.graph) (d.coreVertex center)
        (d.interiorVertex edge offset) +
      prin d.graph (d.interpolatedScript potential)
        (d.interiorVertex edge offset)
    rw [rowDivisor, d.coreClassDivisor_interiorVertex]
    have hNe : d.coreVertex center ≠ d.interiorVertex edge offset := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    simp only [one_chip, if_neg hNe.symm, zero_sub, neg_zero, zero_add]
    exact d.prin_interpolatedScript_interiorVertex_nonneg hInv edge offset

/-! ## The symmetry that exchanges the two orientations

`swap` is the whole automorphism group of row 07's chip weight beyond the
identity: `(0 1)(4 5)(6 7)`, which reflects the picture and carries each base
centre to its opposite-orientation twin.

It carries its own inverse — it is an involution — because
`ClosedOrbit.targetLength` is `fun e => length (slotPerm.symm e)` and
`Equiv.symm` of an `Equiv.ofBijective` does not reduce in the kernel; see the
module docstring of `LowGenus/GuardingOrbit.lean`. -/

/-- The identity. -/
def blockSym0 : CoreSymmetry row07Core :=
  CoreSymmetry.ofInverses row07Core
    (vertexTable [0, 1, 2, 3, 4, 5, 6, 7]) (vertexTable [0, 1, 2, 3, 4, 5, 6, 7])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 1)(4 5)(6 7)`.  Carries the outer base centre `0` to `1` and the inner
base centre `4` to `5`. -/
def swap : CoreSymmetry row07Core :=
  CoreSymmetry.ofInverses row07Core
    (vertexTable [1, 0, 2, 3, 5, 4, 7, 6]) (vertexTable [1, 0, 2, 3, 5, 4, 7, 6])
    (slotTable [1, 0, 3, 2, 4, 6, 5, 7, 10, 11, 8, 9])
    (slotTable [1, 0, 3, 2, 4, 6, 5, 7, 10, 11, 8, 9])
    (flagTable [true, true, true, true, false, false, false, true, false,
      false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The base centre of each chip-free vertex's orbit. -/
def base : Fin 8 → Fin 8 := fun v =>
  if v = 1 then 0 else if v = 5 then 4 else v

/-- The symmetry carrying `base v` to `v`. -/
def mover : Fin 8 → CoreSymmetry row07Core := fun v =>
  if v = 1 then swap else if v = 5 then swap else blockSym0

/-! ## The orbit guard -/

/-- **Row 07 as an orbit guard.**  Chips on `2, 3, 6, 7`; AR's fifth picture
read once at the outer centre `0` and once at the inner centre `4`, each moved
to its reflection by `swap`.  The closing step is
`Guarding.OrbitGuard.closedConstruction` -- no row-specific rank transport, no
hand-rolled pencil. -/
def row07Orbit : OrbitGuard row07Core (by norm_num) 4 where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  base := base
  mover := mover
  mover_chips := by decide
  mover_hits := by decide
  guard_base := by
    intro v hv length forest not_loopy
    have hBase : IsBaseCenter (base v) := by
      revert hv
      fin_cases v <;> decide
    exact (DharMove.ofScript _
      (residual_effective _ rfl (zeroSlots length)
        (fun x y => compFold_iff row07Core (zeroSlots length) x y)
        (mem_zeroSlots length) hBase)).reaches

/-- The AR construction on row 07, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row07_closedConstruction :
    ClosedSubdivisionDharConstruction row07Core (by norm_num) :=
  row07Orbit.closedConstruction row07_connected

end AtanasovRanganathan.GenusFiveRow07