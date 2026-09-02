import LowGenus.ConfigurationThreeChain
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 03

Row 03 is two theta graphs joined by two edges.  Block `A` has hubs `0, 1`
joined by the direct slot `4` and by the two subdivided branches `0-2-1` and
`0-3-1`; block `B` has hubs `4, 5` joined by the banana `9, 10` and by the
branch `4-6-7-5`; the connectors are `2-6` (slot `5`) and `3-7` (slot `7`).

Put one chip on each hub: `0, 1, 4, 5`.  The chip-free vertices `2, 3, 6, 7`
then form the path `2 - 6 - 7 - 3`, and each centre sees a chip-free
*three*-chain with four chip leaves.  Concretely there are two pictures,
exchanged by the automorphism `(2 3)(6 7)(4 5)`:

* `G  :` spine `2 - 6 - 7`, leaves `0, 1` at `2`, leaf `4` at `6`, leaf `5`
  at `7`.  Centre `2` reads it at the end, centre `6` in the middle.
* `G' :` spine `3 - 7 - 6`, leaves `0, 1` at `3`, leaf `5` at `7`, leaf `4`
  at `6`.  Centre `3` reads it at the end, centre `7` in the middle.

That local picture is not one of Atanasov--Ranganathan's eleven; see the
module docstring of `LowGenus/ConfigurationThreeChain.lean`,
which carries the arithmetic and the two nested-min profiles.  All this file
does is name the row's lookup tables, check the incidence facts, and run the
same closed-face bookkeeping as `GenusFiveRow07`.

No core-supported degree-four divisor on this row is covered by
configurations 2, 3 and 5 alone: vertices `4` and `5` must both carry chips
(their third slot is a banana), and every remaining choice leaves a chip-free
vertex with two chip-free neighbours or a chip-free pair that touches only two
of the four chips.
-/

namespace AtanasovRanganathan.GenusFiveRow03

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
open ConfigurationThreeChain

/-! ## The divisor -/

def IsChipVertex (v : Fin 8) : Prop :=
  v = 0 ∨ v = 1 ∨ v = 4 ∨ v = 5

instance (v : Fin 8) : Decidable (IsChipVertex v) := by
  unfold IsChipVertex
  infer_instance

/-- The two centres the pictures are actually proved at: one reading at the end
of the chip-free three-chain and one in its middle.  The other two chip-free
vertices are their images under `swap`, and every centre-parameterised
statement below is therefore proved at two centres rather than four. -/
def IsBaseCenter (v : Fin 8) : Prop := v = 2 ∨ v = 6

instance (v : Fin 8) : Decidable (IsBaseCenter v) := by
  unfold IsBaseCenter
  infer_instance

theorem baseCenter_not_chip {v : Fin 8} (h : IsBaseCenter v) :
    ¬ IsChipVertex v := by
  rcases h with rfl | rfl <;> decide

def chipWeight (v : Fin 8) : ℤ := if IsChipVertex v then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  by_cases hv : IsChipVertex v <;> simp [chipWeight, hv]

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  d.coreClassDivisor chipWeight

/-! ## The two pictures

Each chip-free centre names a chip-free three-chain `firstChain -
secondChain - thirdChain` together with its four chip leaves and six slots. -/

/-- The centres that read their picture at the end of the chain. -/
def IsEndCenter (v : Fin 8) : Prop := v = 2 ∨ v = 3

instance (v : Fin 8) : Decidable (IsEndCenter v) := by
  unfold IsEndCenter
  infer_instance

def firstChain : Fin 8 → Fin 8
  | 2 | 6 => 2
  | 3 | 7 => 3
  | v => v

def secondChain : Fin 8 → Fin 8
  | 2 | 6 => 6
  | 3 | 7 => 7
  | v => v

def thirdChain : Fin 8 → Fin 8
  | 2 | 6 => 7
  | 3 | 7 => 6
  | v => v

def chipOne (_center : Fin 8) : Fin 8 := 0
def chipTwo (_center : Fin 8) : Fin 8 := 1

def chipThree : Fin 8 → Fin 8
  | 2 | 6 => 4
  | 3 | 7 => 5
  | v => v

def chipFour : Fin 8 → Fin 8
  | 2 | 6 => 5
  | 3 | 7 => 4
  | v => v

def armOne : Fin 8 → Fin 12
  | 2 | 6 => 0
  | 3 | 7 => 2
  | _ => 0

def armTwo : Fin 8 → Fin 12
  | 2 | 6 => 1
  | 3 | 7 => 3
  | _ => 1

def midOne : Fin 8 → Fin 12
  | 2 | 6 => 5
  | 3 | 7 => 7
  | _ => 5

def armThree : Fin 8 → Fin 12
  | 2 | 6 => 6
  | 3 | 7 => 8
  | _ => 6

def midTwo (_center : Fin 8) : Fin 12 := 11

def armFour : Fin 8 → Fin 12
  | 2 | 6 => 8
  | 3 | 7 => 6
  | _ => 8

/-- Slot `armOne` runs from its chip into the chain in both pictures. -/
def armOneLedger (_center : Fin 8) : ChainLedger := reverse

/-- Slot `midTwo` is the single slot whose orientation differs between the
two pictures: `6 - 7` runs out of the second chain vertex on `G` and into it
on `G'`. -/
def midTwoLedger : Fin 8 → ChainLedger
  | 2 | 6 => forward
  | _ => reverse

/-! ## The nested-min heights -/

def armMin (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (armOne center)) (d.length (armTwo center))

def baseHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (armFour center)) (d.length (armThree center))

def endMid (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (midTwo center))
    (min (d.length (armThree center) - baseHeight d center) (armMin d center))

def endTop (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (midOne center)) (armMin d center - endMid d center)

def midLow (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (armMin d center)
    (min (d.length (midTwo center))
      (d.length (armThree center) - baseHeight d center))

def midHigh (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  min (d.length (midOne center))
    (min (d.length (midTwo center) - midLow d center)
      (d.length (armThree center) - baseHeight d center - midLow d center))

/-- The height at the first chain vertex. -/
def firstHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  if IsEndCenter center then
    baseHeight d center + endMid d center + endTop d center
  else baseHeight d center + midLow d center

/-- The height at the second chain vertex. -/
def secondHeight (d : DegSpec 8 12) (center : Fin 8) : ℕ :=
  if IsEndCenter center then baseHeight d center + endMid d center
  else baseHeight d center + midLow d center + midHigh d center

/-- The two lower chips sit at height zero; the far chain vertex, the two
upper chips and everything off the picture sit at the ambient height. -/
def rawHeight (d : DegSpec 8 12) (center v : Fin 8) : ℕ :=
  if v = firstChain center then firstHeight d center
  else if v = secondChain center then secondHeight d center
  else if v = chipThree center then 0
  else if v = chipFour center then 0
  else baseHeight d center

def rawPotential (d : DegSpec 8 12) (center v : Fin 8) : ℤ :=
  -(rawHeight d center v : ℤ)

/-- Reading the raw profile at the canonical representative makes class
invariance definitional. -/
def firingPotential (d : DegSpec 8 12) (center v : Fin 8) : ℤ :=
  rawPotential d center (d.rep v)

theorem firingPotential_repInvariant (d : DegSpec 8 12) (center : Fin 8) :
    d.RepInvariant (firingPotential d center) := by
  intro v
  simp [firingPotential, d.rep_idem]

theorem rawPotential_eq_neg_rawHeight
    (d : DegSpec 8 12) (center v : Fin 8) :
    rawPotential d center v = -(rawHeight d center v : ℤ) := rfl

/-! ## Every height is constant along a collapsed slot -/

theorem rawHeight_eq_of_zero_edge
    (d : DegSpec 8 12) {center : Fin 8} (hCenter : IsBaseCenter center)
    (e : Fin 12) :
    d.length e = 0 →
      rawHeight d center (row03Core.tail e) =
        rawHeight d center (row03Core.head e) := by
  fin_cases center <;> simp [IsBaseCenter] at hCenter
  all_goals fin_cases e
  all_goals
    simp [rawHeight, firstHeight, secondHeight, baseHeight, armMin,
      endMid, endTop, midLow, midHigh, IsEndCenter, firstChain, secondChain,
      chipThree, chipFour, armOne, armTwo,
      midOne, armThree, midTwo, armFour, row03Core]
  all_goals omega

theorem rawPotential_eq_of_zero_edge
    (d : DegSpec 8 12) {center : Fin 8} (hCenter : IsBaseCenter center)
    {e : Fin 12} (hZero : d.length e = 0) :
    rawPotential d center (row03Core.tail e) =
      rawPotential d center (row03Core.head e) := by
  rw [rawPotential, rawPotential,
    rawHeight_eq_of_zero_edge d hCenter e hZero]

theorem rawPotential_eq_of_reach
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center)
    {u v : Fin 8} (hReach : ReachIn row03Core F u v) :
    rawPotential d center u = rawPotential d center v := by
  induction hReach with
  | refl => rfl
  | @tail a b hPrefix hLast ih =>
      rw [ih]
      obtain ⟨e, he, hab | hab⟩ := hLast
      · rw [← hab.1, ← hab.2]
        exact rawPotential_eq_of_zero_edge d hCenter
          ((hFZero e).mp ((mem_edgeList F e).mp he))
      · rw [← hab.1, ← hab.2]
        exact (rawPotential_eq_of_zero_edge d hCenter
          ((hFZero e).mp ((mem_edgeList F e).mp he))).symm

theorem firingPotential_eq_raw
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row03Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center) (v : Fin 8) :
    firingPotential d center v = rawPotential d center v := by
  apply rawPotential_eq_of_reach d F hFZero hCenter
  exact (hRepReach (d.rep v) v).mp (d.rep_idem v)

/-! ## Redistributing chips inside contracted classes -/

export ConfigurationCommon (indicatorWeight transferWeight
  sum_transferWeight_eq_zero sum_indicatorWeight_class
  positiveEndpointContribution positiveEndpointContribution_classSum_eq)

/-- One chip is moved from the far chain vertex to the middle one when the
middle slot collapses and the far leaf is the shorter of the two lower
leaves: then the single incoming chip lands on the middle vertex. -/
def shiftWeight (d : DegSpec 8 12) (center : Fin 8) : ℤ :=
  if d.length (midTwo center) = 0 ∧
      d.length (armFour center) < d.length (armThree center) then 1 else 0

def allocatedWeight (d : DegSpec 8 12) (center vertex : Fin 8) : ℤ :=
  chipWeight vertex +
    (if d.length (armOne center) = 0 then
      transferWeight (chipOne center) (firstChain center) vertex else 0) +
    (if d.length (armTwo center) = 0 then
      transferWeight (chipTwo center) (firstChain center) vertex else 0) +
    (if d.length (armThree center) = 0 then
      transferWeight (chipThree center) (secondChain center) vertex else 0) +
    (if d.length (armFour center) = 0 then
      transferWeight (chipFour center) (thirdChain center) vertex else 0) +
    (if d.length (midTwo center) = 0 ∧
        d.length (armFour center) < d.length (armThree center) then
      transferWeight (thirdChain center) (secondChain center) vertex else 0)

theorem allocated_class_sum_eq
    (d : DegSpec 8 12) (hCore : d.core = row03Core)
    (center r : Fin 8) (hCenter : IsBaseCenter center) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocatedWeight d center v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  have hOne : d.length (armOne center) = 0 →
      d.rep (chipOne center) = d.rep (firstChain center) := by
    intro hZero
    have h := d.rep_zero (armOne center) hZero
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, armOne, Fin.reduceFinMk, Matrix.cons_val_zero,
        chipOne, firstChain] at h ⊢;
      exact h
  have hTwo : d.length (armTwo center) = 0 →
      d.rep (chipTwo center) = d.rep (firstChain center) := by
    intro hZero
    have h := d.rep_zero (armTwo center) hZero
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, armTwo, Fin.reduceFinMk, Matrix.cons_val_one,
        Matrix.cons_val_zero, chipTwo, firstChain] at h ⊢;
      first | exact h | exact h.symm
  have hThree : d.length (armThree center) = 0 →
      d.rep (chipThree center) = d.rep (secondChain center) := by
    intro hZero
    have h := d.rep_zero (armThree center) hZero
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, armThree, Fin.reduceFinMk, Matrix.cons_val,
        chipThree, secondChain] at h ⊢;
      first | exact h | exact h.symm
  have hFour : d.length (armFour center) = 0 →
      d.rep (chipFour center) = d.rep (thirdChain center) := by
    intro hZero
    have h := d.rep_zero (armFour center) hZero
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, armFour, Fin.reduceFinMk, Matrix.cons_val, chipFour,
        thirdChain] at h ⊢;
      first | exact h | exact h.symm
  have hShift : (d.length (midTwo center) = 0 ∧
      d.length (armFour center) < d.length (armThree center)) →
      d.rep (thirdChain center) = d.rep (secondChain center) := by
    intro hZero
    have h := d.rep_zero (midTwo center) hZero.1
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, midTwo, Matrix.cons_val, thirdChain,
        Fin.reduceFinMk, secondChain] at h ⊢;
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
  rw [hConditional _ _ _ hOne, hConditional _ _ _ hTwo,
    hConditional _ _ _ hThree, hConditional _ _ _ hFour,
    hConditional _ _ _ hShift]
  simp

/-! ## Which vertex of the centre's class carries the delivered chip -/

def targetOwner (d : DegSpec 8 12) (center : Fin 8) : Fin 8 :=
  if IsEndCenter center then
    (if d.length (midOne center) = 0 ∧ endMid d center < armMin d center then
      secondChain center else firstChain center)
  else
    (if d.length (midOne center) = 0 ∧ midLow d center = armMin d center then
      firstChain center else secondChain center)

theorem targetOwner_rep_eq_center
    (d : DegSpec 8 12) (hCore : d.core = row03Core) (center : Fin 8)
    (hCenter : IsBaseCenter center) :
    d.rep (targetOwner d center) = d.rep center := by
  unfold targetOwner
  split_ifs with hEnd hSide hSide
  · have h := d.rep_zero (midOne center) hSide.1
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, midOne, Fin.reduceFinMk, Matrix.cons_val,
        IsEndCenter, Fin.reduceEq, or_false, secondChain, or_self] at h hEnd ⊢<;>
      first | exact h | exact h.symm
  · fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals simp [firstChain, IsEndCenter] at hEnd ⊢
  · have h := d.rep_zero (midOne center) hSide.1
    fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals
      simp only [hCore, row03Core, Fin.isValue, midOne, Fin.reduceFinMk, Matrix.cons_val,
        IsEndCenter, Fin.reduceEq, or_false, not_true_eq_false, or_self, not_false_eq_true,
        firstChain] at h hEnd ⊢<;>
      exact h
  · fin_cases center <;> simp [IsBaseCenter] at hCenter
    all_goals simp [secondChain, IsEndCenter] at hEnd ⊢

/-! ## Endpoint accounting on the contracted face -/

abbrev endpointContribution := @ConfigurationCommon.endpointContribution 8 12
abbrev endpointPair := @ConfigurationCommon.endpointPair 8 12

theorem positiveEndpointContribution_eq_heightForm
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row03Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center) (v : Fin 8) :
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
    exact firingPotential_eq_raw d F hRepReach hFZero hCenter w
  rw [hp]
  unfold positiveEndpointContribution tailContribution headContribution
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · simp [hZero]
  · have hRise : d.coreRise (rawPotential d center) e =
        (rawHeight d center (d.core.tail e) : ℤ) -
          (rawHeight d center (d.core.head e) : ℤ) := by
      unfold DegSpec.coreRise rawPotential
      ring
    simp [hZero, hRise]

/-! ## The per-vertex coefficient of the local residual -/

def chainCoefficient (d : DegSpec 8 12) (center v : Fin 8) : ℤ :=
  if v = firstChain center then
    zeroChip (d.length (armOne center)) + zeroChip (d.length (armTwo center)) +
      ((armOneLedger center).tail (d.length (armOne center))
          (firstHeight d center) (baseHeight d center) +
        tailContribution (d.length (armTwo center)) (firstHeight d center)
          (baseHeight d center) +
        tailContribution (d.length (midOne center)) (firstHeight d center)
          (secondHeight d center))
  else if v = secondChain center then
    zeroChip (d.length (armThree center)) + shiftWeight d center +
      (headContribution (d.length (midOne center)) (firstHeight d center)
          (secondHeight d center) +
        tailContribution (d.length (armThree center)) (secondHeight d center)
          0 +
        (midTwoLedger center).tail (d.length (midTwo center))
          (secondHeight d center) (baseHeight d center))
  else if v = thirdChain center then
    zeroChip (d.length (armFour center)) - shiftWeight d center +
      ((midTwoLedger center).head (d.length (midTwo center))
          (secondHeight d center) (baseHeight d center) +
        tailContribution (d.length (armFour center)) (baseHeight d center) 0)
  else if v = chipOne center then
    positiveChip (d.length (armOne center)) +
      (armOneLedger center).head (d.length (armOne center))
        (firstHeight d center) (baseHeight d center)
  else if v = chipTwo center then
    positiveChip (d.length (armTwo center)) +
      headContribution (d.length (armTwo center)) (firstHeight d center)
        (baseHeight d center)
  else if v = chipThree center then
    positiveChip (d.length (armThree center)) +
      headContribution (d.length (armThree center)) (secondHeight d center) 0
  else if v = chipFour center then
    positiveChip (d.length (armFour center)) +
      headContribution (d.length (armFour center)) (baseHeight d center) 0
  else 0

/-- The tables that the `simp` normalisation of `chainCoefficient_eq` needs. -/
theorem chainCoefficient_eq
    (d : DegSpec 8 12) (hCore : d.core = row03Core) (center v : Fin 8)
    (hCenter : IsBaseCenter center) :
    allocatedWeight d center v +
        ∑ edge : Fin 12,
          ((if d.core.tail edge = v then
              tailContribution (d.length edge)
                (rawHeight d center (d.core.tail edge))
                (rawHeight d center (d.core.head edge)) else 0) +
          (if d.core.head edge = v then
              headContribution (d.length edge)
                (rawHeight d center (d.core.tail edge))
                (rawHeight d center (d.core.head edge)) else 0)) =
      chainCoefficient d center v := by
  fin_cases center <;> simp [IsBaseCenter] at hCenter
  all_goals fin_cases v
  all_goals
    simp [chainCoefficient, allocatedWeight, transferWeight, indicatorWeight,
      chipWeight, IsChipVertex, shiftWeight, rawHeight, firstChain,
      secondChain, thirdChain, chipOne, chipTwo, chipThree, chipFour,
      armOne, armTwo, midOne, armThree, midTwo, armFour, armOneLedger,
      midTwoLedger, ConfigurationThreeChain.forward, ConfigurationThreeChain.reverse,
      positiveChip, zeroChip, hCore, row03Core, Fin.sum_univ_succ]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals ring

/-! ## The four local readings

Centres `2` and `3` read their picture at the end of the chain, centres `6`
and `7` in the middle.  The two pictures differ only in the orientation of
`armOne` (always into the chain) and of `midTwo` (out of the second chain
vertex on `G`, into it on `G'`). -/

theorem chainResidual_nonneg_center2 (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ chainCoefficient d 2 v - indicatorWeight v (targetOwner d 2) := by
  have hm : armMin d 2 = min (d.length 0) (d.length 1) := rfl
  have hb : baseHeight d 2 = min (d.length 8) (d.length 6) := rfl
  have hmid : endMid d 2 = min (d.length 11)
      (min (d.length 6 - baseHeight d 2) (armMin d 2)) := rfl
  have htop : endTop d 2 =
      min (d.length 5) (armMin d 2 - endMid d 2) := rfl
  have hi : secondHeight d 2 = baseHeight d 2 + endMid d 2 := by
    unfold secondHeight
    rw [if_pos (show IsEndCenter 2 by decide)]
  have ho : firstHeight d 2 = secondHeight d 2 + endTop d 2 := by
    unfold firstHeight
    rw [if_pos (show IsEndCenter 2 by decide), hi]
  have hbo : baseHeight d 2 ≤ firstHeight d 2 := by omega
  have hleafA : firstHeight d 2 ≤ baseHeight d 2 + d.length 0 := by omega
  have hleafB : firstHeight d 2 ≤ baseHeight d 2 + d.length 1 := by omega
  have hbi : baseHeight d 2 ≤ secondHeight d 2 := by omega
  have hit : secondHeight d 2 ≤ baseHeight d 2 + d.length 11 := by omega
  have hfull : secondHeight d 2 = baseHeight d 2 ∨
      baseHeight d 2 = d.length 8 := by omega
  have hleaf3 : secondHeight d 2 ≤ 0 + d.length 6 := by omega
  have hleaf4 : baseHeight d 2 ≤ 0 + d.length 8 := by omega
  have hshift : shiftWeight d 2 =
      if d.length 11 = 0 ∧ d.length 8 < d.length 6 then 1 else 0 := rfl
  have hOwner : targetOwner d 2 =
      if d.length 5 = 0 ∧ endMid d 2 < armMin d 2 then 6 else 2 := rfl
  have hkFirst : indicatorWeight (2 : Fin 8) (targetOwner d 2) =
      if d.length 5 = 0 ∧ endMid d 2 < armMin d 2 then 0 else 1 := by
    by_cases hC : d.length 5 = 0 ∧ endMid d 2 < armMin d 2 <;> simp [indicatorWeight, hOwner, hC]
  have hkSecond : indicatorWeight (6 : Fin 8) (targetOwner d 2) =
      if d.length 5 = 0 ∧ endMid d 2 < armMin d 2 then 1 else 0 := by
    by_cases hC : d.length 5 = 0 ∧ endMid d 2 < armMin d 2 <;> simp [indicatorWeight, hOwner, hC]
  have hkOff : ∀ w : Fin 8, w ≠ 2 → w ≠ 6 →
      indicatorWeight w (targetOwner d 2) = 0 := by
    intro w h1 h2
    by_cases hC : d.length 5 = 0 ∧ endMid d 2 < armMin d 2 <;> simp [indicatorWeight, hOwner, hC, h1, h2]
  clear hOwner
  fin_cases v
  · show (0:ℤ) ≤ chainCoefficient d 2 0 -
        indicatorWeight (0 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 0 = positiveChip (d.length 0) +
        (armOneLedger 2).head (d.length 0) (firstHeight d 2)
          (baseHeight d 2) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 0 (by decide) (by decide)]
    have h := leaf_nonneg (armOneLedger 2) (L := d.length 0)
      (hu := firstHeight d 2) (hv := baseHeight d 2) hbo hleafA
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 1 -
        indicatorWeight (1 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 1 = positiveChip (d.length 1) +
        headContribution (d.length 1) (firstHeight d 2)
          (baseHeight d 2) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 1 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 1)
      (hu := firstHeight d 2) (hv := baseHeight d 2) hbo hleafB
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 2 -
        indicatorWeight (2 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 2 =
        zeroChip (d.length 0) + zeroChip (d.length 1) +
          ((armOneLedger 2).tail (d.length 0) (firstHeight d 2)
              (baseHeight d 2) +
            tailContribution (d.length 1) (firstHeight d 2)
              (baseHeight d 2) +
            tailContribution (d.length 5) (firstHeight d 2)
              (secondHeight d 2)) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkFirst]
    have h := endCenter_first_nonneg (armOneLedger 2)
      (la := d.length 0) (lb := d.length 1) (c := d.length 5) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (m := armMin d 2)
      (b := baseHeight d 2)
      (mid := endMid d 2) (top := endTop d 2)
      (i := secondHeight d 2) (o := firstHeight d 2)
      (if d.length 5 = 0 ∧ endMid d 2 < armMin d 2 then 0 else 1)
      hm hb hmid htop hi ho
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hC : d.length 5 = 0 ∧ endMid d 2 < armMin d 2
        · rw [if_pos hC] at hk; norm_num at hk
        · by_cases hz : d.length 5 = 0
          · exact Or.inr (by omega)
          · exact Or.inl hz)
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 3 -
        indicatorWeight (3 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 3 = 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 3 (by decide) (by decide)]
    norm_num
  · show (0:ℤ) ≤ chainCoefficient d 2 4 -
        indicatorWeight (4 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 4 = positiveChip (d.length 6) +
        headContribution (d.length 6) (secondHeight d 2) 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 4 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 6)
      (hu := secondHeight d 2) (hv := 0) (Nat.zero_le _) hleaf3
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 5 -
        indicatorWeight (5 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 5 = positiveChip (d.length 8) +
        headContribution (d.length 8) (baseHeight d 2) 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 5 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 8)
      (hu := baseHeight d 2) (hv := 0) (Nat.zero_le _) hleaf4
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 6 -
        indicatorWeight (6 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 6 =
        zeroChip (d.length 6) + shiftWeight d 2 +
          (headContribution (d.length 5) (firstHeight d 2)
              (secondHeight d 2) +
            tailContribution (d.length 6) (secondHeight d 2) 0 +
            (midTwoLedger 2).tail (d.length 11) (secondHeight d 2)
              (baseHeight d 2)) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkSecond]
    have h := endCenter_second_nonneg (midTwoLedger 2)
      (la := d.length 0) (lb := d.length 1) (c := d.length 5) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (m := armMin d 2)
      (b := baseHeight d 2)
      (mid := endMid d 2) (top := endTop d 2)
      (i := secondHeight d 2) (o := firstHeight d 2)
      (if d.length 5 = 0 ∧ endMid d 2 < armMin d 2 then 1 else 0) (shiftWeight d 2)
      hm hb hmid htop hi ho hshift
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hC : d.length 5 = 0 ∧ endMid d 2 < armMin d 2
        · exact ⟨hC.1, hC.2⟩
        · rw [if_neg hC] at hk; norm_num at hk)
    omega
  · show (0:ℤ) ≤ chainCoefficient d 2 7 -
        indicatorWeight (7 : Fin 8) (targetOwner d 2)
    have hc : chainCoefficient d 2 7 =
        zeroChip (d.length 8) - shiftWeight d 2 +
          ((midTwoLedger 2).head (d.length 11) (secondHeight d 2)
              (baseHeight d 2) +
            tailContribution (d.length 8) (baseHeight d 2) 0) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 7 (by decide) (by decide)]
    have h := third_nonneg (midTwoLedger 2) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (b := baseHeight d 2)
      (i := secondHeight d 2) (shiftWeight d 2) hb hbi hit
      hfull hshift
    omega

theorem chainResidual_nonneg_center6 (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ chainCoefficient d 6 v - indicatorWeight v (targetOwner d 6) := by
  have hm : armMin d 6 = min (d.length 0) (d.length 1) := rfl
  have hb : baseHeight d 6 = min (d.length 8) (d.length 6) := rfl
  have hlow : midLow d 6 = min (armMin d 6)
      (min (d.length 11) (d.length 6 - baseHeight d 6)) := rfl
  have hhigh : midHigh d 6 = min (d.length 5)
      (min (d.length 11 - midLow d 6)
        (d.length 6 - baseHeight d 6 - midLow d 6)) := rfl
  have ho : firstHeight d 6 = baseHeight d 6 + midLow d 6 := by
    unfold firstHeight
    rw [if_neg (show ¬ IsEndCenter 6 by decide)]
  have hi : secondHeight d 6 = firstHeight d 6 + midHigh d 6 := by
    unfold secondHeight
    rw [if_neg (show ¬ IsEndCenter 6 by decide), ho]
  have hbo : baseHeight d 6 ≤ firstHeight d 6 := by omega
  have hleafA : firstHeight d 6 ≤ baseHeight d 6 + d.length 0 := by omega
  have hleafB : firstHeight d 6 ≤ baseHeight d 6 + d.length 1 := by omega
  have hbi : baseHeight d 6 ≤ secondHeight d 6 := by omega
  have hit : secondHeight d 6 ≤ baseHeight d 6 + d.length 11 := by omega
  have hfull : secondHeight d 6 = baseHeight d 6 ∨
      baseHeight d 6 = d.length 8 := by omega
  have hleaf3 : secondHeight d 6 ≤ 0 + d.length 6 := by omega
  have hleaf4 : baseHeight d 6 ≤ 0 + d.length 8 := by omega
  have hshift : shiftWeight d 6 =
      if d.length 11 = 0 ∧ d.length 8 < d.length 6 then 1 else 0 := rfl
  have hOwner : targetOwner d 6 =
      if d.length 5 = 0 ∧ midLow d 6 = armMin d 6 then 2 else 6 := rfl
  have hkFirst : indicatorWeight (2 : Fin 8) (targetOwner d 6) =
      if d.length 5 = 0 ∧ midLow d 6 = armMin d 6 then 1 else 0 := by
    by_cases hC : d.length 5 = 0 ∧ midLow d 6 = armMin d 6 <;> simp [indicatorWeight, hOwner, hC]
  have hkSecond : indicatorWeight (6 : Fin 8) (targetOwner d 6) =
      if d.length 5 = 0 ∧ midLow d 6 = armMin d 6 then 0 else 1 := by
    by_cases hC : d.length 5 = 0 ∧ midLow d 6 = armMin d 6 <;> simp [indicatorWeight, hOwner, hC]
  have hkOff : ∀ w : Fin 8, w ≠ 2 → w ≠ 6 →
      indicatorWeight w (targetOwner d 6) = 0 := by
    intro w h1 h2
    by_cases hC : d.length 5 = 0 ∧ midLow d 6 = armMin d 6 <;> simp [indicatorWeight, hOwner, hC, h1, h2]
  clear hOwner
  fin_cases v
  · show (0:ℤ) ≤ chainCoefficient d 6 0 -
        indicatorWeight (0 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 0 = positiveChip (d.length 0) +
        (armOneLedger 6).head (d.length 0) (firstHeight d 6)
          (baseHeight d 6) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 0 (by decide) (by decide)]
    have h := leaf_nonneg (armOneLedger 6) (L := d.length 0)
      (hu := firstHeight d 6) (hv := baseHeight d 6) hbo hleafA
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 1 -
        indicatorWeight (1 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 1 = positiveChip (d.length 1) +
        headContribution (d.length 1) (firstHeight d 6)
          (baseHeight d 6) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 1 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 1)
      (hu := firstHeight d 6) (hv := baseHeight d 6) hbo hleafB
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 2 -
        indicatorWeight (2 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 2 =
        zeroChip (d.length 0) + zeroChip (d.length 1) +
          ((armOneLedger 6).tail (d.length 0) (firstHeight d 6)
              (baseHeight d 6) +
            tailContribution (d.length 1) (firstHeight d 6)
              (baseHeight d 6) +
            tailContribution (d.length 5) (firstHeight d 6)
              (secondHeight d 6)) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkFirst]
    have h := midCenter_first_nonneg (armOneLedger 6)
      (la := d.length 0) (lb := d.length 1) (c := d.length 5) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (m := armMin d 6)
      (b := baseHeight d 6)
      (low := midLow d 6) (high := midHigh d 6)
      (i := secondHeight d 6) (o := firstHeight d 6)
      (if d.length 5 = 0 ∧ midLow d 6 = armMin d 6 then 1 else 0)
      hm hb hlow hhigh ho hi
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hC : d.length 5 = 0 ∧ midLow d 6 = armMin d 6
        · exact ⟨hC.1, hC.2⟩
        · rw [if_neg hC] at hk; norm_num at hk)
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 3 -
        indicatorWeight (3 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 3 = 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 3 (by decide) (by decide)]
    norm_num
  · show (0:ℤ) ≤ chainCoefficient d 6 4 -
        indicatorWeight (4 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 4 = positiveChip (d.length 6) +
        headContribution (d.length 6) (secondHeight d 6) 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 4 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 6)
      (hu := secondHeight d 6) (hv := 0) (Nat.zero_le _) hleaf3
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 5 -
        indicatorWeight (5 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 5 = positiveChip (d.length 8) +
        headContribution (d.length 8) (baseHeight d 6) 0 := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 5 (by decide) (by decide)]
    have h := leaf_head_nonneg (L := d.length 8)
      (hu := baseHeight d 6) (hv := 0) (Nat.zero_le _) hleaf4
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 6 -
        indicatorWeight (6 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 6 =
        zeroChip (d.length 6) + shiftWeight d 6 +
          (headContribution (d.length 5) (firstHeight d 6)
              (secondHeight d 6) +
            tailContribution (d.length 6) (secondHeight d 6) 0 +
            (midTwoLedger 6).tail (d.length 11) (secondHeight d 6)
              (baseHeight d 6)) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkSecond]
    have h := midCenter_second_nonneg (midTwoLedger 6)
      (la := d.length 0) (lb := d.length 1) (c := d.length 5) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (m := armMin d 6)
      (b := baseHeight d 6)
      (low := midLow d 6) (high := midHigh d 6)
      (i := secondHeight d 6) (o := firstHeight d 6)
      (if d.length 5 = 0 ∧ midLow d 6 = armMin d 6 then 0 else 1) (shiftWeight d 6)
      hm hb hlow hhigh ho hi hshift
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hC : d.length 5 = 0 ∧ midLow d 6 = armMin d 6
        · rw [if_pos hC] at hk; norm_num at hk
        · by_cases hz : d.length 5 = 0
          · exact Or.inr (by omega)
          · exact Or.inl hz)
    omega
  · show (0:ℤ) ≤ chainCoefficient d 6 7 -
        indicatorWeight (7 : Fin 8) (targetOwner d 6)
    have hc : chainCoefficient d 6 7 =
        zeroChip (d.length 8) - shiftWeight d 6 +
          ((midTwoLedger 6).head (d.length 11) (secondHeight d 6)
              (baseHeight d 6) +
            tailContribution (d.length 8) (baseHeight d 6) 0) := by
      simp +decide only [chainCoefficient,
        armOne, armTwo, midOne,
        armThree, midTwo, armFour, reduceIte]
    rw [hc, hkOff 7 (by decide) (by decide)]
    have h := third_nonneg (midTwoLedger 6) (s := d.length 6)
      (t := d.length 11) (u := d.length 8) (b := baseHeight d 6)
      (i := secondHeight d 6) (shiftWeight d 6) hb hbi hit
      hfull hshift
    omega

/-! ## From the four local readings to the degree-four pencil -/

theorem chainResidual_nonneg (d : DegSpec 8 12) {center : Fin 8}
    (hCenter : IsBaseCenter center) (v : Fin 8) :
    0 ≤ chainCoefficient d center v -
      indicatorWeight v (targetOwner d center) := by
  rcases hCenter with rfl | rfl
  · exact chainResidual_nonneg_center2 d v
  · exact chainResidual_nonneg_center6 d v

theorem localResidual_nonneg
    (d : DegSpec 8 12) (hCore : d.core = row03Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row03Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {center : Fin 8} (hCenter : IsBaseCenter center) (v : Fin 8) :
    0 ≤ allocatedWeight d center v -
        indicatorWeight v (targetOwner d center) +
      positiveEndpointContribution d (firingPotential d center) v := by
  rw [positiveEndpointContribution_eq_heightForm d F hRepReach hFZero hCenter v]
  have hEq := chainCoefficient_eq d hCore center v hCenter
  have hRes := chainResidual_nonneg d hCenter v
  omega

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]

theorem residual_effective
    (d : DegSpec 8 12) (hCore : d.core = row03Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row03Core F x y)
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
    rw [← allocated_class_sum_eq d hCore center r hCenter]
    rw [← positiveEndpointContribution_classSum_eq d potential hInv r]
    have hOwner := targetOwner_rep_eq_center d hCore center hCenter
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


/-! ## The symmetry that exchanges the two pictures

Row 03's chip weight `{0, 1, 4, 5}` is fixed by a group of order two, so the
chip-free vertices fall into the two orbits `{2, 3}` and `{6, 7}`: one reading
at the end of the chain and one in the middle.  The module docstring already
named the map — `(2 3)(6 7)(4 5)` — and called `G'` the image of `G` under it.
That sentence is now the proof.

The literal carries its own inverse.  `ClosedOrbit.targetLength` is
`fun e => length (slotPerm.symm e)`, and `Equiv.symm` of an
`Equiv.ofBijective` does not reduce in the kernel; see the module docstring of
`LowGenus/GuardingOrbit.lean`. -/

/-- The identity. -/
def blockSym0 : CoreSymmetry row03Core :=
  CoreSymmetry.ofInverses row03Core
    (vertexTable [0, 1, 2, 3, 4, 5, 6, 7]) (vertexTable [0, 1, 2, 3, 4, 5, 6, 7])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(2 3)(4 5)(6 7)`, the automorphism of the module docstring.  Carries the
end centre `2` to `3` and the middle centre `6` to `7`. -/
def swap : CoreSymmetry row03Core :=
  CoreSymmetry.ofInverses row03Core
    (vertexTable [0, 1, 3, 2, 5, 4, 7, 6]) (vertexTable [0, 1, 3, 2, 5, 4, 7, 6])
    (slotTable [2, 3, 0, 1, 4, 7, 8, 5, 6, 9, 10, 11])
    (slotTable [2, 3, 0, 1, 4, 7, 8, 5, 6, 9, 10, 11])
    (flagTable [false, false, false, false, false, false, false, false, false,
      true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The base centre of each chip-free vertex's orbit. -/
def base : Fin 8 → Fin 8 := fun v =>
  if v = 3 then 2 else if v = 7 then 6 else v

/-- The symmetry carrying `base v` to `v`. -/
def mover : Fin 8 → CoreSymmetry row03Core := fun v =>
  if v = 3 then swap else if v = 7 then swap else blockSym0

/-! ## The orbit guard -/

/-- **Row 03 as an orbit guard.**  Chips on `0, 1, 4, 5`; the chip-free
three-chain read once at its end (`2`) and once in its middle (`6`), each moved
to its `swap` image.  The closing step is
`Guarding.OrbitGuard.closedConstruction` -- no row-specific rank transport, no
hand-rolled pencil. -/
def row03Orbit : OrbitGuard row03Core (by norm_num) 4 where
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
        (fun x y => compFold_iff row03Core (zeroSlots length) x y)
        (mem_zeroSlots length) hBase)).reaches

/-- The AR construction on row 03, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row03_closedConstruction :
    ClosedSubdivisionDharConstruction row03Core (by norm_num) :=
  row03Orbit.closedConstruction row03_connected

end AtanasovRanganathan.GenusFiveRow03