import LowGenus.ClosedConstructionTail
import LowGenus.ConfigurationMarkedRow
import LowGenus.ConfigurationReservoirChain
import LowGenus.ConfigurationReservoirPair
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 02

Row 02 is AR's *second family*, and one of the two families they single out for
a separate "edge contraction" treatment.  Its core is three bananas glued to two
trivalent hubs,

```
 e0      : 0 -> 1     a9 -- b9        e5      : 6 -> 7     e9 -- f9
 e1      : 1 -> 2     b9 -- c9        e6, e7  : 7 -> 0     f9 == a9   banana B3
 e2      : 2 -> 5     c9 -- d9        e8      : 1 -> 3     b9 -- b9a
 e3, e4  : 5 -> 6     d9 == e9  B2    e9      : 2 -> 4     c9 -- c9a
                                      e10,e11 : 3 -> 4     b9a == c9a banana B1
```

so contracting `B1 = {3,4}`, `B2 = {5,6}` and `B3 = {7,0}` leaves the theta
graph on the hubs `1`, `2` with routes `e1`, `e8·e9` and `e0·e5·e2`.

The formalization uses the following core-supported divisor:

```
 D = [0] + [1] + [2] + [5]
```

It has degree four and is valid on the *whole* closed nonloopy forest
orthant: one chamber, no interior chip, no marks, no symmetry transport.  The
exceptional face `|e5| = 0` is covered by the very same four scripts, with no
case branch and no separate boundary divisor.

Its four chip-free vertices fall into two local pictures, both new, and both
turning on the **reservoir**: a paying chip backed by a second chip one slot
behind it can pay two units.

* `{3, 4}` -- `ConfigurationReservoirPair`: the banana `B1` hanging off the two
  hubs `1`, `2`, each of which is refilled, `1` from the chip at `0` across
  `|e0|` and `2` from the chip at `5` across `|e2|` (or from each other across
  `|e1|`).  Read at the target `4` with `alpha = |e0|`, `l = |e1|`,
  `beta = |e2|`, `p = |e8|`, `q = |e9|`, and at the target `3` with
  `alpha <-> beta`, `p <-> q`.
* `{6, 7}` -- `ConfigurationReservoirChain`: the two bananas `B2`, `B3` in
  series across `e5`, with the chips `5` and `0` on them refilled the same way.
  Read at the target `6` with `alpha = |e0|`, `(n1,n2) = (|e6|,|e7|)`,
  `s = |e5|`, `(m1,m2) = (|e3|,|e4|)`, `beta = |e2|`, and at the target `7` with
  `alpha <-> beta`, `(n1,n2) <-> (m1,m2)`.

Both mirrors are the core automorphism `sigma = (0 5)(1 2)(3 4)(6 7)`; since
there is only one chamber and the orbit machinery transports chambers rather
than targets, the two `sigma` images are written out rather than transported.
The two regions do not interact: in each region's script every vertex of the
other region sits at height `0` and every slot between them carries rise `0`, so
the four chips' ledgers split as `picture + 0`.

Every height is a nested minimum of slot lengths, hence constant across a
collapsed slot, so one script covers the open cell and every nonloopy forest
face at once.  What a collapsed slot *does* cost is an allocation: chips move
inside their contracted class so that the per-vertex ledger, not merely the
class ledger, stays effective.  There are three such moves per picture; the
`{3,4}` picture needs one of them with coefficient **two**, when the arm `1-3`
collapses while the banana still carries a rise.

The endpoint plumbing is `ConfigurationMarkedRow`'s, instantiated at the
identically-zero mark `noMark`, which recovers the ordinary one-ramp script
definitionally; no slot of row 02 carries a chip in its interior.
-/

namespace AtanasovRanganathan.GenusFiveRow02

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
open ConfigurationMarkedThree
open ConfigurationMarkedRow

/-! ## No marks

Row 02's divisor is core supported, so every slot is an ordinary single ramp.
Passing the identically-zero mark through `ConfigurationMarkedRow` recovers
exactly that, and buys the whole residual-effectivity wrapper unchanged. -/

/-- The zero mark: no slot of row 02 carries an interior chip. -/
def noMark : Fin 12 → ℕ := fun _ => 0

@[simp] theorem noMark_apply (e : Fin 12) : noMark e = 0 := rfl

/-- A height profile with no marks needs only class constancy. -/
theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row02Core)
    {h : Fin 8 → ℕ}
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row02Core.tail e) = h (row02Core.head e)) :
    Profile d noMark h := by
  refine ⟨fun e => Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he
    rw [hCore]
    exact hconst e he

/-! ## The divisor -/

/-- `D = [0] + [1] + [2] + [5]`. -/
def chipWeight (v : Fin 8) : ℤ :=
  if v = 0 then 1 else if v = 1 then 1 else if v = 2 then 1
    else if v = 5 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph := d.coreClassDivisor chipWeight

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]

theorem rowDivisor_coreVertex (d : DegSpec 8 12) (r : Fin 8) :
    rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v :=
  d.coreClassDivisor_coreVertex chipWeight r

/-! ## The three banana minima -/

/-- `min |e10| |e11|`, the top banana `B1 = {3,4}`. -/
def parB1 (d : DegSpec 8 12) : ℕ := min (d.length 10) (d.length 11)

/-- `min |e3| |e4|`, the right banana `B2 = {5,6}`. -/
def parB2 (d : DegSpec 8 12) : ℕ := min (d.length 3) (d.length 4)

/-- `min |e6| |e7|`, the left banana `B3 = {7,0}`. -/
def parB3 (d : DegSpec 8 12) : ℕ := min (d.length 6) (d.length 7)

/-! ## The nested-min heights

Four readings, all four verbatim from
auxiliary calculations §3.4. -/

/-- The reservoir pair at the target `4`: `A1 = 0`, `A = 1`, `B = 2`,
`B1 = 5`, `X = 3`, `Y = 4`. -/
def hB4 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirPair.restHeight (d.length 0) (d.length 2)

def hA4 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirPair.workHeight (d.length 0) (d.length 2) (d.length 1)
    (d.length 9)

def hX4 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirPair.hubHeight (d.length 0) (d.length 2) (d.length 1)
    (d.length 8) (d.length 9)

def hY4 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirPair.targetHeight (d.length 0) (d.length 2) (d.length 1)
    (d.length 8) (d.length 9) (parB1 d)

/-- The reservoir chain at the target `6`: `A1 = 1`, `A = 0`, `P = 7`,
`Q = 6`, `B = 5`, `B1 = 2`. -/
def hQ6 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.targetHeight (d.length 0) (d.length 2)
    (d.length 5) (parB2 d) (parB3 d)

def hP6 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.partnerHeight (d.length 0) (d.length 2)
    (d.length 5) (parB2 d) (parB3 d)

def hA6 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.nearHeight (d.length 0) (d.length 2)
    (d.length 5) (parB2 d) (parB3 d)

def hB6 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.farHeight (d.length 0) (d.length 2)
    (d.length 5) (parB2 d) (parB3 d)

/-! ## The four bound bundles -/

theorem boundsT4 (d : DegSpec 8 12) :
    (hB4 d ≤ d.length 0 ∧ hB4 d ≤ d.length 2)
      ∧ (hB4 d = d.length 0 ∨ hB4 d = d.length 2)
      ∧ (hA4 d ≤ d.length 0 ∧ hA4 d ≤ hB4 d + d.length 1
          ∧ hA4 d ≤ hB4 d + d.length 9 ∧ hB4 d ≤ hA4 d)
      ∧ (hA4 d = d.length 0 ∨ hA4 d = hB4 d + d.length 1
          ∨ hA4 d = hB4 d + d.length 9)
      ∧ (hX4 d ≤ hB4 d + d.length 9 ∧ hX4 d ≤ hA4 d + 2 * d.length 8
          ∧ hA4 d ≤ hX4 d)
      ∧ (hX4 d = hB4 d + d.length 9 ∨ hX4 d = hA4 d + 2 * d.length 8)
      ∧ (hY4 d ≤ hB4 d + d.length 9 ∧ hY4 d ≤ hX4 d + parB1 d ∧ hX4 d ≤ hY4 d)
      ∧ (hY4 d = hB4 d + d.length 9 ∨ hY4 d = hX4 d + parB1 d) :=
  ConfigurationReservoirPair.bounds rfl rfl rfl rfl

theorem boundsT6 (d : DegSpec 8 12) :
    (hQ6 d ≤ d.length 2 + parB2 d ∧ hQ6 d ≤ d.length 0 + parB3 d + d.length 5)
      ∧ (hQ6 d = d.length 2 + parB2 d
          ∨ hQ6 d = d.length 0 + parB3 d + d.length 5)
      ∧ (hP6 d ≤ d.length 0 + parB3 d ∧ hP6 d ≤ hQ6 d)
      ∧ (hP6 d = d.length 0 + parB3 d ∨ hP6 d = hQ6 d)
      ∧ (hA6 d ≤ d.length 0 ∧ hA6 d ≤ hP6 d) ∧ (hA6 d = d.length 0 ∨ hA6 d = hP6 d)
      ∧ (hB6 d ≤ d.length 2 ∧ hB6 d ≤ hQ6 d) ∧ (hB6 d = d.length 2 ∨ hB6 d = hQ6 d)
      ∧ (hA6 d ≤ hP6 d ∧ hP6 d ≤ hQ6 d ∧ hB6 d ≤ hQ6 d
          ∧ hP6 d ≤ hA6 d + parB3 d ∧ hQ6 d ≤ hB6 d + parB2 d
          ∧ hQ6 d ≤ hP6 d + d.length 5) :=
  ConfigurationReservoirChain.bounds rfl rfl rfl rfl

/-! ## The four height vectors -/

/-- The reservoir pair read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 1 then hA4 d else if v = 2 then hB4 d else if v = 3 then hX4 d
    else if v = 4 then hY4 d else 0

/-- The reservoir chain read at the target `6`. -/
def heightT6 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then hA6 d else if v = 5 then hB6 d else if v = 6 then hQ6 d
    else if v = 7 then hP6 d else 0

theorem profileT4 {d : DegSpec 8 12} (hCore : d.core = row02Core) :
    Profile d noMark (heightT4 d) := by
  have hb := boundsT4 d
  have hpar : parB1 d = min (d.length 10) (d.length 11) := rfl
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT4, row02Core]
  all_goals omega

theorem profileT6 {d : DegSpec 8 12} (hCore : d.core = row02Core) :
    Profile d noMark (heightT6 d) := by
  have hb := boundsT6 d
  have hp2 : parB2 d = min (d.length 3) (d.length 4) := rfl
  have hp3 : parB3 d = min (d.length 6) (d.length 7) := rfl
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT6, row02Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex

Each of the eight core vertices is trivalent, so `contribForm` has three terms
per vertex; they are the twenty-four slot ends of row 02 sorted by vertex. -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 6) (h 7) (h 0)
      + headContribution (d.length 7) (h 7) (h 0)
  else if v = 1 then
    tailContribution (d.length 1) (h 1) (h 2)
      + tailContribution (d.length 8) (h 1) (h 3)
      + headContribution (d.length 0) (h 0) (h 1)
  else if v = 2 then
    tailContribution (d.length 2) (h 2) (h 5)
      + tailContribution (d.length 9) (h 2) (h 4)
      + headContribution (d.length 1) (h 1) (h 2)
  else if v = 3 then
    tailContribution (d.length 10) (h 3) (h 4)
      + tailContribution (d.length 11) (h 3) (h 4)
      + headContribution (d.length 8) (h 1) (h 3)
  else if v = 4 then
    headContribution (d.length 9) (h 2) (h 4)
      + headContribution (d.length 10) (h 3) (h 4)
      + headContribution (d.length 11) (h 3) (h 4)
  else if v = 5 then
    tailContribution (d.length 3) (h 5) (h 6)
      + tailContribution (d.length 4) (h 5) (h 6)
      + headContribution (d.length 2) (h 2) (h 5)
  else if v = 6 then
    tailContribution (d.length 5) (h 6) (h 7)
      + headContribution (d.length 3) (h 5) (h 6)
      + headContribution (d.length 4) (h 5) (h 6)
  else
    tailContribution (d.length 6) (h 7) (h 0)
      + tailContribution (d.length 7) (h 7) (h 0)
      + headContribution (d.length 5) (h 6) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row02Core)
    {h : Fin 8 → ℕ} (hprof : Profile d noMark h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) noMark
        (markValue d noMark h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row02Core, Fin.isValue, Fin.zero_eta, slotTailForm, noMark,
      lt_self_iff_false, ↓reduceIte, slotHeadForm, Fin.sum_univ_succ, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      zero_add, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Fin.reduceEq,
      Finset.sum_const_zero, contribForm, Fin.mk_one, Fin.reduceFinMk, Finset.sum_singleton]<;>
    ring

/-! ## Which core vertices a collapsed slot identifies -/

section Rep

variable {d : DegSpec 8 12} (hCore : d.core = row02Core)
include hCore

theorem rep_zero_e0 (hz : d.length 0 = 0) : d.rep 0 = d.rep 1 := by
  have h := d.rep_zero 0 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_e1 (hz : d.length 1 = 0) : d.rep 1 = d.rep 2 := by
  have h := d.rep_zero 1 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_e2 (hz : d.length 2 = 0) : d.rep 2 = d.rep 5 := by
  have h := d.rep_zero 2 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_e5 (hz : d.length 5 = 0) : d.rep 6 = d.rep 7 := by
  have h := d.rep_zero 5 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_e8 (hz : d.length 8 = 0) : d.rep 1 = d.rep 3 := by
  have h := d.rep_zero 8 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_e9 (hz : d.length 9 = 0) : d.rep 2 = d.rep 4 := by
  have h := d.rep_zero 9 hz; rw [hCore] at h; simpa [row02Core] using h

theorem rep_zero_parB1 (hz : parB1 d = 0) : d.rep 3 = d.rep 4 := by
  have hEither : d.length 10 = 0 ∨ d.length 11 = 0 := by
    simpa [parB1, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 10 h; rw [hCore] at hh; simpa [row02Core] using hh
  · have hh := d.rep_zero 11 h; rw [hCore] at hh; simpa [row02Core] using hh

theorem rep_zero_parB2 (hz : parB2 d = 0) : d.rep 5 = d.rep 6 := by
  have hEither : d.length 3 = 0 ∨ d.length 4 = 0 := by
    simpa [parB2, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 3 h; rw [hCore] at hh; simpa [row02Core] using hh
  · have hh := d.rep_zero 4 h; rw [hCore] at hh; simpa [row02Core] using hh

theorem rep_zero_parB3 (hz : parB3 d = 0) : d.rep 7 = d.rep 0 := by
  have hEither : d.length 6 = 0 ∨ d.length 7 = 0 := by
    simpa [parB3, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 6 h; rw [hCore] at hh; simpa [row02Core] using hh
  · have hh := d.rep_zero 7 h; rw [hCore] at hh; simpa [row02Core] using hh

end Rep

/-! ## Chip allocations

Every transfer moves weight *inside* one contracted class, so no class sum --
hence no divisor value -- changes.  The reservoir chips fall into their working
chips' classes when the reservoir arms collapse; the pair picture additionally
lends the resting chip to the working one across a collapsed `e1`, and hands the
hub **two** units across a collapsed arm. -/

/-- The allocation of the reservoir pair read at `4`. -/
def allocT4 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 0 = 0 then transferWeight 0 1 v else 0)
    + (if d.length 2 = 0 then transferWeight 5 2 v else 0)
    + (if d.length 1 = 0 ∧ hB4 d < d.length 0 then transferWeight 2 1 v else 0)
    + (if d.length 8 = 0 ∧ hX4 d < hY4 d then transferWeight 1 3 v else 0)
    + (if d.length 8 = 0 ∧ hX4 d < hY4 d then transferWeight 1 3 v else 0)

/-- The allocation of the reservoir chain read at `6`. -/
def allocT6 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 0 = 0 then transferWeight 1 0 v else 0)
    + (if d.length 2 = 0 then transferWeight 2 5 v else 0)
    + (if parB3 d = 0 ∧ hP6 d < hQ6 d then transferWeight 0 7 v else 0)

theorem allocT4_classSum {d : DegSpec 8 12} (hCore : d.core = row02Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT4 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT4, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 0 1 (rep_zero_e0 hCore),
    sum_conditional_transfer_eq_zero d _ 5 2
      (fun hz => (rep_zero_e2 hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 2 1
      (fun hz => (rep_zero_e1 hCore hz.1).symm),
    sum_conditional_transfer_eq_zero d _ 1 3
      (fun hz => rep_zero_e8 hCore hz.1)]
  simp

theorem allocT6_classSum {d : DegSpec 8 12} (hCore : d.core = row02Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT6 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT6, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 1 0
      (fun hz => (rep_zero_e0 hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 2 5 (rep_zero_e2 hCore),
    sum_conditional_transfer_eq_zero d _ 0 7
      (fun hz => (rep_zero_parB3 hCore hz.1).symm)]
  simp

/-! ## The reservoir pair at the target `4` -/

def t4Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    positiveChip (d.length 0) + tailContribution (d.length 0) 0 (hA4 d)
  else if v = 1 then
    1 + zeroChip (d.length 0)
        + ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
        - 2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
      + (headContribution (d.length 0) 0 (hA4 d)
          + tailContribution (d.length 1) (hA4 d) (hB4 d)
          + tailContribution (d.length 8) (hA4 d) (hX4 d))
  else if v = 2 then
    1 + zeroChip (d.length 2)
        - ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
      + (headContribution (d.length 1) (hA4 d) (hB4 d)
          + tailContribution (d.length 2) (hB4 d) 0
          + tailContribution (d.length 9) (hB4 d) (hY4 d))
  else if v = 3 then
    2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
      + (headContribution (d.length 8) (hA4 d) (hX4 d)
          + tailContribution (d.length 10) (hX4 d) (hY4 d)
          + tailContribution (d.length 11) (hX4 d) (hY4 d))
  else if v = 4 then
    headContribution (d.length 9) (hB4 d) (hY4 d)
      + headContribution (d.length 10) (hX4 d) (hY4 d)
      + headContribution (d.length 11) (hX4 d) (hY4 d)
  else if v = 5 then
    positiveChip (d.length 2) + headContribution (d.length 2) (hB4 d) 0
  else 0

theorem t4Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT4 d v + contribForm d (heightT4 d) v = t4Coeff d v := by
  fin_cases v <;>
    simp [t4Coeff, allocT4, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, ConfigurationReservoirPair.lendFlat,
      ConfigurationReservoirPair.lendHub, contribForm, heightT4]
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem t4Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t4Coeff d v := by
  have hb := boundsT4 d
  have hpar : parB1 d = min (d.length 10) (d.length 11) := rfl
  fin_cases v
  · show (0 : ℤ) ≤ positiveChip (d.length 0)
      + tailContribution (d.length 0) 0 (hA4 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 0)
        + ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
        - 2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
      + (headContribution (d.length 0) 0 (hA4 d)
          + tailContribution (d.length 1) (hA4 d) (hB4 d)
          + tailContribution (d.length 8) (hA4 d) (hX4 d))
    have := ConfigurationReservoirPair.pairWork_nonneg rev fwd
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d) rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 2)
        - ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
      + (headContribution (d.length 1) (hA4 d) (hB4 d)
          + tailContribution (d.length 2) (hB4 d) 0
          + tailContribution (d.length 9) (hB4 d) (hY4 d))
    have := ConfigurationReservoirPair.pairRest_nonneg rev fwd
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d) rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤
      2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
      + (headContribution (d.length 8) (hA4 d) (hX4 d)
          + tailContribution (d.length 10) (hX4 d) (hY4 d)
          + tailContribution (d.length 11) (hX4 d) (hY4 d))
    have := ConfigurationReservoirPair.pairHub_nonneg fwd
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (m1 := d.length 10) (m2 := d.length 11)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail] at this
    omega
  · show (0 : ℤ) ≤ headContribution (d.length 9) (hB4 d) (hY4 d)
      + headContribution (d.length 10) (hX4 d) (hY4 d)
      + headContribution (d.length 11) (hX4 d) (hY4 d)
    have := ConfigurationReservoirPair.pairTarget_nonneg rev
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (m1 := d.length 10) (m2 := d.length 11)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d) rfl rfl rfl rfl rfl
    simp only [rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 2)
      + headContribution (d.length 2) (hB4 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

def ownerFour (d : DegSpec 8 12) : Fin 8 :=
  if ConfigurationReservoirPair.Delivers (d.length 9) (parB1 d) (hB4 d) (hX4 d)
      (hY4 d) then 4
  else if d.length 9 = 0 then 2
  else if 0 < d.length 8 then 3
  else 1

theorem t4Coeff_owner (d : DegSpec 8 12) : 1 ≤ t4Coeff d (ownerFour d) := by
  have hb := boundsT4 d
  have hpar : parB1 d = min (d.length 10) (d.length 11) := rfl
  unfold ownerFour
  by_cases hDel : ConfigurationReservoirPair.Delivers (d.length 9) (parB1 d)
      (hB4 d) (hX4 d) (hY4 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ headContribution (d.length 9) (hB4 d) (hY4 d)
      + headContribution (d.length 10) (hX4 d) (hY4 d)
      + headContribution (d.length 11) (hX4 d) (hY4 d)
    have := ConfigurationReservoirPair.pairTarget_ge_one rev
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (m1 := d.length 10) (m2 := d.length 11)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
      rfl rfl rfl rfl rfl hDel
    simp only [rev_tail] at this
    omega
  · have hcases := ConfigurationReservoirPair.cases_of_not_delivers
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hq : d.length 9 = 0
    · rw [if_pos hq]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 2)
          - ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
        + (headContribution (d.length 1) (hA4 d) (hB4 d)
            + tailContribution (d.length 2) (hB4 d) 0
            + tailContribution (d.length 9) (hB4 d) (hY4 d))
      have := ConfigurationReservoirPair.pairRest_ge_one rev fwd
        (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
        (p := d.length 8) (q := d.length 9) (par := parB1 d)
        (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
        rfl rfl rfl rfl hq
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [if_neg hq]
      by_cases hp : 0 < d.length 8
      · rw [if_pos hp]
        show (1 : ℤ) ≤
          2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
          + (headContribution (d.length 8) (hA4 d) (hX4 d)
              + tailContribution (d.length 10) (hX4 d) (hY4 d)
              + tailContribution (d.length 11) (hX4 d) (hY4 d))
        have := ConfigurationReservoirPair.pairHub_ge_one fwd
          (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
          (p := d.length 8) (q := d.length 9) (par := parB1 d)
          (m1 := d.length 10) (m2 := d.length 11)
          (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
          rfl rfl rfl rfl rfl hp (by omega) (by omega)
        simp only [fwd_tail] at this
        omega
      · rw [if_neg hp]
        show (1 : ℤ) ≤ 1 + zeroChip (d.length 0)
            + ConfigurationReservoirPair.lendFlat (d.length 1) (d.length 0) (hB4 d)
            - 2 * ConfigurationReservoirPair.lendHub (d.length 8) (hX4 d) (hY4 d)
          + (headContribution (d.length 0) 0 (hA4 d)
              + tailContribution (d.length 1) (hA4 d) (hB4 d)
              + tailContribution (d.length 8) (hA4 d) (hX4 d))
        have := ConfigurationReservoirPair.pairWork_ge_one rev fwd
          (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
          (p := d.length 8) (q := d.length 9) (par := parB1 d)
          (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
          rfl rfl rfl rfl (by omega) (by omega)
        simp only [fwd_tail, rev_tail] at this
        omega

theorem ownerFour_rep {d : DegSpec 8 12} (hCore : d.core = row02Core) :
    d.rep (ownerFour d) = d.rep 4 := by
  have hb := boundsT4 d
  have hpar : parB1 d = min (d.length 10) (d.length 11) := rfl
  unfold ownerFour
  by_cases hDel : ConfigurationReservoirPair.Delivers (d.length 9) (parB1 d)
      (hB4 d) (hX4 d) (hY4 d)
  · rw [if_pos hDel]
  · have hcases := ConfigurationReservoirPair.cases_of_not_delivers
      (alpha := d.length 0) (beta := d.length 2) (l := d.length 1)
      (p := d.length 8) (q := d.length 9) (par := parB1 d)
      (hB := hB4 d) (hA := hA4 d) (hX := hX4 d) (hY := hY4 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hq : d.length 9 = 0
    · rw [if_pos hq]
      exact rep_zero_e9 hCore hq
    · rw [if_neg hq]
      have hparZero : parB1 d = 0 := by omega
      by_cases hp : 0 < d.length 8
      · rw [if_pos hp]
        exact rep_zero_parB1 hCore hparZero
      · rw [if_neg hp]
        rw [rep_zero_e8 hCore (by omega)]
        exact rep_zero_parB1 hCore hparZero

/-! ## The reservoir chain at the target `6` -/

def t6Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    1 + zeroChip (d.length 0)
        - ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
      + (tailContribution (d.length 0) (hA6 d) 0
          + headContribution (d.length 6) (hP6 d) (hA6 d)
          + headContribution (d.length 7) (hP6 d) (hA6 d))
  else if v = 1 then
    positiveChip (d.length 0) + headContribution (d.length 0) (hA6 d) 0
  else if v = 2 then
    positiveChip (d.length 2) + tailContribution (d.length 2) 0 (hB6 d)
  else if v = 5 then
    1 + zeroChip (d.length 2)
      + (headContribution (d.length 2) 0 (hB6 d)
          + tailContribution (d.length 3) (hB6 d) (hQ6 d)
          + tailContribution (d.length 4) (hB6 d) (hQ6 d))
  else if v = 6 then
    headContribution (d.length 3) (hB6 d) (hQ6 d)
      + headContribution (d.length 4) (hB6 d) (hQ6 d)
      + tailContribution (d.length 5) (hQ6 d) (hP6 d)
  else if v = 7 then
    ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
      + (tailContribution (d.length 6) (hP6 d) (hA6 d)
          + tailContribution (d.length 7) (hP6 d) (hA6 d)
          + headContribution (d.length 5) (hQ6 d) (hP6 d))
  else 0

theorem t6Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT6 d v + contribForm d (heightT6 d) v = t6Coeff d v := by
  fin_cases v <;>
    simp [t6Coeff, allocT6, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, ConfigurationReservoirChain.lend, contribForm,
      heightT6]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)

theorem t6Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t6Coeff d v := by
  have hb := boundsT6 d
  have hp2 : parB2 d = min (d.length 3) (d.length 4) := rfl
  have hp3 : parB3 d = min (d.length 6) (d.length 7) := rfl
  fin_cases v
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 0)
        - ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
      + (tailContribution (d.length 0) (hA6 d) 0
          + headContribution (d.length 6) (hP6 d) (hA6 d)
          + headContribution (d.length 7) (hP6 d) (hA6 d))
    have := ConfigurationReservoirChain.chainNear_nonneg fwd rev
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (n1 := d.length 6) (n2 := d.length 7) (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 0)
      + headContribution (d.length 0) (hA6 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 2)
      + tailContribution (d.length 2) 0 (hB6 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 2)
      + (headContribution (d.length 2) 0 (hB6 d)
          + tailContribution (d.length 3) (hB6 d) (hQ6 d)
          + tailContribution (d.length 4) (hB6 d) (hQ6 d))
    have := ConfigurationReservoirChain.chainFar_nonneg rev fwd
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (m1 := d.length 3) (m2 := d.length 4) (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ headContribution (d.length 3) (hB6 d) (hQ6 d)
      + headContribution (d.length 4) (hB6 d) (hQ6 d)
      + tailContribution (d.length 5) (hQ6 d) (hP6 d)
    have := ConfigurationReservoirChain.chainTarget_nonneg rev fwd
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (m1 := d.length 3) (m2 := d.length 4) (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
      + (tailContribution (d.length 6) (hP6 d) (hA6 d)
          + tailContribution (d.length 7) (hP6 d) (hA6 d)
          + headContribution (d.length 5) (hQ6 d) (hP6 d))
    have := ConfigurationReservoirChain.chainPartner_nonneg fwd rev
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (n1 := d.length 6) (n2 := d.length 7) (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega

def ownerSix (d : DegSpec 8 12) : Fin 8 :=
  if ConfigurationReservoirChain.Delivers (d.length 0) (d.length 2) (d.length 5)
      (parB2 d) (parB3 d) (hQ6 d) then 6
  else if parB2 d = 0 ∧ hQ6 d = d.length 2 then 5
  else if 0 < parB3 d then 7
  else 0

theorem t6Coeff_owner (d : DegSpec 8 12) : 1 ≤ t6Coeff d (ownerSix d) := by
  have hb := boundsT6 d
  have hp2 : parB2 d = min (d.length 3) (d.length 4) := rfl
  have hp3 : parB3 d = min (d.length 6) (d.length 7) := rfl
  unfold ownerSix
  by_cases hDel : ConfigurationReservoirChain.Delivers (d.length 0) (d.length 2)
      (d.length 5) (parB2 d) (parB3 d) (hQ6 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ headContribution (d.length 3) (hB6 d) (hQ6 d)
      + headContribution (d.length 4) (hB6 d) (hQ6 d)
      + tailContribution (d.length 5) (hQ6 d) (hP6 d)
    have := ConfigurationReservoirChain.chainTarget_ge_one rev fwd
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (m1 := d.length 3) (m2 := d.length 4) (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
      rfl rfl rfl rfl rfl hDel
    simp only [fwd_tail, rev_tail] at this
    omega
  · have hcases := ConfigurationReservoirChain.cases_of_not_delivers
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hB : parB2 d = 0 ∧ hQ6 d = d.length 2
    · rw [if_pos hB]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 2)
        + (headContribution (d.length 2) 0 (hB6 d)
            + tailContribution (d.length 3) (hB6 d) (hQ6 d)
            + tailContribution (d.length 4) (hB6 d) (hQ6 d))
      have := ConfigurationReservoirChain.chainFar_ge_one rev fwd
        (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
        (m1 := d.length 3) (m2 := d.length 4) (par2 := parB2 d) (par3 := parB3 d)
        (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
        rfl rfl rfl rfl rfl hB.1
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [if_neg hB]
      by_cases hp : 0 < parB3 d
      · rw [if_pos hp]
        show (1 : ℤ) ≤ ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
          + (tailContribution (d.length 6) (hP6 d) (hA6 d)
              + tailContribution (d.length 7) (hP6 d) (hA6 d)
              + headContribution (d.length 5) (hQ6 d) (hP6 d))
        have := ConfigurationReservoirChain.chainPartner_ge_one fwd rev
          (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
          (n1 := d.length 6) (n2 := d.length 7) (par2 := parB2 d)
          (par3 := parB3 d)
          (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
          rfl rfl rfl rfl rfl (by omega) (by omega) hp
        simp only [fwd_tail, rev_tail] at this
        omega
      · rw [if_neg hp]
        show (1 : ℤ) ≤ 1 + zeroChip (d.length 0)
            - ConfigurationReservoirChain.lend (parB3 d) (hP6 d) (hQ6 d)
          + (tailContribution (d.length 0) (hA6 d) 0
              + headContribution (d.length 6) (hP6 d) (hA6 d)
              + headContribution (d.length 7) (hP6 d) (hA6 d))
        have := ConfigurationReservoirChain.chainNear_ge_one fwd rev
          (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
          (n1 := d.length 6) (n2 := d.length 7) (par2 := parB2 d)
          (par3 := parB3 d)
          (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
          rfl rfl rfl rfl rfl (by omega) (by omega)
        simp only [fwd_tail, rev_tail] at this
        omega

theorem ownerSix_rep {d : DegSpec 8 12} (hCore : d.core = row02Core) :
    d.rep (ownerSix d) = d.rep 6 := by
  have hb := boundsT6 d
  have hp2 : parB2 d = min (d.length 3) (d.length 4) := rfl
  have hp3 : parB3 d = min (d.length 6) (d.length 7) := rfl
  unfold ownerSix
  by_cases hDel : ConfigurationReservoirChain.Delivers (d.length 0) (d.length 2)
      (d.length 5) (parB2 d) (parB3 d) (hQ6 d)
  · rw [if_pos hDel]
  · have hcases := ConfigurationReservoirChain.cases_of_not_delivers
      (alpha := d.length 0) (beta := d.length 2) (s := d.length 5)
      (par2 := parB2 d) (par3 := parB3 d)
      (hQ := hQ6 d) (hP := hP6 d) (hA := hA6 d) (hB := hB6 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hB : parB2 d = 0 ∧ hQ6 d = d.length 2
    · rw [if_pos hB]
      exact rep_zero_parB2 hCore hB.1
    · rw [if_neg hB]
      have hs : d.length 5 = 0 := by omega
      by_cases hp : 0 < parB3 d
      · rw [if_pos hp]
        exact (rep_zero_e5 hCore hs).symm
      · rw [if_neg hp]
        rw [← rep_zero_parB3 hCore (by omega)]
        exact (rep_zero_e5 hCore hs).symm

/-! ## The two chip-free classes at the base targets

Row 02's chip weight `{0, 1, 2, 5}` is fixed by a group of order **two**, not
four, so the chip-free vertices fall into two orbits — `{3, 4}` and `{6, 7}` —
and two readings, not one, are the row's content: the reservoir *pair* at `4`
and the reservoir *chain* at `6`.  Their images at `3` and `7` are the sigma
images the docstrings above already name, and they are no longer proved. -/

theorem rowDivisor_reaches_base {d : DegSpec 8 12}
    (hCore : d.core = row02Core) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row02Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) {center : Fin 8}
    (hBase : center = 4 ∨ center = 6) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hInterior : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      0 ≤ rowDivisor d (d.interiorVertex e o) :=
    fun e o => rowDivisor_effective d _
  have hChip : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      o.val + 1 = noMark e → noMark e < d.length e →
      1 ≤ rowDivisor d (d.interiorVertex e o) := by
    intro e o hm _
    simp [noMark] at hm
  have hpT4 := profileT4 hCore
  have hpT6 := profileT6 hCore
  have hrT4 := height_rep_eq d hCore hpT4.const F hRepReach hFZero
  have hrT6 := height_rep_eq d hCore hpT6.const F hRepReach hFZero
  rcases hBase with rfl | rfl
  · exact (DharMove.ofScript _ (residual_effective d hpT4 hrT4
      (rowDivisor_coreVertex d) hInterior hChip (allocT4_classSum hCore)
      (ownerFour_rep hCore) (fun v => by
        rw [contrib_eq hCore hpT4 hrT4 v]
        exact residual_of_coeff
          (fun w => by rw [t4Coeff_eq d w]; exact t4Coeff_nonneg d w)
          (by rw [t4Coeff_eq d (ownerFour d)]; exact t4Coeff_owner d)
          v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT6 hrT6
      (rowDivisor_coreVertex d) hInterior hChip (allocT6_classSum hCore)
      (ownerSix_rep hCore) (fun v => by
        rw [contrib_eq hCore hpT6 hrT6 v]
        exact residual_of_coeff
          (fun w => by rw [t6Coeff_eq d w]; exact t6Coeff_nonneg d w)
          (by rw [t6Coeff_eq d (ownerSix d)]; exact t6Coeff_owner d)
          v))).reaches

/-! ## The sigma symmetry

`sigma` is the whole automorphism group of row 02's chip weight beyond the
identity: it exchanges the two hubs of every banana, carrying `4` to `3` and
`6` to `7`.  It is the map the target-`3` and target-`7` docstrings above call
"the sigma image".

It carries its own inverse — it is an involution — because
`ClosedOrbit.targetLength` is `fun e => length (slotPerm.symm e)` and
`Equiv.symm` of an `Equiv.ofBijective` does not reduce in the kernel; see the
module docstring of `LowGenus/GuardingOrbit.lean`. -/

/-- The identity. -/
def blockSym0 : CoreSymmetry row02Core :=
  CoreSymmetry.ofInverses row02Core
    (vertexTable [0, 1, 2, 3, 4, 5, 6, 7]) (vertexTable [0, 1, 2, 3, 4, 5, 6, 7])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `sigma = (0 5)(1 2)(3 4)(6 7)`.  Carries `4` to `3` and `6` to `7`. -/
def sigma : CoreSymmetry row02Core :=
  CoreSymmetry.ofInverses row02Core
    (vertexTable [5, 2, 1, 4, 3, 0, 7, 6]) (vertexTable [5, 2, 1, 4, 3, 0, 7, 6])
    (slotTable [2, 1, 0, 6, 7, 5, 3, 4, 9, 8, 10, 11])
    (slotTable [2, 1, 0, 6, 7, 5, 3, 4, 9, 8, 10, 11])
    (flagTable [true, true, true, true, true, true, true, true, false, false,
      true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The base target of each chip-free vertex's orbit. -/
def base : Fin 8 → Fin 8 := fun v =>
  if v = 3 then 4 else if v = 7 then 6 else v

/-- The symmetry carrying `base v` to `v`. -/
def mover : Fin 8 → CoreSymmetry row02Core := fun v =>
  if v = 3 then sigma else if v = 7 then sigma else blockSym0

/-! ## The orbit guard -/

/-- **Row 02 as an orbit guard.**  Chips on `0, 1, 2, 5`; the reservoir pair
read at `4` and the reservoir chain read at `6`, each moved to its sigma image.
This still covers the exceptional contraction face `|e5| = 0` that AR treat
with a separate (and also incorrect) divisor: the closed orthant is quantified
in `OrbitGuard.closedConstruction`, not chosen here. -/
def row02Orbit : OrbitGuard row02Core (by norm_num) 4 where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  base := base
  mover := mover
  mover_chips := by decide
  mover_hits := by decide
  guard_base := by
    intro v hv length forest not_loopy
    refine rowDivisor_reaches_base rfl (zeroSlots length)
      (fun x y => compFold_iff row02Core (zeroSlots length) x y)
      (mem_zeroSlots length) ?_
    revert hv
    fin_cases v <;> decide

theorem row02_closedConstruction :
    ClosedSubdivisionDharConstruction row02Core (by norm_num) :=
  row02Orbit.closedConstruction row02_connected

end AtanasovRanganathan.GenusFiveRow02
