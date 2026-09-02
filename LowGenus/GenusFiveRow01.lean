import LowGenus.ClosedConstructionTail
import LowGenus.ConfigurationMarkedRow
import LowGenus.ConfigurationReservoirPair
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 01

Row 01 is AR's *first family*.  Its core is two bananas joined by a
four-vertex band,

```
 e0, e1 : 0 -> 1     banana B0        e6      : 5 -> 7
 e2     : 2 -> 0                      e7      : 2 -> 4
 e3     : 1 -> 3                      e8      : 4 -> 6
 e4     : 2 -> 3                      e9      : 4 -> 5
 e5     : 3 -> 5                      e10,e11 : 6 -> 7   banana B6
```

so the four *interior* vertices `2, 3, 4, 5` carry the whole divisor

```
 D = [2] + [3] + [4] + [5]
```

and the four *banana* vertices `0, 1, 6, 7` are chip free.  Each of the four is
the target of one instance of `ConfigurationReservoirPair`: a banana hanging off
two hubs, each hub fed by a chip that is itself backed by a second chip one slot
behind it.  In the notation of that file,

```
   A1 --alpha-- A --l-- B --beta-- B1        chips at A1, A, B, B1
                |             |
                p             q              X, Y chip free
                |             |
               (X) ==(m1,m2)== (Y)
```

the four readings are

| target `Y` | `X` | `A` | `A1` | `B` | `B1` | `alpha` | `p` | `l` | `q` | `beta` | banana |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `0` | `1` | `3` | `5` | `2` | `4` | `e5` | `e3` | `e4` | `e2` | `e7` | `e0,e1` |
| `1` | `0` | `2` | `4` | `3` | `5` | `e7` | `e2` | `e4` | `e3` | `e5` | `e0,e1` |
| `6` | `7` | `5` | `3` | `4` | `2` | `e5` | `e6` | `e9` | `e8` | `e7` | `e10,e11` |
| `7` | `6` | `4` | `2` | `5` | `3` | `e7` | `e8` | `e9` | `e6` | `e5` | `e10,e11` |

The two reservoir arms `e5` and `e7` are each shared between the two halves:
the band `2 - 3` and `4 - 5` is read once from each side, and what is a
reservoir on one reading is a working chip on the other.

Since a vertex that carries a chip needs no picture at all
(`Guarding.GuardingSet.chip_reaches`), these four readings are the *entire*
per-graph content of the row, and `GuardingSet.closedConstruction` turns them
into the closed-orthant statement with nothing row specific in between.

**Orientation.**  `ConfigurationReservoirPair` states the two hub arms `p` and
`q` for a core in which they point `A -> X` and `B -> Y`.  On row 01 that holds
for the targets `6` and `7`, but the slot `e3` runs `1 -> 3`, which is `X -> A`
on the reading at `0` and `Y -> B` on the reading at `1`.  The single lemma
`tail_eq_head_rev` below -- the contribution at an end does not know which end
of the slot it is, only which height it carries -- reconciles the two, and is
the only new arithmetic in the file.

Every height is a nested minimum of slot lengths, hence constant across a
collapsed slot, so one script covers the open cell and every nonloopy forest
face at once.  A collapsed slot costs an allocation instead: chips move inside
their contracted class so that the per-vertex ledger, not merely the class
ledger, stays effective, and the hub transfer is used with coefficient **two**.

The endpoint plumbing is `ConfigurationMarkedRow`'s, instantiated at the
identically-zero mark `noMark`; no slot of row 01 carries a chip in its
interior.

The declarations below prove directly that the core-supported divisor
`1_{2,3,4,5}` has rank at least one throughout the stated orthant.
-/

namespace AtanasovRanganathan.GenusFiveRow01

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.CoreOrbitReduction
open Configurations
open GenusFiveCoreAtlas
open Guarding
open ConfigurationFive
open ConfigurationMarkedThree
open ConfigurationMarkedRow
open ConfigurationReservoirPair

/-! ## Reading a slot from the other end

The two-slope potential puts its lower slope first, so `tailContribution` and
`headContribution` are not the same function.  They are, however, the same
*contribution*: what a slot charges at one of its ends depends only on the
height there and the height at the other end, not on which end the core calls
the tail.  Concretely the first canonical slope is the Euclidean quotient and
the last is the ceiling, and the two swap when the rise is negated. -/

/-- The first canonical slope of a rise is minus the last canonical slope of
the opposite rise. -/
theorem step_first_eq_neg_last {L : ℕ} (hL : 0 < L) (T : ℤ) :
    SubdivisionArithmetic.step L T 0 =
      -SubdivisionArithmetic.step L (-T) (L - 1) := by
  have hLZ : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  rw [SubdivisionArithmetic.firstStep_eq_quotient T hL,
    SubdivisionArithmetic.lastStep_eq_ite (-T) hL]
  simp only [SubdivisionArithmetic.quotient, SubdivisionArithmetic.remainder]
  have e1 : (L : ℤ) * (T / (L : ℤ)) + T % (L : ℤ) = T :=
    Int.mul_ediv_add_emod T (L : ℤ)
  have b1 : 0 ≤ T % (L : ℤ) := Int.emod_nonneg T hLZ.ne'
  have b2 : T % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos T hLZ
  by_cases hr : T % (L : ℤ) = 0
  · have hT : -T = (L : ℤ) * (-(T / (L : ℤ))) := by rw [hr] at e1; linarith
    have hd : (-T) / (L : ℤ) = -(T / (L : ℤ)) := by
      rw [hT, Int.mul_ediv_cancel_left _ hLZ.ne']
    have hm : (-T) % (L : ℤ) = 0 := by rw [hT, Int.mul_emod_right]
    simp only [hd, hm]
    norm_num
  · have hT : -T = ((L : ℤ) - T % (L : ℤ)) + (L : ℤ) * (-(T / (L : ℤ)) - 1) := by
      linarith
    have hd : (-T) / (L : ℤ) = -(T / (L : ℤ)) - 1 := by
      rw [hT, Int.add_mul_ediv_left _ _ hLZ.ne',
        Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
    have hm : (-T) % (L : ℤ) = (L : ℤ) - T % (L : ℤ) := by
      rw [hT, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [hd, hm]
    rw [if_neg (by omega)]
    ring

/-- **A slot has no preferred end.**  The charge at the end carrying `hu`, with
`hv` at the other end, is the same whether the core calls that end the tail or
the head.  This is what lets row 01 read `e3` in both directions. -/
theorem tail_eq_head_rev (L hu hv : ℕ) :
    tailContribution L hu hv = headContribution L hv hu := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [tailContribution, headContribution, hL]
  · have hneg : ((hv : ℤ) - (hu : ℤ)) = -((hu : ℤ) - (hv : ℤ)) := by ring
    simp only [tailContribution, headContribution, if_neg hL.ne', hneg]
    exact step_first_eq_neg_last hL _

/-! ## No marks -/

/-- The zero mark: no slot of row 01 carries an interior chip. -/
def noMark : Fin 12 → ℕ := fun _ => 0

@[simp] theorem noMark_apply (e : Fin 12) : noMark e = 0 := rfl

/-- A height profile with no marks needs only class constancy. -/
theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row01Core)
    {h : Fin 8 → ℕ}
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row01Core.tail e) = h (row01Core.head e)) :
    Profile d noMark h := by
  refine ⟨fun e => Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he
    rw [hCore]
    exact hconst e he

/-! ## The divisor -/

/-- `D = [2] + [3] + [4] + [5]`. -/
def chipWeight (v : Fin 8) : ℤ :=
  if v = 2 then 1 else if v = 3 then 1 else if v = 4 then 1
    else if v = 5 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph := d.coreClassDivisor chipWeight

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_coreVertex (d : DegSpec 8 12) (r : Fin 8) :
    rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v :=
  d.coreClassDivisor_coreVertex chipWeight r

/-! ## The two banana minima -/

/-- `min |e0| |e1|`, the banana on `{0, 1}`. -/
def par01 (d : DegSpec 8 12) : ℕ := min (d.length 0) (d.length 1)

/-- `min |e10| |e11|`, the banana on `{6, 7}`. -/
def par67 (d : DegSpec 8 12) : ℕ := min (d.length 10) (d.length 11)

/-! ## The nested-min heights, four readings -/

/-- The reading at the target `0`: `A1 = 5`, `A = 3`, `B = 2`, `B1 = 4`,
`X = 1`, `Y = 0`. -/
def hB0 (d : DegSpec 8 12) : ℕ :=
  restHeight (d.length 5) (d.length 7)

def hA0 (d : DegSpec 8 12) : ℕ :=
  workHeight (d.length 5) (d.length 7) (d.length 4) (d.length 2)

def hX0 (d : DegSpec 8 12) : ℕ :=
  hubHeight (d.length 5) (d.length 7) (d.length 4) (d.length 3) (d.length 2)

def hY0 (d : DegSpec 8 12) : ℕ :=
  targetHeight (d.length 5) (d.length 7) (d.length 4) (d.length 3) (d.length 2)
    (par01 d)

/-! ## The four bound bundles -/

theorem boundsT0 (d : DegSpec 8 12) :
    (hB0 d ≤ d.length 5 ∧ hB0 d ≤ d.length 7)
      ∧ (hB0 d = d.length 5 ∨ hB0 d = d.length 7)
      ∧ (hA0 d ≤ d.length 5 ∧ hA0 d ≤ hB0 d + d.length 4
          ∧ hA0 d ≤ hB0 d + d.length 2 ∧ hB0 d ≤ hA0 d)
      ∧ (hA0 d = d.length 5 ∨ hA0 d = hB0 d + d.length 4
          ∨ hA0 d = hB0 d + d.length 2)
      ∧ (hX0 d ≤ hB0 d + d.length 2 ∧ hX0 d ≤ hA0 d + 2 * d.length 3
          ∧ hA0 d ≤ hX0 d)
      ∧ (hX0 d = hB0 d + d.length 2 ∨ hX0 d = hA0 d + 2 * d.length 3)
      ∧ (hY0 d ≤ hB0 d + d.length 2 ∧ hY0 d ≤ hX0 d + par01 d ∧ hX0 d ≤ hY0 d)
      ∧ (hY0 d = hB0 d + d.length 2 ∨ hY0 d = hX0 d + par01 d) :=
  ConfigurationReservoirPair.bounds rfl rfl rfl rfl

/-! ## The four height vectors -/

/-- The pair read at the target `0`. -/
def heightT0 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then hY0 d else if v = 1 then hX0 d else if v = 2 then hB0 d
    else if v = 3 then hA0 d else 0

theorem profileT0 {d : DegSpec 8 12} (hCore : d.core = row01Core) :
    Profile d noMark (heightT0 d) := by
  have hb := boundsT0 d
  have hpar : par01 d = min (d.length 0) (d.length 1) := rfl
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT0, row01Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex

Each of the eight core vertices is trivalent, so `contribForm` has three terms
per vertex; they are the twenty-four slot ends of row 01 sorted by vertex. -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1)
      + tailContribution (d.length 1) (h 0) (h 1)
      + headContribution (d.length 2) (h 2) (h 0)
  else if v = 1 then
    headContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 1) (h 0) (h 1)
      + tailContribution (d.length 3) (h 1) (h 3)
  else if v = 2 then
    tailContribution (d.length 2) (h 2) (h 0)
      + tailContribution (d.length 4) (h 2) (h 3)
      + tailContribution (d.length 7) (h 2) (h 4)
  else if v = 3 then
    headContribution (d.length 3) (h 1) (h 3)
      + headContribution (d.length 4) (h 2) (h 3)
      + tailContribution (d.length 5) (h 3) (h 5)
  else if v = 4 then
    headContribution (d.length 7) (h 2) (h 4)
      + tailContribution (d.length 8) (h 4) (h 6)
      + tailContribution (d.length 9) (h 4) (h 5)
  else if v = 5 then
    headContribution (d.length 5) (h 3) (h 5)
      + headContribution (d.length 9) (h 4) (h 5)
      + tailContribution (d.length 6) (h 5) (h 7)
  else if v = 6 then
    headContribution (d.length 8) (h 4) (h 6)
      + tailContribution (d.length 10) (h 6) (h 7)
      + tailContribution (d.length 11) (h 6) (h 7)
  else
    headContribution (d.length 6) (h 5) (h 7)
      + headContribution (d.length 10) (h 6) (h 7)
      + headContribution (d.length 11) (h 6) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row01Core)
    {h : Fin 8 → ℕ} (hprof : Profile d noMark h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) noMark
        (markValue d noMark h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row01Core, Fin.isValue, Fin.zero_eta, slotTailForm, noMark,
      lt_self_iff_false, ↓reduceIte, slotHeadForm, Fin.sum_univ_succ, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      zero_add, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Fin.reduceEq,
      Finset.sum_const_zero, contribForm, Fin.mk_one, Fin.reduceFinMk, Finset.sum_singleton]<;>
    ring

/-! ## Which core vertices a collapsed slot identifies -/

section Rep

variable {d : DegSpec 8 12} (hCore : d.core = row01Core)
include hCore

theorem rep_zero_e2 (hz : d.length 2 = 0) : d.rep 2 = d.rep 0 := by
  have h := d.rep_zero 2 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e3 (hz : d.length 3 = 0) : d.rep 1 = d.rep 3 := by
  have h := d.rep_zero 3 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e4 (hz : d.length 4 = 0) : d.rep 2 = d.rep 3 := by
  have h := d.rep_zero 4 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e5 (hz : d.length 5 = 0) : d.rep 3 = d.rep 5 := by
  have h := d.rep_zero 5 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e6 (hz : d.length 6 = 0) : d.rep 5 = d.rep 7 := by
  have h := d.rep_zero 6 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e7 (hz : d.length 7 = 0) : d.rep 2 = d.rep 4 := by
  have h := d.rep_zero 7 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e8 (hz : d.length 8 = 0) : d.rep 4 = d.rep 6 := by
  have h := d.rep_zero 8 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_e9 (hz : d.length 9 = 0) : d.rep 4 = d.rep 5 := by
  have h := d.rep_zero 9 hz; rw [hCore] at h; simpa [row01Core] using h

theorem rep_zero_par01 (hz : par01 d = 0) : d.rep 0 = d.rep 1 := by
  have hEither : d.length 0 = 0 ∨ d.length 1 = 0 := by
    simpa [par01, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 0 h; rw [hCore] at hh; simpa [row01Core] using hh
  · have hh := d.rep_zero 1 h; rw [hCore] at hh; simpa [row01Core] using hh

theorem rep_zero_par67 (hz : par67 d = 0) : d.rep 6 = d.rep 7 := by
  have hEither : d.length 10 = 0 ∨ d.length 11 = 0 := by
    simpa [par67, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 10 h; rw [hCore] at hh; simpa [row01Core] using hh
  · have hh := d.rep_zero 11 h; rw [hCore] at hh; simpa [row01Core] using hh

end Rep

/-! ## Chip allocations

Every transfer moves weight *inside* one contracted class, so no class sum --
hence no divisor value -- changes.  The reservoir chip falls into its working
chip's class when the reservoir arm collapses; the resting chip is lent across
a collapsed `l`, and the hub is handed **two** units across a collapsed arm. -/

/-- The allocation of the reading at `0`. -/
def allocT0 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 5 = 0 then transferWeight 5 3 v else 0)
    + (if d.length 7 = 0 then transferWeight 4 2 v else 0)
    + (if d.length 4 = 0 ∧ hB0 d < d.length 5 then transferWeight 2 3 v else 0)
    + (if d.length 3 = 0 ∧ hX0 d < hY0 d then transferWeight 3 1 v else 0)
    + (if d.length 3 = 0 ∧ hX0 d < hY0 d then transferWeight 3 1 v else 0)

theorem allocT0_classSum {d : DegSpec 8 12} (hCore : d.core = row01Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT0 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT0, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 5 3
      (fun hz => (rep_zero_e5 hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 4 2
      (fun hz => (rep_zero_e7 hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 2 3
      (fun hz => rep_zero_e4 hCore hz.1),
    sum_conditional_transfer_eq_zero d _ 3 1
      (fun hz => (rep_zero_e3 hCore hz.1).symm)]
  simp

/-! ## The pair at the target `0`

Here `p = |e3|` is traversed against the picture's arrow, so the two ledgers at
its ends are swapped and `tail_eq_head_rev` puts them back. -/

def t0Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    headContribution (d.length 2) (hB0 d) (hY0 d)
      + tailContribution (d.length 0) (hY0 d) (hX0 d)
      + tailContribution (d.length 1) (hY0 d) (hX0 d)
  else if v = 1 then
    2 * lendHub (d.length 3) (hX0 d) (hY0 d)
      + (tailContribution (d.length 3) (hX0 d) (hA0 d)
          + headContribution (d.length 0) (hY0 d) (hX0 d)
          + headContribution (d.length 1) (hY0 d) (hX0 d))
  else if v = 2 then
    1 + zeroChip (d.length 7) - lendFlat (d.length 4) (d.length 5) (hB0 d)
      + (tailContribution (d.length 4) (hB0 d) (hA0 d)
          + tailContribution (d.length 7) (hB0 d) 0
          + tailContribution (d.length 2) (hB0 d) (hY0 d))
  else if v = 3 then
    1 + zeroChip (d.length 5) + lendFlat (d.length 4) (d.length 5) (hB0 d)
        - 2 * lendHub (d.length 3) (hX0 d) (hY0 d)
      + (tailContribution (d.length 5) (hA0 d) 0
          + headContribution (d.length 4) (hB0 d) (hA0 d)
          + headContribution (d.length 3) (hX0 d) (hA0 d))
  else if v = 4 then
    positiveChip (d.length 7) + headContribution (d.length 7) (hB0 d) 0
  else if v = 5 then
    positiveChip (d.length 5) + headContribution (d.length 5) (hA0 d) 0
  else 0

theorem t0Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT0 d v + contribForm d (heightT0 d) v = t0Coeff d v := by
  fin_cases v <;>
    simp [t0Coeff, allocT0, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, lendFlat, lendHub, contribForm, heightT0]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem t0Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t0Coeff d v := by
  have hb := boundsT0 d
  have hpar : par01 d = min (d.length 0) (d.length 1) := rfl
  have hrev : tailContribution (d.length 3) (hX0 d) (hA0 d)
      = headContribution (d.length 3) (hA0 d) (hX0 d) :=
    tail_eq_head_rev _ _ _
  have hrev' : tailContribution (d.length 3) (hA0 d) (hX0 d)
      = headContribution (d.length 3) (hX0 d) (hA0 d) :=
    tail_eq_head_rev _ _ _
  fin_cases v
  · show (0 : ℤ) ≤ headContribution (d.length 2) (hB0 d) (hY0 d)
      + tailContribution (d.length 0) (hY0 d) (hX0 d)
      + tailContribution (d.length 1) (hY0 d) (hX0 d)
    have := ConfigurationReservoirPair.pairTarget_nonneg fwd
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (m1 := d.length 0) (m2 := d.length 1)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail] at this
    omega
  · show (0 : ℤ) ≤ 2 * lendHub (d.length 3) (hX0 d) (hY0 d)
      + (tailContribution (d.length 3) (hX0 d) (hA0 d)
          + headContribution (d.length 0) (hY0 d) (hX0 d)
          + headContribution (d.length 1) (hY0 d) (hX0 d))
    have := ConfigurationReservoirPair.pairHub_nonneg rev
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (m1 := d.length 0) (m2 := d.length 1)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d) rfl rfl rfl rfl rfl
    simp only [rev_tail] at this
    omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 7)
        - lendFlat (d.length 4) (d.length 5) (hB0 d)
      + (tailContribution (d.length 4) (hB0 d) (hA0 d)
          + tailContribution (d.length 7) (hB0 d) 0
          + tailContribution (d.length 2) (hB0 d) (hY0 d))
    have := ConfigurationReservoirPair.pairRest_nonneg fwd fwd
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d) rfl rfl rfl rfl
    simp only [fwd_tail] at this
    omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 5)
        + lendFlat (d.length 4) (d.length 5) (hB0 d)
        - 2 * lendHub (d.length 3) (hX0 d) (hY0 d)
      + (tailContribution (d.length 5) (hA0 d) 0
          + headContribution (d.length 4) (hB0 d) (hA0 d)
          + headContribution (d.length 3) (hX0 d) (hA0 d))
    have := ConfigurationReservoirPair.pairWork_nonneg fwd rev
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d) rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 7)
      + headContribution (d.length 7) (hB0 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
      + headContribution (d.length 5) (hA0 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

def ownerZero (d : DegSpec 8 12) : Fin 8 :=
  if ConfigurationReservoirPair.Delivers (d.length 2) (par01 d) (hB0 d) (hX0 d)
      (hY0 d) then 0
  else if d.length 2 = 0 then 2
  else if 0 < d.length 3 then 1
  else 3

theorem t0Coeff_owner (d : DegSpec 8 12) : 1 ≤ t0Coeff d (ownerZero d) := by
  have hb := boundsT0 d
  have hpar : par01 d = min (d.length 0) (d.length 1) := rfl
  have hrev : tailContribution (d.length 3) (hX0 d) (hA0 d)
      = headContribution (d.length 3) (hA0 d) (hX0 d) :=
    tail_eq_head_rev _ _ _
  have hrev' : tailContribution (d.length 3) (hA0 d) (hX0 d)
      = headContribution (d.length 3) (hX0 d) (hA0 d) :=
    tail_eq_head_rev _ _ _
  unfold ownerZero
  by_cases hDel : ConfigurationReservoirPair.Delivers (d.length 2) (par01 d)
      (hB0 d) (hX0 d) (hY0 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ headContribution (d.length 2) (hB0 d) (hY0 d)
      + tailContribution (d.length 0) (hY0 d) (hX0 d)
      + tailContribution (d.length 1) (hY0 d) (hX0 d)
    have := ConfigurationReservoirPair.pairTarget_ge_one fwd
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (m1 := d.length 0) (m2 := d.length 1)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
      rfl rfl rfl rfl rfl hDel
    simp only [fwd_tail] at this
    omega
  · have hcases := ConfigurationReservoirPair.cases_of_not_delivers
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hq : d.length 2 = 0
    · rw [if_pos hq]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 7)
          - lendFlat (d.length 4) (d.length 5) (hB0 d)
        + (tailContribution (d.length 4) (hB0 d) (hA0 d)
            + tailContribution (d.length 7) (hB0 d) 0
            + tailContribution (d.length 2) (hB0 d) (hY0 d))
      have := ConfigurationReservoirPair.pairRest_ge_one fwd fwd
        (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
        (p := d.length 3) (q := d.length 2) (par := par01 d)
        (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
        rfl rfl rfl rfl hq
      simp only [fwd_tail] at this
      omega
    · rw [if_neg hq]
      by_cases hp : 0 < d.length 3
      · rw [if_pos hp]
        show (1 : ℤ) ≤ 2 * lendHub (d.length 3) (hX0 d) (hY0 d)
          + (tailContribution (d.length 3) (hX0 d) (hA0 d)
              + headContribution (d.length 0) (hY0 d) (hX0 d)
              + headContribution (d.length 1) (hY0 d) (hX0 d))
        have := ConfigurationReservoirPair.pairHub_ge_one rev
          (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
          (p := d.length 3) (q := d.length 2) (par := par01 d)
          (m1 := d.length 0) (m2 := d.length 1)
          (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
          rfl rfl rfl rfl rfl hp (by omega) (by omega)
        simp only [rev_tail] at this
        omega
      · rw [if_neg hp]
        show (1 : ℤ) ≤ 1 + zeroChip (d.length 5)
            + lendFlat (d.length 4) (d.length 5) (hB0 d)
            - 2 * lendHub (d.length 3) (hX0 d) (hY0 d)
          + (tailContribution (d.length 5) (hA0 d) 0
              + headContribution (d.length 4) (hB0 d) (hA0 d)
              + headContribution (d.length 3) (hX0 d) (hA0 d))
        have := ConfigurationReservoirPair.pairWork_ge_one fwd rev
          (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
          (p := d.length 3) (q := d.length 2) (par := par01 d)
          (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
          rfl rfl rfl rfl (by omega) (by omega)
        simp only [fwd_tail, rev_tail] at this
        omega

theorem ownerZero_rep {d : DegSpec 8 12} (hCore : d.core = row01Core) :
    d.rep (ownerZero d) = d.rep 0 := by
  have hb := boundsT0 d
  have hpar : par01 d = min (d.length 0) (d.length 1) := rfl
  unfold ownerZero
  by_cases hDel : ConfigurationReservoirPair.Delivers (d.length 2) (par01 d)
      (hB0 d) (hX0 d) (hY0 d)
  · rw [if_pos hDel]
  · have hcases := ConfigurationReservoirPair.cases_of_not_delivers
      (alpha := d.length 5) (beta := d.length 7) (l := d.length 4)
      (p := d.length 3) (q := d.length 2) (par := par01 d)
      (hB := hB0 d) (hA := hA0 d) (hX := hX0 d) (hY := hY0 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hq : d.length 2 = 0
    · rw [if_pos hq]
      exact rep_zero_e2 hCore hq
    · rw [if_neg hq]
      have hparZero : par01 d = 0 := by omega
      by_cases hp : 0 < d.length 3
      · rw [if_pos hp]
        exact (rep_zero_par01 hCore hparZero).symm
      · rw [if_neg hp]
        exact (rep_zero_e3 hCore (by omega)).symm.trans
          (rep_zero_par01 hCore hparZero).symm

/-! ## The chip-free class at the base target

One reservoir-pair reading is the row's entire content.  The other three
chip-free vertices are its images under the symmetries below, and the four chip
vertices need no picture at all. -/

theorem rowDivisor_reaches_zero {d : DegSpec 8 12}
    (hCore : d.core = row01Core) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row01Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) :
    Reaches d.graph (rowDivisor d) (d.coreVertex 0) := by
  have hInterior : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      0 ≤ rowDivisor d (d.interiorVertex e o) :=
    fun e o => rowDivisor_effective d _
  have hChip : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      o.val + 1 = noMark e → noMark e < d.length e →
      1 ≤ rowDivisor d (d.interiorVertex e o) := by
    intro e o hm _
    simp [noMark] at hm
  have hpT0 := profileT0 hCore
  have hrT0 := height_rep_eq d hCore hpT0.const F hRepReach hFZero
  exact (DharMove.ofScript _ (residual_effective d hpT0 hrT0
    (rowDivisor_coreVertex d) hInterior hChip (allocT0_classSum hCore)
    (ownerZero_rep hCore) (fun v => by
      rw [contrib_eq hCore hpT0 hrT0 v]
      exact residual_of_coeff
        (fun w => by rw [t0Coeff_eq d w]; exact t0Coeff_nonneg d w)
        (by rw [t0Coeff_eq d (ownerZero d)]; exact t0Coeff_owner d)
        v))).reaches

/-! ## The three symmetries that carry the base target across the two blocks

Row 01's chip weight `{2, 3, 4, 5}` is fixed by a group of order four, and that
group is **transitive** on the chip-free vertices `{0, 1, 6, 7}`: the two
`K₄`-minus-edge blocks may be swapped, and each block's two hubs exchanged.

Each literal carries its own inverse.  `ClosedOrbit.targetLength` is
`fun e => length (slotPerm.symm e)`, and `Equiv.symm` of an `Equiv.ofBijective`
does not reduce in the kernel, so `CoreSymmetry.ofMaps` would leave the orbit
transport undecidable while still passing every `vertexPerm` test; see the
module docstring of `LowGenus/GuardingOrbit.lean`.  All three permutations are
involutions, so each inverse table is its own. -/

/-- The identity. -/
def blockSym0 : CoreSymmetry row01Core :=
  CoreSymmetry.ofInverses row01Core
    (vertexTable [0, 1, 2, 3, 4, 5, 6, 7]) (vertexTable [0, 1, 2, 3, 4, 5, 6, 7])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 1)(2 3)(4 5)(6 7)`: exchange the two hubs of each block.  Carries `0`
to `1`. -/
def blockSym1 : CoreSymmetry row01Core :=
  CoreSymmetry.ofInverses row01Core
    (vertexTable [1, 0, 3, 2, 5, 4, 7, 6]) (vertexTable [1, 0, 3, 2, 5, 4, 7, 6])
    (slotTable [0, 1, 3, 2, 4, 7, 8, 5, 6, 9, 10, 11])
    (slotTable [0, 1, 3, 2, 4, 7, 8, 5, 6, 9, 10, 11])
    (flagTable [true, true, true, true, true, false, false, false, false,
      true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 6)(1 7)(2 4)(3 5)`: swap the two blocks.  Carries `0` to `6`. -/
def blockSym6 : CoreSymmetry row01Core :=
  CoreSymmetry.ofInverses row01Core
    (vertexTable [6, 7, 4, 5, 2, 3, 0, 1]) (vertexTable [6, 7, 4, 5, 2, 3, 0, 1])
    (slotTable [10, 11, 8, 6, 9, 5, 3, 7, 2, 4, 0, 1])
    (slotTable [10, 11, 8, 6, 9, 5, 3, 7, 2, 4, 0, 1])
    (flagTable [false, false, false, true, false, true, true, true, false,
      false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 7)(1 6)(2 5)(3 4)`: swap the blocks and the hubs.  Carries `0` to
`7`. -/
def blockSym7 : CoreSymmetry row01Core :=
  CoreSymmetry.ofInverses row01Core
    (vertexTable [7, 6, 5, 4, 3, 2, 1, 0]) (vertexTable [7, 6, 5, 4, 3, 2, 1, 0])
    (slotTable [10, 11, 6, 8, 9, 7, 2, 5, 3, 4, 0, 1])
    (slotTable [10, 11, 6, 8, 9, 7, 2, 5, 3, 4, 0, 1])
    (flagTable [true, true, false, true, true, true, false, true, true,
      true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The symmetry carrying the base target `0` to each chip-free vertex. -/
def mover : Fin 8 → CoreSymmetry row01Core := fun v =>
  if v = 1 then blockSym1 else if v = 6 then blockSym6
  else if v = 7 then blockSym7 else blockSym0

/-! ## The orbit guard -/

/-- **Row 01 as an orbit guard.**  Chips on `2, 3, 4, 5`; one reservoir-pair
reading, taken at `0` and moved to `1`, `6` and `7`. -/
def row01Orbit : OrbitGuard row01Core (by norm_num) 4 where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  base := fun _ => 0
  mover := mover
  mover_chips := by decide
  mover_hits := by decide
  guard_base := by
    intro _v _hv length forest not_loopy
    exact rowDivisor_reaches_zero rfl (zeroSlots length)
      (fun x y => compFold_iff row01Core (zeroSlots length) x y)
      (mem_zeroSlots length)

/-- **AR row 01.**  The length-independent divisor `[2]+[3]+[4]+[5]`, valid
simultaneously on the open cell and every nonloopy forest face of the length
orthant.  The closing step is `OrbitGuard.closedConstruction`; nothing row
specific happens after the one reservoir-pair reading is named. -/
theorem row01_closedConstruction :
    ClosedSubdivisionDharConstruction row01Core (by norm_num) :=
  row01Orbit.closedConstruction row01_connected

end AtanasovRanganathan.GenusFiveRow01
