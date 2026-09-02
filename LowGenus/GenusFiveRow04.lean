import LowGenus.ConfigurationMarkedRow
import LowGenus.ConfigurationReservoirChain
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 04

Row 04 is the genus-five core that alternates a banana with a single slot all
the way round an eight-cycle,

```
 e0, e1  : 0 => 1     banana      e2  : 1 -- 4
 e3, e4  : 4 => 5     banana      e5  : 5 -- 6
 e6, e7  : 6 => 7     banana      e8  : 7 -- 3
 e9, e10 : 3 => 2     banana      e11 : 2 -- 0
```

so the four bananas hang between the four single slots and the whole core is a
necklace.  Contracting all four bananas leaves the four-cycle on `0`, `4`, `6`,
`3` -- one loop for each banana and one for the cycle, genus five.

**The guarding set is `{0, 2, 5, 6}`**, two adjacent pairs sitting on the two
single slots `e11 : 2 -- 0` and `e5 : 5 -- 6`.  Those two slots are the
picture's two *reservoir arms*: a paying chip whose neighbour also carries a
chip can pay two units, which is exactly what a chip needs in order to cover
both slots of a banana at once.

The four chip-free vertices `1`, `3`, `4`, `7` are each the target of one
instance of `ConfigurationReservoirChain`'s picture

```
   A1 --alpha-- A ==(n1,n2)== P --s-- Q ==(m1,m2)== B --beta-- B1

   chips at A1, A, B, B1;  P and Q chip free, Q the target
```

read around the necklace in one of the two directions:

| target `Q` | `A1` | `A` | `P` | `B` | `B1` | `alpha` | `(n1,n2)` | `s` | `(m1,m2)` | `beta` |
|---|---|---|---|---|---|---|---|---|---|---|
| `4` | `2` | `0` | `1` | `5` | `6` | `e11` | `e0,e1`  | `e2` | `e3,e4`  | `e5`  |
| `1` | `6` | `5` | `4` | `0` | `2` | `e5`  | `e3,e4`  | `e2` | `e0,e1`  | `e11` |
| `3` | `5` | `6` | `7` | `2` | `0` | `e5`  | `e6,e7`  | `e8` | `e9,e10` | `e11` |
| `7` | `0` | `2` | `3` | `6` | `5` | `e11` | `e9,e10` | `e8` | `e6,e7`  | `e5`  |

The involution `(0 5)(1 4)(2 6)(3 7)` is a core automorphism fixing the chip
set and swapping the target `4` with `1` and the target `3` with `7`; as in row
02 the images are written out rather than transported, since the orbit
machinery moves chambers and not targets.

Every height is a nested minimum of slot lengths, hence constant across a
collapsed slot, so one script per target covers the open cell and every
nonloopy forest face at once.  A collapsed slot costs only an *allocation*:
chips move inside their contracted class so that the per-vertex ledger stays
effective.  Each picture needs three such moves -- the two reservoir chips fall
into their working chips' classes when the arms collapse, and the working chip
`A` lends the partner `P` one unit across a collapsed banana.

The closing step is generic: the four pictures are packaged as the `guard`
field of an `AtanasovRanganathan.Guarding.GuardingSet` and
`GuardingSet.closedConstruction` supplies the row's
`ClosedSubdivisionDharConstruction`.  Nothing row-specific happens after the
four targets are named; in particular the chip vertices need no argument at
all.

The endpoint plumbing is `ConfigurationMarkedRow`'s at the identically-zero
mark, which recovers the ordinary one-ramp script definitionally; no slot of
row 04 carries a chip in its interior.
-/

namespace AtanasovRanganathan.GenusFiveRow04

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
open ConfigurationFive
open ConfigurationMarkedThree
open ConfigurationMarkedRow
open Guarding

/-! ## No marks

Row 04's divisor is core supported, so every slot is an ordinary single ramp.
Passing the identically-zero mark through `ConfigurationMarkedRow` recovers
exactly that, and buys the whole residual-effectivity wrapper unchanged. -/

/-- The zero mark: no slot of row 04 carries an interior chip. -/
def noMark : Fin 12 → ℕ := fun _ => 0

@[simp] theorem noMark_apply (e : Fin 12) : noMark e = 0 := rfl

/-- A height profile with no marks needs only class constancy. -/
theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row04Core)
    {h : Fin 8 → ℕ}
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row04Core.tail e) = h (row04Core.head e)) :
    Profile d noMark h := by
  refine ⟨fun e => Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he
    rw [hCore]
    exact hconst e he

/-! ## The divisor -/

/-- `D = [0] + [2] + [5] + [6]`. -/
def chipWeight (v : Fin 8) : ℤ :=
  if v = 0 then 1 else if v = 2 then 1 else if v = 5 then 1
    else if v = 6 then 1 else 0

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

/-! ## The four banana minima -/

/-- `min |e0| |e1|`, the banana `0 == 1`. -/
def par01 (d : DegSpec 8 12) : ℕ := min (d.length 0) (d.length 1)

/-- `min |e3| |e4|`, the banana `4 == 5`. -/
def par45 (d : DegSpec 8 12) : ℕ := min (d.length 3) (d.length 4)

/-- `min |e6| |e7|`, the banana `6 == 7`. -/
def par67 (d : DegSpec 8 12) : ℕ := min (d.length 6) (d.length 7)

/-- `min |e9| |e10|`, the banana `3 == 2`. -/
def par32 (d : DegSpec 8 12) : ℕ := min (d.length 9) (d.length 10)

/-! ## The nested-min heights, four readings -/

/-- The chain at the target `1`: `A1 = 6`, `A = 5`, `P = 4`, `B = 0`,
`B1 = 2`. -/
def hQ1 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.targetHeight (d.length 5) (d.length 11)
    (d.length 2) (par01 d) (par45 d)

def hP1 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.partnerHeight (d.length 5) (d.length 11)
    (d.length 2) (par01 d) (par45 d)

def hA1 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.nearHeight (d.length 5) (d.length 11)
    (d.length 2) (par01 d) (par45 d)

def hB1 (d : DegSpec 8 12) : ℕ :=
  ConfigurationReservoirChain.farHeight (d.length 5) (d.length 11)
    (d.length 2) (par01 d) (par45 d)

/-! ## The four bound bundles -/

theorem boundsT1 (d : DegSpec 8 12) :
    (hQ1 d ≤ d.length 11 + par01 d
        ∧ hQ1 d ≤ d.length 5 + par45 d + d.length 2)
      ∧ (hQ1 d = d.length 11 + par01 d
          ∨ hQ1 d = d.length 5 + par45 d + d.length 2)
      ∧ (hP1 d ≤ d.length 5 + par45 d ∧ hP1 d ≤ hQ1 d)
      ∧ (hP1 d = d.length 5 + par45 d ∨ hP1 d = hQ1 d)
      ∧ (hA1 d ≤ d.length 5 ∧ hA1 d ≤ hP1 d)
      ∧ (hA1 d = d.length 5 ∨ hA1 d = hP1 d)
      ∧ (hB1 d ≤ d.length 11 ∧ hB1 d ≤ hQ1 d)
      ∧ (hB1 d = d.length 11 ∨ hB1 d = hQ1 d)
      ∧ (hA1 d ≤ hP1 d ∧ hP1 d ≤ hQ1 d ∧ hB1 d ≤ hQ1 d
          ∧ hP1 d ≤ hA1 d + par45 d ∧ hQ1 d ≤ hB1 d + par01 d
          ∧ hQ1 d ≤ hP1 d + d.length 2) :=
  ConfigurationReservoirChain.bounds rfl rfl rfl rfl

/-! ## The four height vectors -/

/-- The chain read at the target `1`. -/
def heightT1 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then hB1 d else if v = 1 then hQ1 d else if v = 4 then hP1 d
    else if v = 5 then hA1 d else 0

theorem profileT1 {d : DegSpec 8 12} (hCore : d.core = row04Core) :
    Profile d noMark (heightT1 d) := by
  have hb := boundsT1 d
  have hp01 : par01 d = min (d.length 0) (d.length 1) := rfl
  have hp45 : par45 d = min (d.length 3) (d.length 4) := rfl
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT1, row04Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex

Each of the eight core vertices is trivalent, so `contribForm` has three terms
per vertex; they are the twenty-four slot ends of row 04 sorted by vertex. -/

def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 1)
      + tailContribution (d.length 1) (h 0) (h 1)
      + headContribution (d.length 11) (h 2) (h 0)
  else if v = 1 then
    headContribution (d.length 0) (h 0) (h 1)
      + headContribution (d.length 1) (h 0) (h 1)
      + tailContribution (d.length 2) (h 1) (h 4)
  else if v = 2 then
    headContribution (d.length 9) (h 3) (h 2)
      + headContribution (d.length 10) (h 3) (h 2)
      + tailContribution (d.length 11) (h 2) (h 0)
  else if v = 3 then
    headContribution (d.length 8) (h 7) (h 3)
      + tailContribution (d.length 9) (h 3) (h 2)
      + tailContribution (d.length 10) (h 3) (h 2)
  else if v = 4 then
    headContribution (d.length 2) (h 1) (h 4)
      + tailContribution (d.length 3) (h 4) (h 5)
      + tailContribution (d.length 4) (h 4) (h 5)
  else if v = 5 then
    headContribution (d.length 3) (h 4) (h 5)
      + headContribution (d.length 4) (h 4) (h 5)
      + tailContribution (d.length 5) (h 5) (h 6)
  else if v = 6 then
    headContribution (d.length 5) (h 5) (h 6)
      + tailContribution (d.length 6) (h 6) (h 7)
      + tailContribution (d.length 7) (h 6) (h 7)
  else
    headContribution (d.length 6) (h 6) (h 7)
      + headContribution (d.length 7) (h 6) (h 7)
      + tailContribution (d.length 8) (h 7) (h 3)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row04Core)
    {h : Fin 8 → ℕ} (hprof : Profile d noMark h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) noMark
        (markValue d noMark h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row04Core, Fin.isValue, Fin.zero_eta, slotTailForm, noMark,
      lt_self_iff_false, ↓reduceIte, slotHeadForm, Fin.sum_univ_succ, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      zero_add, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Fin.reduceEq,
      Finset.sum_const_zero, contribForm, Fin.mk_one, Fin.reduceFinMk, Finset.sum_singleton]<;>
    ring

/-! ## Which core vertices a collapsed slot identifies -/

section Rep

variable {d : DegSpec 8 12} (hCore : d.core = row04Core)
include hCore

theorem rep_zero_e2 (hz : d.length 2 = 0) : d.rep 1 = d.rep 4 := by
  have h := d.rep_zero 2 hz; rw [hCore] at h; simpa [row04Core] using h

theorem rep_zero_e5 (hz : d.length 5 = 0) : d.rep 5 = d.rep 6 := by
  have h := d.rep_zero 5 hz; rw [hCore] at h; simpa [row04Core] using h

theorem rep_zero_e8 (hz : d.length 8 = 0) : d.rep 7 = d.rep 3 := by
  have h := d.rep_zero 8 hz; rw [hCore] at h; simpa [row04Core] using h

theorem rep_zero_e11 (hz : d.length 11 = 0) : d.rep 2 = d.rep 0 := by
  have h := d.rep_zero 11 hz; rw [hCore] at h; simpa [row04Core] using h

theorem rep_zero_par01 (hz : par01 d = 0) : d.rep 0 = d.rep 1 := by
  have hEither : d.length 0 = 0 ∨ d.length 1 = 0 := by
    simpa [par01, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 0 h; rw [hCore] at hh; simpa [row04Core] using hh
  · have hh := d.rep_zero 1 h; rw [hCore] at hh; simpa [row04Core] using hh

theorem rep_zero_par45 (hz : par45 d = 0) : d.rep 4 = d.rep 5 := by
  have hEither : d.length 3 = 0 ∨ d.length 4 = 0 := by
    simpa [par45, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 3 h; rw [hCore] at hh; simpa [row04Core] using hh
  · have hh := d.rep_zero 4 h; rw [hCore] at hh; simpa [row04Core] using hh

theorem rep_zero_par67 (hz : par67 d = 0) : d.rep 6 = d.rep 7 := by
  have hEither : d.length 6 = 0 ∨ d.length 7 = 0 := by
    simpa [par67, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 6 h; rw [hCore] at hh; simpa [row04Core] using hh
  · have hh := d.rep_zero 7 h; rw [hCore] at hh; simpa [row04Core] using hh

theorem rep_zero_par32 (hz : par32 d = 0) : d.rep 3 = d.rep 2 := by
  have hEither : d.length 9 = 0 ∨ d.length 10 = 0 := by
    simpa [par32, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 9 h; rw [hCore] at hh; simpa [row04Core] using hh
  · have hh := d.rep_zero 10 h; rw [hCore] at hh; simpa [row04Core] using hh

end Rep

/-! ## Chip allocations

Every transfer moves weight *inside* one contracted class, so no class sum --
hence no divisor value -- changes.  Each picture makes three moves: the two
reservoir chips fall into their working chips' classes when the reservoir arms
collapse, and the working chip `A` lends the partner `P` a unit across a
collapsed near banana. -/

/-- The allocation of the chain read at `1`. -/
def allocT1 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 5 = 0 then transferWeight 6 5 v else 0)
    + (if d.length 11 = 0 then transferWeight 2 0 v else 0)
    + (if par45 d = 0 ∧ hP1 d < hQ1 d then transferWeight 5 4 v else 0)

theorem allocT1_classSum {d : DegSpec 8 12} (hCore : d.core = row04Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT1 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT1, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 6 5
      (fun hz => (rep_zero_e5 hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 2 0 (rep_zero_e11 hCore),
    sum_conditional_transfer_eq_zero d _ 5 4
      (fun hz => (rep_zero_par45 hCore hz.1).symm)]
  simp

/-! ## The chain at the target `1` -/

def t1Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    1 + zeroChip (d.length 11)
      + (headContribution (d.length 11) 0 (hB1 d)
          + tailContribution (d.length 0) (hB1 d) (hQ1 d)
          + tailContribution (d.length 1) (hB1 d) (hQ1 d))
  else if v = 1 then
    headContribution (d.length 0) (hB1 d) (hQ1 d)
      + headContribution (d.length 1) (hB1 d) (hQ1 d)
      + tailContribution (d.length 2) (hQ1 d) (hP1 d)
  else if v = 2 then
    positiveChip (d.length 11) + tailContribution (d.length 11) 0 (hB1 d)
  else if v = 4 then
    ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
      + (tailContribution (d.length 3) (hP1 d) (hA1 d)
          + tailContribution (d.length 4) (hP1 d) (hA1 d)
          + headContribution (d.length 2) (hQ1 d) (hP1 d))
  else if v = 5 then
    1 + zeroChip (d.length 5)
        - ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
      + (tailContribution (d.length 5) (hA1 d) 0
          + headContribution (d.length 3) (hP1 d) (hA1 d)
          + headContribution (d.length 4) (hP1 d) (hA1 d))
  else if v = 6 then
    positiveChip (d.length 5) + headContribution (d.length 5) (hA1 d) 0
  else 0

theorem t1Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT1 d v + contribForm d (heightT1 d) v = t1Coeff d v := by
  fin_cases v <;>
    simp [t1Coeff, allocT1, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, ConfigurationReservoirChain.lend, contribForm,
      heightT1]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem t1Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t1Coeff d v := by
  have hb := boundsT1 d
  have hp01 : par01 d = min (d.length 0) (d.length 1) := rfl
  have hp45 : par45 d = min (d.length 3) (d.length 4) := rfl
  fin_cases v
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 11)
      + (headContribution (d.length 11) 0 (hB1 d)
          + tailContribution (d.length 0) (hB1 d) (hQ1 d)
          + tailContribution (d.length 1) (hB1 d) (hQ1 d))
    have := ConfigurationReservoirChain.chainFar_nonneg rev fwd
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (m1 := d.length 0) (m2 := d.length 1) (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ headContribution (d.length 0) (hB1 d) (hQ1 d)
      + headContribution (d.length 1) (hB1 d) (hQ1 d)
      + tailContribution (d.length 2) (hQ1 d) (hP1 d)
    have := ConfigurationReservoirChain.chainTarget_nonneg rev fwd
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (m1 := d.length 0) (m2 := d.length 1) (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 11)
      + tailContribution (d.length 11) 0 (hB1 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
      + (tailContribution (d.length 3) (hP1 d) (hA1 d)
          + tailContribution (d.length 4) (hP1 d) (hA1 d)
          + headContribution (d.length 2) (hQ1 d) (hP1 d))
    have := ConfigurationReservoirChain.chainPartner_nonneg fwd rev
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (n1 := d.length 3) (n2 := d.length 4) (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 5)
        - ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
      + (tailContribution (d.length 5) (hA1 d) 0
          + headContribution (d.length 3) (hP1 d) (hA1 d)
          + headContribution (d.length 4) (hP1 d) (hA1 d))
    have := ConfigurationReservoirChain.chainNear_nonneg fwd rev
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (n1 := d.length 3) (n2 := d.length 4) (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d) rfl rfl rfl rfl rfl
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ positiveChip (d.length 5)
      + headContribution (d.length 5) (hA1 d) 0
    exact positiveChip_add_head_nonneg (by omega)
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num

def ownerOne (d : DegSpec 8 12) : Fin 8 :=
  if ConfigurationReservoirChain.Delivers (d.length 5) (d.length 11)
      (d.length 2) (par01 d) (par45 d) (hQ1 d) then 1
  else if par01 d = 0 ∧ hQ1 d = d.length 11 then 0
  else if 0 < par45 d then 4
  else 5

theorem t1Coeff_owner (d : DegSpec 8 12) : 1 ≤ t1Coeff d (ownerOne d) := by
  have hb := boundsT1 d
  have hp01 : par01 d = min (d.length 0) (d.length 1) := rfl
  have hp45 : par45 d = min (d.length 3) (d.length 4) := rfl
  unfold ownerOne
  by_cases hDel : ConfigurationReservoirChain.Delivers (d.length 5)
      (d.length 11) (d.length 2) (par01 d) (par45 d) (hQ1 d)
  · rw [if_pos hDel]
    show (1 : ℤ) ≤ headContribution (d.length 0) (hB1 d) (hQ1 d)
      + headContribution (d.length 1) (hB1 d) (hQ1 d)
      + tailContribution (d.length 2) (hQ1 d) (hP1 d)
    have := ConfigurationReservoirChain.chainTarget_ge_one rev fwd
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (m1 := d.length 0) (m2 := d.length 1) (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
      rfl rfl rfl rfl rfl hDel
    simp only [fwd_tail, rev_tail] at this
    omega
  · have hcases := ConfigurationReservoirChain.cases_of_not_delivers
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hB : par01 d = 0 ∧ hQ1 d = d.length 11
    · rw [if_pos hB]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 11)
        + (headContribution (d.length 11) 0 (hB1 d)
            + tailContribution (d.length 0) (hB1 d) (hQ1 d)
            + tailContribution (d.length 1) (hB1 d) (hQ1 d))
      have := ConfigurationReservoirChain.chainFar_ge_one rev fwd
        (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
        (m1 := d.length 0) (m2 := d.length 1) (par2 := par01 d)
        (par3 := par45 d)
        (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
        rfl rfl rfl rfl rfl hB.1
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [if_neg hB]
      by_cases hp : 0 < par45 d
      · rw [if_pos hp]
        show (1 : ℤ) ≤
          ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
          + (tailContribution (d.length 3) (hP1 d) (hA1 d)
              + tailContribution (d.length 4) (hP1 d) (hA1 d)
              + headContribution (d.length 2) (hQ1 d) (hP1 d))
        have := ConfigurationReservoirChain.chainPartner_ge_one fwd rev
          (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
          (n1 := d.length 3) (n2 := d.length 4) (par2 := par01 d)
          (par3 := par45 d)
          (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
          rfl rfl rfl rfl rfl (by omega) (by omega) hp
        simp only [fwd_tail, rev_tail] at this
        omega
      · rw [if_neg hp]
        show (1 : ℤ) ≤ 1 + zeroChip (d.length 5)
            - ConfigurationReservoirChain.lend (par45 d) (hP1 d) (hQ1 d)
          + (tailContribution (d.length 5) (hA1 d) 0
              + headContribution (d.length 3) (hP1 d) (hA1 d)
              + headContribution (d.length 4) (hP1 d) (hA1 d))
        have := ConfigurationReservoirChain.chainNear_ge_one fwd rev
          (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
          (n1 := d.length 3) (n2 := d.length 4) (par2 := par01 d)
          (par3 := par45 d)
          (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
          rfl rfl rfl rfl rfl (by omega) (by omega)
        simp only [fwd_tail, rev_tail] at this
        omega

theorem ownerOne_rep {d : DegSpec 8 12} (hCore : d.core = row04Core) :
    d.rep (ownerOne d) = d.rep 1 := by
  unfold ownerOne
  by_cases hDel : ConfigurationReservoirChain.Delivers (d.length 5)
      (d.length 11) (d.length 2) (par01 d) (par45 d) (hQ1 d)
  · rw [if_pos hDel]
  · have hcases := ConfigurationReservoirChain.cases_of_not_delivers
      (alpha := d.length 5) (beta := d.length 11) (s := d.length 2)
      (par2 := par01 d) (par3 := par45 d)
      (hQ := hQ1 d) (hP := hP1 d) (hA := hA1 d) (hB := hB1 d)
      rfl rfl rfl rfl hDel
    rw [if_neg hDel]
    by_cases hB : par01 d = 0 ∧ hQ1 d = d.length 11
    · rw [if_pos hB]
      exact rep_zero_par01 hCore hB.1
    · rw [if_neg hB]
      have hs : d.length 2 = 0 := by omega
      by_cases hp : 0 < par45 d
      · rw [if_pos hp]
        exact (rep_zero_e2 hCore hs).symm
      · rw [if_neg hp]
        rw [← rep_zero_par45 hCore (by omega)]
        exact (rep_zero_e2 hCore hs).symm

/-! ## The chip-free class at the base target

One reservoir chain is the row's entire content.  The other three chip-free
vertices are its images under the symmetries below, so they are not proved
again. -/

theorem rowDivisor_reaches_one {d : DegSpec 8 12} (hCore : d.core = row04Core)
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row04Core (zeroSlots d.length) x y) :
    Reaches d.graph (rowDivisor d) (d.coreVertex 1) := by
  have hInterior : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      0 ≤ rowDivisor d (d.interiorVertex e o) :=
    fun e o => rowDivisor_effective d _
  have hChip : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      o.val + 1 = noMark e → noMark e < d.length e →
      1 ≤ rowDivisor d (d.interiorVertex e o) := by
    intro e o hm _
    simp [noMark] at hm
  have hpT1 := profileT1 hCore
  have hrT1 := height_rep_eq d hCore hpT1.const (zeroSlots d.length) hRepReach
    (mem_zeroSlots d.length)
  exact (DharMove.ofScript _ (residual_effective d hpT1 hrT1
    (rowDivisor_coreVertex d) hInterior hChip (allocT1_classSum hCore)
    (ownerOne_rep hCore) (fun v => by
      rw [contrib_eq hCore hpT1 hrT1 v]
      exact residual_of_coeff
        (fun w => by rw [t1Coeff_eq d w]; exact t1Coeff_nonneg d w)
        (by rw [t1Coeff_eq d (ownerOne d)]; exact t1Coeff_owner d)
        v))).reaches

/-! ## The three symmetries that carry the base target round the necklace

Row 04's chip weight `{0, 2, 5, 6}` is fixed by a group of order four, and that
group is **transitive** on the chip-free vertices `{1, 3, 4, 7}`: the necklace
can be rotated by two beads and reflected, and either move exchanges the two
reservoir arms `e11 : 2--0` and `e5 : 5--6` with each other.

Each literal carries its own inverse.  That is not decoration:
`ClosedOrbit.targetLength` is `fun e => length (slotPerm.symm e)`, and
`Equiv.symm` of an `Equiv.ofBijective` does not reduce in the kernel, so a
symmetry built by `CoreSymmetry.ofMaps` would make the orbit transport
undecidable while still passing every `vertexPerm` test.  See the module
docstring of `LowGenus/GuardingOrbit.lean`.  All three permutations happen to
be involutions, so each inverse table is its own. -/

/-- The identity. -/
def blockSym0 : CoreSymmetry row04Core :=
  CoreSymmetry.ofInverses row04Core
    (vertexTable [0, 1, 2, 3, 4, 5, 6, 7]) (vertexTable [0, 1, 2, 3, 4, 5, 6, 7])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (slotTable [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 2)(1 3)(4 7)(5 6)`: reflect the necklace.  Carries `1` to `3`. -/
def blockSym1 : CoreSymmetry row04Core :=
  CoreSymmetry.ofInverses row04Core
    (vertexTable [2, 3, 0, 1, 7, 6, 5, 4]) (vertexTable [2, 3, 0, 1, 7, 6, 5, 4])
    (slotTable [9, 10, 8, 6, 7, 5, 3, 4, 2, 0, 1, 11])
    (slotTable [9, 10, 8, 6, 7, 5, 3, 4, 2, 0, 1, 11])
    (flagTable [true, true, true, true, true, true, true, true, true, true,
      true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 5)(1 4)(2 6)(3 7)`: the antipodal map.  Carries `1` to `4`. -/
def blockSym2 : CoreSymmetry row04Core :=
  CoreSymmetry.ofInverses row04Core
    (vertexTable [5, 4, 6, 7, 1, 0, 2, 3]) (vertexTable [5, 4, 6, 7, 1, 0, 2, 3])
    (slotTable [3, 4, 2, 0, 1, 11, 9, 10, 8, 6, 7, 5])
    (slotTable [3, 4, 2, 0, 1, 11, 9, 10, 8, 6, 7, 5])
    (flagTable [true, true, true, true, true, true, true, true, true, true,
      true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `(0 6)(1 7)(2 5)(3 4)`: rotation by half the necklace.  Carries `1` to
`7`. -/
def blockSym3 : CoreSymmetry row04Core :=
  CoreSymmetry.ofInverses row04Core
    (vertexTable [6, 7, 5, 4, 3, 2, 0, 1]) (vertexTable [6, 7, 5, 4, 3, 2, 0, 1])
    (slotTable [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5])
    (slotTable [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5]) (flagTable [])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The symmetry carrying the base target `1` to each chip-free vertex. -/
def mover : Fin 8 → CoreSymmetry row04Core := fun v =>
  if v = 3 then blockSym1 else if v = 4 then blockSym2
  else if v = 7 then blockSym3 else blockSym0

/-! ## The orbit guard -/

/-- **Row 04 as an orbit guard.**  Chips on `0, 2, 5, 6`; one reservoir chain,
read at `1` and moved to `3`, `4` and `7`. -/
def row04Orbit : OrbitGuard row04Core (by norm_num) 4 where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  base := fun _ => 1
  mover := mover
  mover_chips := by decide
  mover_hits := by decide
  guard_base := by
    intro _v _hv length forest not_loopy
    exact rowDivisor_reaches_one rfl
      (fun x y => compFold_iff row04Core (zeroSlots length) x y)

/-- **AR row 04.**  The length-independent divisor `[0]+[2]+[5]+[6]`, valid
simultaneously on the open cell and on every nonloopy forest face of the length
orthant.  The closing step is `OrbitGuard.closedConstruction`; nothing
row-specific happens after the one reservoir chain is named. -/
theorem row04_closedConstruction :
    ClosedSubdivisionDharConstruction row04Core (by norm_num) :=
  row04Orbit.closedConstruction row04_connected

end AtanasovRanganathan.GenusFiveRow04