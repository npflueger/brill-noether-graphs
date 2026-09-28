import Utilities.Subdivision.SlotGrid
import Utilities.Subdivision.SlopeScript
import Utilities.Foundations.RankInvariance

/-!
# The interior-firing lemma

If every slot length and every interior offset moment of an effective divisor
is divisible by `m`, the divisor is linearly equivalent to an effective one
supported on the `m`-grid (`exists_onGrid`).

The argument: on a path of degree-two vertices, firing the consecutive set
`{s, …, t}` moves one chip from `s` to `s − 1` and one from `t` to `t + 1`,
and the offset sum of the interior chips is preserved modulo the slot length.
Here the whole nest of consecutive sets is fired at once, as the trapezoid
script `moveScript`, so no iteration of `set_firing` is needed.

## What is proved

Fix a specification `T : Spec n p` and a modulus `m`.

* `slotMoment T D e` — the offset-weighted sum `Σ_j D(interior e j) · (j + 1)`
  of the interior chips of one slot; `slotCount`, `interiorTotal` count them.
* `trapVal q r d` — the trapezoid profile that is `0` outside `[q − d, r + d]`,
  rises with slope one to the plateau `d` on `[q, r]`, and falls back; its
  second difference is `+1, −1, −1, +1` at `q − d, q, r, r + d`
  (`trapVal_laplace`).
* `moveScript T e q r d` — the corresponding firing script, built as a
  `Spec.slotValueScript` (from `Utilities.Subdivision.SlopeScript`) that
  vanishes on every core vertex and on every slot other than `e`.  Its
  Laplacian is computed exactly: `prin_moveScript_interior_same`,
  `prin_moveScript_interior_other`, and `prin_moveScript_core_nonneg` (at a
  core vertex it is a sum of indicators, hence never negative).
* `moved T D e q r d = D + prin (moveScript …)`, with `linear_equiv_moved`
  (via `principal_iff_eq_prin` of `ChipFiringWithLean.Basic`),
  `effective_moved`, `dvd_slotMoment_moved` (the slot moment changes by `0` or
  by `− T.length e`, so it is unchanged modulo any `m` dividing the slot
  length), and `slotCount_moved_le` (one interior chip at least leaves the
  interior whenever `d = min q (T.length e − r)`).
* `exists_two_chips` — an effective divisor with at least two interior chips on
  a slot has two offsets `q ≤ r` that can be pushed apart.
* **`exists_onGrid`** — the lemma itself: if `m` divides every slot length and
  `(m : ℤ)` divides every `slotMoment T D e`, an effective `D` is
  `linear_equiv` to an effective `D'` of the same degree all of whose chips are
  on the `m`-grid of `Utilities.Subdivision.SlotGrid`.  `exists_onGrid_rank`
  adds that every rank lower bound is carried across
  (by `Utilities.Foundations.RankInvariance`), and `exists_onGrid_scale`
  states both for `spec.scale N` with `m ∣ N`.
* `segmentTwoChips` and the example after it — two chips at fine offsets `1`
  and `3` of the six-fold unit segment, offset sum `4`, moved onto the `2`-grid
  unconditionally.

## What is NOT proved here

Every hypothesis is explicit and none is discharged: `effective D`, `m ∣ T.length e`
for every slot, and `(m : ℤ) ∣ slotMoment T D e` for every slot.  The lemma says
nothing about *where* on the grid the chips end up, nothing about the divisor
class, and nothing about how the moment hypothesis is to be obtained — that is
a separate input, not used or assumed here (`Utilities.Subdivision.SlotMoment`
supplies the arithmetic that turns rational chip positions with odd
denominators into this hypothesis).  The conclusion is an existence statement;
`moved` is the single step, not the result.
Loops in the core are excluded only because `Spec` excludes them.

## Consumers

`Utilities.Subdivision.ZeroBudgetRounding`, which consumes the grid support,
and through it the Draisma--Vargas count, where it is used to construct
odd-subdivision witnesses.
-/

namespace DraismaVargas.Count.InteriorFiring

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Count.SlotGrid

variable {n p : ℕ}

/-- The trapezoid profile: zero outside `[q - d, r + d]`, rising with slope one to the
plateau `d` on `[q, r]`, and falling back.  It is the sum of the indicator scripts of
the nested intervals `[q - i, r + i]`, `0 ≤ i < d`. -/
def trapVal (q r d : ℕ) (k : ℕ) : ℤ :=
  max 0 (min (d : ℤ) (min ((k : ℤ) - (q : ℤ) + (d : ℤ)) ((r : ℤ) + (d : ℤ) - (k : ℤ))))

/-- The profile vanishes at the tail endpoint. -/
theorem trapVal_zero (q r d : ℕ) (hdq : d ≤ q) : trapVal q r d 0 = 0 := by
  unfold trapVal
  omega

/-- The profile vanishes at the head endpoint. -/
theorem trapVal_end (q r d L : ℕ) (hrL : r + d ≤ L) : trapVal q r d L = 0 := by
  unfold trapVal
  omega

/-- The outgoing slope at the tail is one exactly when the left chip reaches the tail. -/
theorem trapVal_one (q r d : ℕ) (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) :
    trapVal q r d 1 = if q = d then (1 : ℤ) else 0 := by
  unfold trapVal
  split_ifs <;> omega

/-- The outgoing slope at the head is one exactly when the right chip reaches the head. -/
theorem trapVal_pred (q r d L : ℕ) (hd : 1 ≤ d) (hqr : q ≤ r)
    (hrL : r + d ≤ L) :
    trapVal q r d (L - 1) = if r + d = L then (1 : ℤ) else 0 := by
  have hL : 1 ≤ L := by omega
  have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
  unfold trapVal
  rw [hcast]
  split_ifs <;> omega

/-- The second difference of the profile: `+1` at `q - d`, `-1` at `q`, `-1` at `r`,
`+1` at `r + d`.  This is the whole content of the move. -/
theorem trapVal_laplace (q r d : ℕ) (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (o : ℕ) :
    trapVal q r d (o + 2) - 2 * trapVal q r d (o + 1) + trapVal q r d o
      = (if o + 1 = q - d then (1 : ℤ) else 0) - (if o + 1 = q then (1 : ℤ) else 0)
        - (if o + 1 = r then (1 : ℤ) else 0) + (if o + 1 = r + d then (1 : ℤ) else 0) := by
  unfold trapVal
  split_ifs <;> omega

/-! ## The firing script of one interior move -/

/-- The value profile of the move script on each slot. -/
def moveValue (e : Fin p) (q r d : ℕ) : Fin p → ℕ → ℤ :=
  fun e' k => if e' = e then trapVal q r d k else 0

/-- The script that pushes the chip at offset `q` of slot `e` left by `d` and the
chip at offset `r` right by `d`. -/
def moveScript (T : Spec n p) (e : Fin p) (q r d : ℕ) : firing_script T.graph :=
  T.slotValueScript (fun _ => 0) (moveValue e q r d)

/-- The move profile is compatible with the identically zero core potential. -/
theorem moveValue_compatible (T : Spec n p) (e : Fin p) (q r d : ℕ)
    (hdq : d ≤ q) (hrL : r + d ≤ T.length e) :
    T.SlotValueCompatible (fun _ => 0) (moveValue e q r d) where
  tail := by
    intro e'
    by_cases h : e' = e
    · subst h; simp [moveValue, trapVal_zero q r d hdq]
    · simp [moveValue, h]
  head := by
    intro e'
    by_cases h : e' = e
    · subst h; simp [moveValue, trapVal_end q r d _ hrL]
    · simp [moveValue, h]

/-- The move script has no Laplacian on any other slot. -/
theorem prin_moveScript_interior_other (T : Spec n p) (e e' : Fin p) (q r d : ℕ)
    (hdq : d ≤ q) (hrL : r + d ≤ T.length e) (hne : e' ≠ e)
    (o : Fin (T.length e' - 1)) :
    prin T.graph (moveScript T e q r d) (T.interiorVertex e' o) = 0 := by
  unfold moveScript
  rw [T.prin_interiorVertex_eq_slopeDifference
    (T.isStepSlope_slotValueScript (moveValue_compatible T e q r d hdq hrL)) e' o]
  simp [moveValue, hne]

/-- The Laplacian of the move script inside slot `e`. -/
theorem prin_moveScript_interior_same (T : Spec n p) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (o : Fin (T.length e - 1)) :
    prin T.graph (moveScript T e q r d) (T.interiorVertex e o) =
      (if o.val + 1 = q - d then (1 : ℤ) else 0) - (if o.val + 1 = q then (1 : ℤ) else 0)
        - (if o.val + 1 = r then (1 : ℤ) else 0)
        + (if o.val + 1 = r + d then (1 : ℤ) else 0) := by
  unfold moveScript
  rw [T.prin_interiorVertex_eq_slopeDifference
    (T.isStepSlope_slotValueScript (moveValue_compatible T e q r d hdq hrL)) e o]
  simp only [moveValue, if_true]
  have h := trapVal_laplace q r d hd hdq hqr o.val
  have hrw : o.val + 1 + 1 = o.val + 2 := rfl
  rw [hrw]
  linarith [h]

/-- At a core vertex the Laplacian of the move script is a sum of indicators, so a chip
is only ever gained there, never lost. -/
theorem prin_moveScript_core_nonneg (T : Spec n p) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (w : Fin n) :
    0 ≤ prin T.graph (moveScript T e q r d) (T.coreVertex w) := by
  unfold moveScript
  rw [T.prin_coreVertex_eq_endpointSum
    (T.isStepSlope_slotValueScript (moveValue_compatible T e q r d hdq hrL)) w]
  refine Finset.sum_nonneg ?_
  intro e' _
  by_cases hne : e' = e
  · subst hne
    have hlen : T.length e' - 1 + 1 = T.length e' := by
      have := T.length_pos e'
      omega
    have h0 : moveValue e' q r d e' 0 = 0 := by
      simp [moveValue, trapVal_zero q r d hdq]
    have hL : moveValue e' q r d e' (T.length e') = 0 := by
      simp [moveValue, trapVal_end q r d _ hrL]
    have h1 : moveValue e' q r d e' 1 = if q = d then (1 : ℤ) else 0 := by
      simp [moveValue, trapVal_one q r d hd hdq hqr]
    have hp : moveValue e' q r d e' (T.length e' - 1)
        = if r + d = T.length e' then (1 : ℤ) else 0 := by
      simp [moveValue, trapVal_pred q r d _ hd hqr hrL]
    rw [hlen, h0, hL, h1, hp]
    split_ifs <;> simp
  · simp [moveValue, hne]

/-! ## One interior move at the level of divisors -/

/-- The divisor after one interior move. -/
def moved (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ) : CFDiv T.graph :=
  D + prin T.graph (moveScript T e q r d)

/-- One interior move is a linear equivalence. -/
theorem linear_equiv_moved (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ) :
    linear_equiv T.graph D (moved T D e q r d) := by
  unfold linear_equiv moved
  have hrw : D + prin T.graph (moveScript T e q r d) - D
      = prin T.graph (moveScript T e q r d) := by abel
  rw [hrw]
  exact (principal_iff_eq_prin T.graph _).mpr ⟨moveScript T e q r d, rfl⟩

/-- An interior move never decreases the chip count at a core vertex. -/
theorem moved_core (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e) (w : Fin n) :
    D (T.coreVertex w) ≤ moved T D e q r d (T.coreVertex w) := by
  have := prin_moveScript_core_nonneg T e q r d hd hdq hqr hrL w
  simp only [moved, Pi.add_apply]
  omega

/-- An interior move on slot `e` leaves every other slot untouched. -/
theorem moved_interior_other (T : Spec n p) (D : CFDiv T.graph) (e e' : Fin p) (q r d : ℕ)
    (hdq : d ≤ q) (hrL : r + d ≤ T.length e) (hne : e' ≠ e)
    (o : Fin (T.length e' - 1)) :
    moved T D e q r d (T.interiorVertex e' o) = D (T.interiorVertex e' o) := by
  have := prin_moveScript_interior_other T e e' q r d hdq hrL hne o
  simp only [moved, Pi.add_apply, this, add_zero]

/-- The effect of an interior move inside its own slot. -/
theorem moved_interior_same (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (o : Fin (T.length e - 1)) :
    moved T D e q r d (T.interiorVertex e o) = D (T.interiorVertex e o)
      + ((if o.val + 1 = q - d then (1 : ℤ) else 0) - (if o.val + 1 = q then (1 : ℤ) else 0)
        - (if o.val + 1 = r then (1 : ℤ) else 0)
        + (if o.val + 1 = r + d then (1 : ℤ) else 0)) := by
  have := prin_moveScript_interior_same T e q r d hd hdq hqr hrL o
  simp only [moved, Pi.add_apply, this]

/-- An interior move preserves effectivity, provided the two chips it moves are there. -/
theorem effective_moved (T : Spec n p) (D : CFDiv T.graph) (hDeff : effective D)
    (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (hchips : ∀ o : Fin (T.length e - 1),
      (if o.val + 1 = q then (1 : ℤ) else 0) + (if o.val + 1 = r then (1 : ℤ) else 0)
        ≤ D (T.interiorVertex e o)) :
    effective (moved T D e q r d) := by
  intro y
  rcases y with w | ⟨e', o⟩
  · have h1 := moved_core T D e q r d hd hdq hqr hrL w
    have h2 := hDeff (T.coreVertex w)
    show moved T D e q r d (T.coreVertex w) ≥ 0
    omega
  · by_cases hne : e' = e
    · subst hne
      show moved T D e' q r d (T.interiorVertex e' o) ≥ 0
      rw [moved_interior_same T D e' q r d hd hdq hqr hrL o]
      have h := hchips o
      split_ifs at h ⊢ <;> omega
    · show moved T D e q r d (T.interiorVertex e' o) ≥ 0
      rw [moved_interior_other T D e e' q r d hdq hrL hne o]
      exact hDeff _

/-! ## Interior moments and counts -/

/-- The offset-weighted sum of the interior chips on one slot. -/
def slotMoment (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) : ℤ :=
  ∑ o : Fin (T.length e - 1), D (T.interiorVertex e o) * ((o.val + 1 : ℕ) : ℤ)

/-- The number of interior chips on one slot. -/
def slotCount (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) : ℤ :=
  ∑ o : Fin (T.length e - 1), D (T.interiorVertex e o)

/-- The number of interior chips on the whole subdivision. -/
def interiorTotal (T : Spec n p) (D : CFDiv T.graph) : ℤ :=
  ∑ e : Fin p, slotCount T D e

/-- A sum over interior offsets of an indicator at one path position. -/
theorem sum_ite_succ {N : ℕ} (t : ℕ) (f : ℕ → ℤ) :
    (∑ o : Fin N, if o.val + 1 = t then f (o.val + 1) else 0)
      = if 1 ≤ t ∧ t ≤ N then f t else 0 := by
  classical
  by_cases h : 1 ≤ t ∧ t ≤ N
  · obtain ⟨h1, h2⟩ := h
    rw [if_pos ⟨h1, h2⟩]
    have hlt : t - 1 < N := by omega
    have hmk : (⟨t - 1, hlt⟩ : Fin N).val = t - 1 := rfl
    refine (Finset.sum_eq_single (⟨t - 1, hlt⟩ : Fin N) ?_ ?_).trans ?_
    · intro o _ hone
      rw [if_neg]
      intro hcon
      exact hone (Fin.ext (by rw [hmk]; omega))
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · rw [if_pos (by rw [hmk]; omega)]
      congr 1
      rw [hmk]
      omega
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro o _
    rw [if_neg]
    intro hcon
    exact h ⟨by omega, by have := o.isLt; omega⟩

/-- The change of any offset-weighted interior sum under one move. -/
theorem sum_weighted_moved (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (f : ℕ → ℤ) :
    (∑ o : Fin (T.length e - 1),
        moved T D e q r d (T.interiorVertex e o) * f (o.val + 1))
      = (∑ o : Fin (T.length e - 1), D (T.interiorVertex e o) * f (o.val + 1))
        + ((if 1 ≤ q - d ∧ q - d ≤ T.length e - 1 then f (q - d) else 0)
            - (if 1 ≤ q ∧ q ≤ T.length e - 1 then f q else 0)
            - (if 1 ≤ r ∧ r ≤ T.length e - 1 then f r else 0)
            + (if 1 ≤ r + d ∧ r + d ≤ T.length e - 1 then f (r + d) else 0)) := by
  classical
  have hterm : ∀ o : Fin (T.length e - 1),
      moved T D e q r d (T.interiorVertex e o) * f (o.val + 1)
        = D (T.interiorVertex e o) * f (o.val + 1)
          + ((if o.val + 1 = q - d then f (o.val + 1) else 0)
              - (if o.val + 1 = q then f (o.val + 1) else 0)
              - (if o.val + 1 = r then f (o.val + 1) else 0)
              + (if o.val + 1 = r + d then f (o.val + 1) else 0)) := by
    intro o
    rw [moved_interior_same T D e q r d hd hdq hqr hrL o]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun o _ => hterm o), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_ite_succ, sum_ite_succ, sum_ite_succ, sum_ite_succ]

/-- The change of the slot moment under one move. -/
theorem slotMoment_moved (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (h1q : 1 ≤ q) (hrlt : r ≤ T.length e - 1) :
    slotMoment T (moved T D e q r d) e = slotMoment T D e
      + ((if 1 ≤ q - d ∧ q - d ≤ T.length e - 1 then ((q - d : ℕ) : ℤ) else 0)
          - (q : ℤ) - (r : ℤ)
          + (if 1 ≤ r + d ∧ r + d ≤ T.length e - 1 then ((r + d : ℕ) : ℤ) else 0)) := by
  have h := sum_weighted_moved T D e q r d hd hdq hqr hrL (fun k => (k : ℤ))
  have hq : (if 1 ≤ q ∧ q ≤ T.length e - 1 then (q : ℤ) else 0) = (q : ℤ) :=
    if_pos ⟨h1q, by omega⟩
  have hr : (if 1 ≤ r ∧ r ≤ T.length e - 1 then (r : ℤ) else 0) = (r : ℤ) :=
    if_pos ⟨by omega, hrlt⟩
  simp only [slotMoment]
  rw [h, hq, hr]

/-- The change of the interior chip count under one move. -/
theorem slotCount_moved (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (h1q : 1 ≤ q) (hrlt : r ≤ T.length e - 1) :
    slotCount T (moved T D e q r d) e = slotCount T D e
      + ((if 1 ≤ q - d ∧ q - d ≤ T.length e - 1 then (1 : ℤ) else 0) - 1 - 1
          + (if 1 ≤ r + d ∧ r + d ≤ T.length e - 1 then (1 : ℤ) else 0)) := by
  have h := sum_weighted_moved T D e q r d hd hdq hqr hrL (fun _ => (1 : ℤ))
  simp only [mul_one] at h
  have hq : (if 1 ≤ q ∧ q ≤ T.length e - 1 then (1 : ℤ) else 0) = (1 : ℤ) :=
    if_pos ⟨h1q, by omega⟩
  have hr : (if 1 ≤ r ∧ r ≤ T.length e - 1 then (1 : ℤ) else 0) = (1 : ℤ) :=
    if_pos ⟨by omega, hrlt⟩
  simp only [slotCount]
  rw [h, hq, hr]

/-- Other slots keep their moment. -/
theorem slotMoment_moved_other (T : Spec n p) (D : CFDiv T.graph) (e e' : Fin p) (q r d : ℕ)
    (hdq : d ≤ q) (hrL : r + d ≤ T.length e) (hne : e' ≠ e) :
    slotMoment T (moved T D e q r d) e' = slotMoment T D e' :=
  Finset.sum_congr rfl (fun o _ => by
    rw [moved_interior_other T D e e' q r d hdq hrL hne o])

/-- Other slots keep their chip count. -/
theorem slotCount_moved_other (T : Spec n p) (D : CFDiv T.graph) (e e' : Fin p) (q r d : ℕ)
    (hdq : d ≤ q) (hrL : r + d ≤ T.length e) (hne : e' ≠ e) :
    slotCount T (moved T D e q r d) e' = slotCount T D e' :=
  Finset.sum_congr rfl (fun o _ => by
    rw [moved_interior_other T D e e' q r d hdq hrL hne o])

/-- The slot moment changes by `0` or by `-(T.length e)`, so divisibility by any `m`
dividing the slot length is preserved. -/
theorem dvd_slotMoment_moved (T : Spec n p) (D : CFDiv T.graph) (m : ℕ) (e : Fin p)
    (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (h1q : 1 ≤ q) (hrlt : r ≤ T.length e - 1) (hmL : m ∣ T.length e)
    (hmom : (m : ℤ) ∣ slotMoment T D e) :
    (m : ℤ) ∣ slotMoment T (moved T D e q r d) e := by
  rw [slotMoment_moved T D e q r d hd hdq hqr hrL h1q hrlt]
  have hcases :
      ((if 1 ≤ q - d ∧ q - d ≤ T.length e - 1 then ((q - d : ℕ) : ℤ) else 0)
        - (q : ℤ) - (r : ℤ)
        + (if 1 ≤ r + d ∧ r + d ≤ T.length e - 1 then ((r + d : ℕ) : ℤ) else 0))
      = 0 ∨
      ((if 1 ≤ q - d ∧ q - d ≤ T.length e - 1 then ((q - d : ℕ) : ℤ) else 0)
        - (q : ℤ) - (r : ℤ)
        + (if 1 ≤ r + d ∧ r + d ≤ T.length e - 1 then ((r + d : ℕ) : ℤ) else 0))
      = -((T.length e : ℕ) : ℤ) := by
    split_ifs <;> omega
  rcases hcases with hz | hz
  · rw [hz, add_zero]; exact hmom
  · rw [hz]
    exact dvd_add hmom (dvd_neg.mpr (Int.natCast_dvd_natCast.mpr hmL))

/-- When `d = min q (T.length e - r)` at least one of the two moved chips reaches an
endpoint, so the interior chip count of the slot drops. -/
theorem slotCount_moved_le (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (h1q : 1 ≤ q) (hrlt : r ≤ T.length e - 1)
    (hdmin : q = d ∨ r + d = T.length e) :
    slotCount T (moved T D e q r d) e ≤ slotCount T D e - 1 := by
  rw [slotCount_moved T D e q r d hd hdq hqr hrL h1q hrlt]
  rcases hdmin with h | h <;> split_ifs <;> omega

/-- One move removes at least one chip from the interior. -/
theorem interiorTotal_moved_le (T : Spec n p) (D : CFDiv T.graph) (e : Fin p) (q r d : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (hqr : q ≤ r) (hrL : r + d ≤ T.length e)
    (h1q : 1 ≤ q) (hrlt : r ≤ T.length e - 1)
    (hdmin : q = d ∨ r + d = T.length e) :
    interiorTotal T (moved T D e q r d) ≤ interiorTotal T D - 1 := by
  classical
  have hbound : ∀ e' : Fin p, slotCount T (moved T D e q r d) e'
      ≤ slotCount T D e' + (if e' = e then (-1 : ℤ) else 0) := by
    intro e'
    by_cases hne : e' = e
    · subst hne
      rw [if_pos rfl]
      have := slotCount_moved_le T D e' q r d hd hdq hqr hrL h1q hrlt hdmin
      omega
    · rw [if_neg hne, add_zero, slotCount_moved_other T D e e' q r d hdq hrL hne]
  have hsum : (∑ e' : Fin p, slotCount T (moved T D e q r d) e')
      ≤ ∑ e' : Fin p, (slotCount T D e' + (if e' = e then (-1 : ℤ) else 0)) :=
    Finset.sum_le_sum (fun e' _ => hbound e')
  have hone : (∑ e' : Fin p, (if e' = e then (-1 : ℤ) else 0)) = -1 := by simp
  have hsplit : (∑ e' : Fin p, (slotCount T D e' + (if e' = e then (-1 : ℤ) else 0)))
      = (∑ e' : Fin p, slotCount T D e') - 1 := by
    rw [Finset.sum_add_distrib, hone]
    ring
  rw [hsplit] at hsum
  simpa [interiorTotal] using hsum

/-- A slot carrying at least two interior chips has two offsets that can be pushed apart. -/
theorem exists_two_chips (T : Spec n p) (D : CFDiv T.graph) (hDeff : effective D)
    (e : Fin p) (h2 : 2 ≤ slotCount T D e) :
    ∃ q r : ℕ, 1 ≤ q ∧ q ≤ r ∧ r ≤ T.length e - 1 ∧
      ∀ o : Fin (T.length e - 1),
        (if o.val + 1 = q then (1 : ℤ) else 0) + (if o.val + 1 = r then (1 : ℤ) else 0)
          ≤ D (T.interiorVertex e o) := by
  classical
  set S : Finset (Fin (T.length e - 1)) :=
    Finset.univ.filter (fun o => 1 ≤ D (T.interiorVertex e o)) with hS
  have hmemS : ∀ o : Fin (T.length e - 1), o ∈ S ↔ 1 ≤ D (T.interiorVertex e o) := by
    intro o; simp [hS]
  have hzero : ∀ o : Fin (T.length e - 1), o ∉ S → D (T.interiorVertex e o) = 0 := by
    intro o ho
    have h1 := hDeff (T.interiorVertex e o)
    have h2 : ¬ (1 ≤ D (T.interiorVertex e o)) := fun hc => ho ((hmemS o).mpr hc)
    omega
  have hsumS : slotCount T D e = ∑ o ∈ S, D (T.interiorVertex e o) := by
    rw [slotCount]
    exact (Finset.sum_subset (Finset.subset_univ S)
      (fun o _ ho => hzero o ho)).symm
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hc | hc
    · rw [hc, Finset.sum_empty] at hsumS; omega
    · exact hc
  set a := S.min' hSne with ha
  set b := S.max' hSne with hb
  have haS : a ∈ S := S.min'_mem hSne
  have hbS : b ∈ S := S.max'_mem hSne
  have hab : a.val ≤ b.val := S.min'_le b hbS
  refine ⟨a.val + 1, b.val + 1, by omega, by omega, by have := b.isLt; omega, ?_⟩
  intro o
  by_cases hoa : o.val + 1 = a.val + 1
  · have hoa' : o = a := Fin.ext (by omega)
    by_cases hob : o.val + 1 = b.val + 1
    · have hob' : o = b := Fin.ext (by omega)
      have habeq : a = b := hoa' ▸ hob'
      have hsub : S ⊆ {a} := by
        intro x hx
        have h1 : a ≤ x := S.min'_le x hx
        have h2 : x ≤ b := S.le_max' x hx
        rw [← habeq] at h2
        exact Finset.mem_singleton.mpr (le_antisymm h2 h1)
      have hSeq : S = {a} :=
        Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr haS)
      rw [hSeq, Finset.sum_singleton] at hsumS
      rw [if_pos hoa, if_pos hob, hoa']
      omega
    · rw [if_pos hoa, if_neg hob, hoa']
      have := (hmemS a).mp haS
      omega
  · by_cases hob : o.val + 1 = b.val + 1
    · have hob' : o = b := Fin.ext (by omega)
      rw [if_neg hoa, if_pos hob, hob']
      have := (hmemS b).mp hbS
      omega
    · rw [if_neg hoa, if_neg hob]
      have := hDeff (T.interiorVertex e o)
      omega

/-! ## The interior-firing lemma -/

/-- When every slot carries at most one interior chip, the moment hypothesis says
exactly that the surviving chips are on the grid. -/
theorem onGrid_of_slotCount_le_one (T : Spec n p) (m : ℕ) (D : CFDiv T.graph)
    (hDeff : effective D)
    (hmom : ∀ e, (m : ℤ) ∣ slotMoment T D e)
    (hcount : ∀ e, slotCount T D e ≤ 1) :
    ∀ y, D y ≠ 0 → OnGrid T m y := by
  classical
  intro y hy
  rcases y with w | ⟨e, o⟩
  · trivial
  · show m ∣ (o.val + 1)
    have hy' : D (T.interiorVertex e o) ≠ 0 := hy
    have hnn := hDeff (T.interiorVertex e o)
    have hge : 1 ≤ D (T.interiorVertex e o) := by omega
    have hother : ∀ o' : Fin (T.length e - 1), o' ≠ o → D (T.interiorVertex e o') = 0 := by
      intro o' hne
      have h1 : D (T.interiorVertex e o)
          ≤ ∑ x ∈ Finset.univ.erase o', D (T.interiorVertex e x) :=
        Finset.single_le_sum (f := fun x => D (T.interiorVertex e x))
          (fun x _ => hDeff _) (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ o⟩)
      have h2 : slotCount T D e
          = D (T.interiorVertex e o')
            + ∑ x ∈ Finset.univ.erase o', D (T.interiorVertex e x) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ o')).symm
      have h3 := hDeff (T.interiorVertex e o')
      have h4 := hcount e
      omega
    have hcs : slotCount T D e = D (T.interiorVertex e o) :=
      Finset.sum_eq_single o (fun o' _ hne => hother o' hne)
        (fun h => absurd (Finset.mem_univ o) h)
    have h4 := hcount e
    have hD1 : D (T.interiorVertex e o) = 1 := by omega
    have hmomval : slotMoment T D e = ((o.val + 1 : ℕ) : ℤ) := by
      rw [slotMoment,
        Finset.sum_eq_single o (fun o' _ hne => by rw [hother o' hne]; ring)
          (fun h => absurd (Finset.mem_univ o) h), hD1, one_mul]
    have hdvd := hmom e
    rw [hmomval] at hdvd
    exact_mod_cast hdvd

/-- The induction on the number of interior chips. -/
theorem exists_onGrid_aux (T : Spec n p) (m : ℕ) (hmL : ∀ e, m ∣ T.length e) :
    ∀ (N : ℕ) (D : CFDiv T.graph), effective D → (∀ e, (m : ℤ) ∣ slotMoment T D e) →
      interiorTotal T D ≤ (N : ℤ) →
      ∃ D' : CFDiv T.graph, linear_equiv T.graph D D' ∧ effective D' ∧
        (∀ y, D' y ≠ 0 → OnGrid T m y) := by
  classical
  intro N
  induction N with
  | zero =>
      intro D hDeff hmom hle
      refine ⟨D, linear_equiv.refl T.graph D, hDeff, ?_⟩
      refine onGrid_of_slotCount_le_one T m D hDeff hmom ?_
      intro e
      have hnn : ∀ e' : Fin p, 0 ≤ slotCount T D e' := fun e' =>
        Finset.sum_nonneg (fun o _ => hDeff _)
      have hsingle := Finset.single_le_sum (f := fun e' => slotCount T D e')
        (fun e' _ => hnn e') (Finset.mem_univ e)
      simp only [interiorTotal] at hle
      simp only [Nat.cast_zero] at hle
      omega
  | succ N ih =>
      intro D hDeff hmom hle
      by_cases hall : ∀ e, slotCount T D e ≤ 1
      · exact ⟨D, linear_equiv.refl T.graph D, hDeff,
          onGrid_of_slotCount_le_one T m D hDeff hmom hall⟩
      · push Not at hall
        obtain ⟨e, he⟩ := hall
        have h2 : 2 ≤ slotCount T D e := by omega
        obtain ⟨q, r, h1q, hqr, hrlt, hchips⟩ := exists_two_chips T D hDeff e h2
        have hLpos := T.length_pos e
        obtain ⟨d, hdef⟩ : ∃ d, d = min q (T.length e - r) := ⟨_, rfl⟩
        have hd : 1 ≤ d := by omega
        have hdq : d ≤ q := by omega
        have hrL : r + d ≤ T.length e := by omega
        have hdmin : q = d ∨ r + d = T.length e := by omega
        have heff' : effective (moved T D e q r d) :=
          effective_moved T D hDeff e q r d hd hdq hqr hrL hchips
        have hmom' : ∀ e', (m : ℤ) ∣ slotMoment T (moved T D e q r d) e' := by
          intro e'
          by_cases hne : e' = e
          · subst hne
            exact dvd_slotMoment_moved T D m e' q r d hd hdq hqr hrL h1q hrlt
              (hmL e') (hmom e')
          · rw [slotMoment_moved_other T D e e' q r d hdq hrL hne]
            exact hmom e'
        have hle' : interiorTotal T (moved T D e q r d) ≤ (N : ℤ) := by
          have := interiorTotal_moved_le T D e q r d hd hdq hqr hrL h1q hrlt hdmin
          have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
          rw [hcast] at hle
          omega
        obtain ⟨D'', hlin, heff'', hgrid⟩ := ih (moved T D e q r d) heff' hmom' hle'
        exact ⟨D'', linear_equiv.trans (linear_equiv_moved T D e q r d) hlin, heff'', hgrid⟩

/-- **The interior-firing lemma.** -/
theorem exists_onGrid (T : Spec n p) (m : ℕ) (hmL : ∀ e, m ∣ T.length e)
    (D : CFDiv T.graph) (hDeff : effective D)
    (hmom : ∀ e, (m : ℤ) ∣ slotMoment T D e) :
    ∃ D' : CFDiv T.graph, linear_equiv T.graph D D' ∧ effective D' ∧
      deg D' = deg D ∧ (∀ y, D' y ≠ 0 → OnGrid T m y) := by
  obtain ⟨D', hlin, heff, hgrid⟩ :=
    exists_onGrid_aux T m hmL (interiorTotal T D).toNat D hDeff hmom
      (Int.self_le_toNat _)
  exact ⟨D', hlin, heff, (linear_equiv_preserves_deg T.graph D D' hlin).symm, hgrid⟩

/-- The interior-firing lemma, carrying a rank lower bound. -/
theorem exists_onGrid_rank (T : Spec n p) (m : ℕ) (hmL : ∀ e, m ∣ T.length e)
    (D : CFDiv T.graph) (hDeff : effective D)
    (hmom : ∀ e, (m : ℤ) ∣ slotMoment T D e) (r : ℤ) (hrank : rank T.graph D ≥ r) :
    ∃ D' : CFDiv T.graph, linear_equiv T.graph D D' ∧ effective D' ∧
      deg D' = deg D ∧ rank T.graph D' ≥ r ∧ (∀ y, D' y ≠ 0 → OnGrid T m y) := by
  obtain ⟨D', hlin, heff, hdeg, hgrid⟩ := exists_onGrid T m hmL D hDeff hmom
  refine ⟨D', hlin, heff, hdeg, ?_, hgrid⟩
  rw [← Utilities.rank_eq_of_linear_equiv T.graph hlin]
  exact hrank

/-- The interior-firing lemma on a scaled specification. -/
theorem exists_onGrid_scale (spec : Spec n p) (N : ℕ) (hN : 0 < N) (m : ℕ)
    (hdvd : m ∣ N) (D : CFDiv (spec.scale N hN).graph) (hDeff : effective D)
    (hmom : ∀ e, (m : ℤ) ∣ slotMoment (spec.scale N hN) D e)
    (r : ℤ) (hrank : rank (spec.scale N hN).graph D ≥ r) :
    ∃ D' : CFDiv (spec.scale N hN).graph,
      linear_equiv (spec.scale N hN).graph D D' ∧ effective D' ∧
        deg D' = deg D ∧ rank (spec.scale N hN).graph D' ≥ r ∧
        (∀ y, D' y ≠ 0 → OnGrid (spec.scale N hN) m y) :=
  exists_onGrid_rank (spec.scale N hN) m
    (fun e => by
      rw [Spec.scale_length]
      exact Dvd.dvd.mul_right hdvd _)
    D hDeff hmom r hrank

/-! ## The interior-firing lemma at a concrete small specification -/

/-- The fine interior vertex at offset `k + 1` of the six-fold segment. -/
def segmentFine (k : ℕ) (hk : k < 5) : (segmentSpec.scale 6 (by norm_num)).Vertex :=
  Sum.inr ⟨0, ⟨k, by simpa using hk⟩⟩

/-- Two chips at fine offsets `1` and `3` of the six-fold segment. -/
def segmentTwoChips : CFDiv (segmentSpec.scale 6 (by norm_num)).graph :=
  one_chip (segmentFine 0 (by norm_num)) + one_chip (segmentFine 2 (by norm_num))

theorem segmentTwoChips_effective : effective segmentTwoChips := fun v =>
  add_nonneg (eff_one_chip _ v) (eff_one_chip _ v)

theorem segmentTwoChips_deg : deg segmentTwoChips = 2 := by
  rw [segmentTwoChips, deg.map_add, deg_one_chip, deg_one_chip]
  norm_num

theorem segmentTwoChips_moment :
    slotMoment (segmentSpec.scale 6 (by norm_num)) segmentTwoChips 0 = 4 := by decide

/-- Two chips at fine offsets `1` and `3` of the six-fold segment have offset sum `4`,
so the interior-firing lemma moves them onto the `2`-grid. -/
example :
    ∃ D' : CFDiv (segmentSpec.scale 6 (by norm_num)).graph,
      linear_equiv (segmentSpec.scale 6 (by norm_num)).graph segmentTwoChips D' ∧
        effective D' ∧ deg D' = 2 ∧
        ∀ y, D' y ≠ 0 → OnGrid (segmentSpec.scale 6 (by norm_num)) 2 y := by
  have hlen : ∀ e : Fin 1, (2 : ℕ) ∣ (segmentSpec.scale 6 (by norm_num)).length e := by decide
  have hmom : ∀ e : Fin 1, ((2 : ℕ) : ℤ)
      ∣ slotMoment (segmentSpec.scale 6 (by norm_num)) segmentTwoChips e := by decide
  obtain ⟨D', hlin, heff, hdeg, hgrid⟩ :=
    exists_onGrid (segmentSpec.scale 6 (by norm_num)) 2 hlen segmentTwoChips
      segmentTwoChips_effective hmom
  exact ⟨D', hlin, heff, by rw [hdeg, segmentTwoChips_deg], hgrid⟩

end DraismaVargas.Count.InteriorFiring
