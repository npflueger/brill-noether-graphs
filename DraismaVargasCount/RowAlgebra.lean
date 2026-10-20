module

public import Mathlib.Tactic

@[expose] public section

/-!
# The arithmetic of a row laid along a slot

A row of `L` occurrences is laid along a slot of length `BL`. Occurrence `i` starts at the
integral offset `start i` and has length `len i`, with `start (i + 1) = start i + len i`. The
**row potential** `value v₀ slope start len pos` at a position `pos` is the potential `v₀` at the
row's start plus, for every occurrence, its slope times the clamped ramp `ramp` over its window.
A row is read along the slot in one of two orientations: `orient` reads a slot offset as a row
position and `offset` a row position as a slot offset.

Nothing here refers to a gluing datum or a member: these are the statements about numbers that
the pencil transports of `PencilTransportProducer`, of the typed frames of `DiagonalSecant` and
of the tripod rows of `GenusSixExistence` share.

## What is proved

* §1 `ramp`, `ramp_succ_sub`, `ramp_of_le`, `ramp_of_ge` and the telescoping `sum_window`, in the
  namespace `DraismaVargas.Count.PencilTransportProducer`.
* §2 the shapes `value`, `orient`, `offset`.
* §3 the prefix arithmetic: `start_le_start`, `start_add_len_le`, `sum_len`.
* §4 the row potential at the ends: `value_of_nonpos`, `value_of_ge`, and on a row of zero
  lengths, `value_of_len_zero`.
* §5 **`slot_sum`**, the window computation: the unit-step sum of the row potential along the
  slot, against any `δ`, is the sum over the occurrences of the slope times the difference of
  `δ` at the two ends of the occurrence.
* §6 the jump: **`exists_single_long`** (if no interior prefix lies strictly inside the slot, one
  occurrence carries the whole length), and `offset_pos`, `offset_lt`.
-/

/-! ## 1.  Ramps and their telescoping -/

namespace DraismaVargas.Count.PencilTransportProducer

section Ramp

/-- The clamped ramp `min (max (q - start) 0) len`. -/
def ramp (q start len : ℤ) : ℤ := min (max (q - start) 0) len

theorem ramp_succ_sub (o start len : ℤ) (hLen : 0 ≤ len) :
    ramp (o + 1) start len - ramp o start len =
      if start ≤ o ∧ o < start + len then 1 else 0 := by
  unfold ramp
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [max_eq_left (by omega), max_eq_left (by omega), min_eq_left (by omega),
      min_eq_left (by omega)]
    ring
  · rcases not_and_or.mp h with h1 | h2
    · push Not at h1
      rw [max_eq_right (by omega), max_eq_right (by omega)]
      simp
    · push Not at h2
      rw [min_eq_right (by omega), min_eq_right (by omega)]
      ring

theorem ramp_of_le (q start len : ℤ) (hLen : 0 ≤ len) (hq : q ≤ start) :
    ramp q start len = 0 := by
  unfold ramp
  rw [max_eq_right (by omega), min_eq_left hLen]

theorem ramp_of_ge (q start len : ℤ) (hLen : 0 ≤ len) (hq : start + len ≤ q) :
    ramp q start len = len := by
  unfold ramp
  rw [max_eq_left (by omega), min_eq_right (by omega)]

/-- **Telescoping along a window.**  Summing the step differences of `δ` over the
unit steps of the window `[start, start + len)` leaves its two ends. -/
theorem sum_window (δ : ℕ → ℤ) (total start len : ℕ) (h : start + len ≤ total) :
    (∑ o ∈ Finset.range total,
      (if start ≤ o ∧ o < start + len then (1 : ℤ) else 0) * (δ o - δ (o + 1))) =
      δ start - δ (start + len) := by
  induction len with
  | zero =>
      rw [Finset.sum_eq_zero]
      · simp
      · intro o _
        rw [ite_eq_right (by omega), zero_mul]
  | succ len ih =>
      have hSplit : ∀ o ∈ Finset.range total,
          (if start ≤ o ∧ o < start + (len + 1) then (1 : ℤ) else 0) * (δ o - δ (o + 1)) =
            (if start ≤ o ∧ o < start + len then (1 : ℤ) else 0) * (δ o - δ (o + 1)) +
              (if o = start + len then δ o - δ (o + 1) else 0) := by
        intro o _
        by_cases h1 : start ≤ o ∧ o < start + len
        · rw [ite_eq_left ⟨h1.1, by omega⟩, ite_eq_left h1, ite_eq_right (by omega)]
          ring
        · by_cases h2 : o = start + len
          · rw [ite_eq_left (by omega), ite_eq_right h1, ite_eq_left h2]
            ring
          · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]
            ring
      rw [Finset.sum_congr rfl hSplit, Finset.sum_add_distrib, ih (by omega),
        Finset.sum_ite_eq' (Finset.range total) (start + len)]
      rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
      rw [show start + (len + 1) = start + len + 1 by omega]
      ring

end Ramp

end DraismaVargas.Count.PencilTransportProducer

namespace DraismaVargas.Count.RowAlgebra

open DraismaVargas.Count.PencilTransportProducer (ramp ramp_succ_sub ramp_of_le ramp_of_ge
  sum_window)

/-! ## 2.  The row potential, and the two orientations -/

variable {L : ℕ}

/-- **The row potential** at the position `pos` of a row of `L` occurrences: the potential `v₀`
at the row's start plus, for every occurrence, its slope times the ramp over its window. -/
def value (v₀ : ℤ) (slope : Fin L → ℤ) (start : ℕ → ℕ) (len : Fin L → ℕ) (pos : ℤ) : ℤ :=
  v₀ + ∑ i : Fin L, slope i * ramp pos (start i) (len i)

/-- The row position of the slot offset `o`, reflected when the row runs against the slot. -/
def orient (rev : Bool) (BL o : ℕ) : ℤ := if rev then (BL : ℤ) - o else o

/-- The slot offset of the row position `x`, reflected when the row runs against the slot. -/
def offset (rev : Bool) (BL x : ℕ) : ℕ := if rev then BL - x else x

variable (v₀ : ℤ) (slope : Fin L → ℤ) (start : ℕ → ℕ) (len : Fin L → ℕ)

/-! ## 3.  Prefix arithmetic -/

section Prefix

variable {start len} (hSucc : ∀ i : Fin L, start (i.val + 1) = start i + len i)
include hSucc

/-- The prefixes increase along the row. -/
theorem start_le_start {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) : start i ≤ start j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have h : start (j + 1) = start j + len ⟨j, by omega⟩ := hSucc ⟨j, by omega⟩
      have := ih (by omega)
      omega

/-- Every occurrence ends by the full prefix. -/
theorem start_add_len_le (i : Fin L) : start i + len i ≤ start L := by
  rw [← hSucc]
  exact start_le_start hSucc (by omega) le_rfl

/-- The occurrence lengths add up to the full prefix. -/
theorem sum_len (h0 : start 0 = 0) : (∑ i : Fin L, (len i : ℤ)) = start L := by
  have h : ∀ i : Fin L, (len i : ℤ) = (start (i.val + 1) : ℤ) - (start i : ℤ) := by
    intro i
    rw [hSucc]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ h i]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (start (j + 1) : ℤ) - (start j : ℤ)),
    Finset.sum_range_sub (fun j ↦ (start j : ℤ)), h0]
  simp

end Prefix

/-! ## 4.  The row potential at the ends, and on a row of zero lengths -/

/-- Before the row's start the row potential is its value at the start. -/
theorem value_of_nonpos {pos : ℤ} (hpos : pos ≤ 0) : value v₀ slope start len pos = v₀ := by
  unfold value
  rw [Finset.sum_eq_zero, add_zero]
  intro i _
  have h0 : (0 : ℤ) ≤ start i := by positivity
  rw [ramp_of_le _ _ _ (by positivity) (by omega), mul_zero]

/-- After the full prefix the row potential is `v₁`, given that the slopes times the lengths
telescope to `v₁ - v₀` (`hTel`). -/
theorem value_of_ge {start : ℕ → ℕ} {len : Fin L → ℕ}
    (hSucc : ∀ i : Fin L, start (i.val + 1) = start i + len i)
    {v₁ : ℤ} (hTel : (∑ i : Fin L, slope i * (len i : ℤ)) = v₁ - v₀) {pos : ℤ}
    (hpos : (start L : ℤ) ≤ pos) : value v₀ slope start len pos = v₁ := by
  unfold value
  rw [Finset.sum_congr rfl fun i _ ↦ by
    rw [ramp_of_ge _ _ _ (by positivity) (by
      have := start_add_len_le hSucc i
      have : ((start i + len i : ℕ) : ℤ) ≤ pos := le_trans (by exact_mod_cast this) hpos
      push_cast at this
      omega)]]
  rw [hTel]
  ring

/-- On a row of zero lengths the row potential is constant. -/
theorem value_of_len_zero (hz : ∀ i, len i = 0) (pos : ℤ) :
    value v₀ slope start len pos = v₀ := by
  unfold value
  rw [Finset.sum_eq_zero, add_zero]
  intro i _
  rw [hz i, Nat.cast_zero]
  unfold ramp
  rw [min_eq_right (le_max_right _ _), mul_zero]

/-! ## 5.  The window computation -/

/-- **The window computation.**  The unit-step sum of the row potential along a slot of length
`BL`, read in either orientation, against the step differences of any `δ`, is the sum over the
occurrences of the slope times the difference of `δ` at the two (oriented) ends of the
occurrence.  The step slope of the potential is the sum of the slopes of the occurrences covering
that step, so each occurrence telescopes over its window (`sum_window`); reversal maps windows to
windows. -/
theorem slot_sum {start : ℕ → ℕ} {len : Fin L → ℕ}
    (hSucc : ∀ i : Fin L, start (i.val + 1) = start i + len i)
    (rev : Bool) (BL : ℕ) (hWin : ∀ i : Fin L, start i + len i ≤ BL) (δ : ℕ → ℤ) :
    (∑ o : Fin BL,
      (value v₀ slope start len (orient rev BL (o.val + 1)) -
          value v₀ slope start len (orient rev BL o.val)) *
        (δ o.val - δ (o.val + 1))) =
      ∑ i : Fin L, slope i *
        (δ (offset rev BL (start i)) - δ (offset rev BL (start (i.val + 1)))) := by
  unfold orient offset
  cases rev
  · simp only [Bool.false_eq_true, ite_false]
    have hDiff : ∀ o : ℕ,
        value v₀ slope start len ((o + 1 : ℕ) : ℤ) - value v₀ slope start len (o : ℤ) =
          ∑ i : Fin L, slope i *
            (if start i ≤ o ∧ o < start i + len i then (1 : ℤ) else 0) := by
      intro o
      unfold value
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_sub, show ((o + 1 : ℕ) : ℤ) = (o : ℤ) + 1 by push_cast; ring,
        ramp_succ_sub _ _ _ (by positivity)]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin L, slope i *
      (if start i ≤ o ∧ o < start i + len i then (1 : ℤ) else 0)) * (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_window δ _ _ _ (hWin i), hSucc]
  · simp only [ite_true]
    have hDiff : ∀ o : ℕ, o < BL →
        value v₀ slope start len ((BL : ℤ) - ((o + 1 : ℕ) : ℤ)) -
            value v₀ slope start len ((BL : ℤ) - (o : ℤ)) =
          ∑ i : Fin L, slope i *
            -(if BL - start i - len i ≤ o ∧ o < BL - start i then (1 : ℤ) else 0) := by
      intro o ho
      unfold value
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hStep := ramp_succ_sub ((BL : ℤ) - ((o + 1 : ℕ) : ℤ)) (start i) (len i)
        (by positivity)
      rw [show (BL : ℤ) - ((o + 1 : ℕ) : ℤ) + 1 = (BL : ℤ) - (o : ℤ) by push_cast; ring]
        at hStep
      rw [← mul_sub, ← neg_sub, hStep]
      have := hWin i
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val o.isLt]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin L, slope i *
      -(if BL - start i - len i ≤ o ∧ o < BL - start i then (1 : ℤ) else 0)) *
        (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hW := hWin i
    have hEq : ∀ o ∈ Finset.range BL,
        slope i * -(if BL - start i - len i ≤ o ∧ o < BL - start i then (1 : ℤ) else 0) *
            (δ o - δ (o + 1)) =
          -slope i * ((if BL - start i - len i ≤ o ∧ o < BL - start i - len i + len i
              then (1 : ℤ) else 0) * (δ o - δ (o + 1))) := by
      intro o _
      have hIff : (o < BL - start i) ↔ (o < BL - start i - len i + len i) := by omega
      simp only [hIff]
      ring
    rw [Finset.sum_congr rfl hEq, ← Finset.mul_sum,
      sum_window δ BL (BL - start i - len i) (len i) (by omega), hSucc,
      show BL - start i - len i + len i = BL - start i by omega,
      show BL - (start i + len i) = BL - start i - len i by omega]
    ring

/-! ## 6.  The jump -/

/-- **The jump.**  If no prefix strictly inside the row lies strictly inside the slot, the first
prefix to leave `0` jumps to the full length: one occurrence carries the whole length and every
other has length zero. -/
theorem exists_single_long {start : ℕ → ℕ} {len : Fin L → ℕ}
    (hSucc : ∀ i : Fin L, start (i.val + 1) = start i + len i)
    (h0 : start 0 = 0) {BL : ℕ} (hFull : start L = BL) (hPos : 0 < BL)
    (hNo : ∀ j, 0 < j → j < L → start j = 0 ∨ start j = BL) :
    ∃ i0 : Fin L, len i0 = BL ∧ ∀ i, i ≠ i0 → len i = 0 := by
  classical
  have hEx : ∃ j, 1 ≤ start j := ⟨L, by omega⟩
  have hJ : 1 ≤ start (Nat.find hEx) := Nat.find_spec hEx
  have hJpos : 0 < Nat.find hEx := by
    by_contra h
    rw [show Nat.find hEx = 0 by omega, h0] at hJ
    omega
  have hJle : Nat.find hEx ≤ L := Nat.find_min' hEx (by omega)
  have hJm : start (Nat.find hEx - 1) = 0 := by
    have := Nat.find_min hEx (show Nat.find hEx - 1 < Nat.find hEx by omega)
    omega
  have hJv : start (Nat.find hEx) = BL := by
    rcases Nat.lt_or_ge (Nat.find hEx) L with h | h
    · rcases hNo _ hJpos h with h' | h' <;> omega
    · rw [show Nat.find hEx = L by omega, hFull]
  set i0 : Fin L := ⟨Nat.find hEx - 1, by omega⟩ with hi0
  have hL0 : len i0 = BL := by
    have h : start (Nat.find hEx - 1 + 1) = start (Nat.find hEx - 1) + len i0 := hSucc i0
    rw [show Nat.find hEx - 1 + 1 = Nat.find hEx by omega] at h
    omega
  refine ⟨i0, hL0, fun i hi ↦ ?_⟩
  have hSum := sum_len hSucc h0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hL0, hFull] at hSum
  have hz : (∑ x ∈ Finset.univ.erase i0, (len x : ℤ)) = 0 := by linarith
  have hnn : ∀ x ∈ Finset.univ.erase i0, (0 : ℤ) ≤ len x := fun _ _ ↦ by positivity
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i
    (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact_mod_cast this

/-- A row position strictly inside the slot is a slot offset strictly past the start. -/
theorem offset_pos {rev : Bool} {BL x : ℕ} (hx : 0 < x) (hxB : x < BL) :
    0 < offset rev BL x := by
  unfold offset
  split_ifs <;> omega

/-- A row position strictly inside the slot is a slot offset strictly before the end. -/
theorem offset_lt {rev : Bool} {BL x : ℕ} (hx : 0 < x) (hxB : x < BL) :
    offset rev BL x < BL := by
  unfold offset
  split_ifs <;> omega

end DraismaVargas.Count.RowAlgebra
