module

public import Utilities.Gluing.HandleGraph

@[expose] public section

/-!
# Spreading the chips on a handle

The spreading step of the long-handle lemma (`Utilities/Gluing/LongHandle.lean`; step (c) of
the prose proof in `Research/long-handle-lemma.md`). Two chips on the handle, at positions
`a ≤ c`, can be moved apart: firing the handle vertices at positions `a, …, c` moves one chip
from `a` to `a - 1` and one from `c` to `c + 1`, whatever lies strictly between. Position `0` is
`x` and position `m + 2` is `y`, so a chip can leave the handle at either end. The sum of the two
positions does not change.

Repeating this, every effective divisor is linearly equivalent to an effective divisor with at
most one chip left on the handle. The chips that left are recorded: `α` of them at `x` and `β` at
`y`, and the moment of the handle chips, counting each chip that left at `y` as `m + 2`, is
unchanged.

The proof works with the indices `i ≤ j : Fin (m + 1)` of the two chips (positions `i + 1` and
`j + 1`) and the script `handleBlockScript i j` that fires `q_i, …, q_j`. Termination is by the
potential `handlePotential`, which weights a chip at position `p` by `p * (m + 2 - p)` and drops by
at least two in every step.

Headline: `exists_collapsed_representative`.
-/

namespace Utilities

universe u

open Finset

/-! ## Generic facts -/

/-- Removing a chip from a vertex that holds one keeps a divisor effective. A local copy of
`Utilities.effective_sub_one_chip` (`Utilities/Foundations/RankDeterminingSet.lean`), kept here
so as not to import that module. -/
private theorem effective_sub_one_chip_aux {Γ : CFGraph.{u}} {D : CFDiv Γ} {v : Γ.V}
    (hD : effective D) (hv : 1 ≤ D v) : effective (D - one_chip v) := by
  intro w
  rw [Pi.sub_apply]
  by_cases h : w = v
  · rw [h, one_chip_apply_v]
    omega
  · rw [one_chip_apply_other' v w h]
    have := hD w
    omega

/-- A sum over `Fin (m + 1)` that picks out the index with value `t`. -/
theorem sum_fin_ite_val_eq (m t : ℕ) (w : ℕ → ℤ) :
    ∑ k : Fin (m + 1), (if (k : ℕ) = t then w k else 0) = if t ≤ m then w t else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k = t then w k else 0) (m + 1),
    Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_add_one_iff]

/-- A sum over `Fin (m + 1)` that picks out the index with value `t - 1`. -/
theorem sum_fin_ite_succ_val_eq (m t : ℕ) (w : ℕ → ℤ) :
    ∑ k : Fin (m + 1), (if (k : ℕ) + 1 = t then w k else 0) =
      if 1 ≤ t ∧ t ≤ m + 1 then w (t - 1) else 0 := by
  rcases t with _ | s
  · simp
  · simp only [Nat.add_right_cancel_iff]
    rw [sum_fin_ite_val_eq]
    by_cases h : s ≤ m
    · rw [ite_eq_left h, ite_eq_left (by omega), Nat.add_sub_cancel]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

variable {G : CFGraph.{u}} {x y : G.V} {m : ℕ}

/-! ## Weighted counts of the handle chips -/

/-- The chips on the handle weighted by a function of their index: `∑ w i * D (q_i)`. -/
def handleWeighted (w : ℕ → ℤ) (D : CFDiv (handleGraph G x y m)) : ℤ :=
  ∑ i : Fin (m + 1), w i * D (handleInr i)

/-- A weighted count is additive. -/
theorem handleWeighted_add (w : ℕ → ℤ) (D D' : CFDiv (handleGraph G x y m)) :
    handleWeighted w (D + D') = handleWeighted w D + handleWeighted w D' := by
  simp only [handleWeighted, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The number of handle chips is the weighted count with weight one. -/
theorem handleInterior_eq_handleWeighted (D : CFDiv (handleGraph G x y m)) :
    handleInterior D = handleWeighted (fun _ => 1) D := by
  simp only [handleInterior, handleWeighted, one_mul]

/-- The moment is the weighted count with weight `i + 1`. -/
theorem handleMoment_eq_handleWeighted (D : CFDiv (handleGraph G x y m)) :
    handleMoment D = handleWeighted (fun k => (k : ℤ) + 1) D := rfl

/-- The weight of index `k` (position `k + 1`) in the potential: `(k + 1) * (m + 1 - k)`. -/
def handleWeight (m k : ℕ) : ℤ := ((k : ℤ) + 1) * ((m : ℤ) + 1 - k)

/-- The potential of the handle chips: a chip at position `p` counts `p * (m + 2 - p)`. -/
def handlePotential (D : CFDiv (handleGraph G x y m)) : ℤ :=
  handleWeighted (handleWeight m) D

/-- An effective divisor has nonnegative potential. -/
theorem handlePotential_nonneg {D : CFDiv (handleGraph G x y m)} (hD : effective D) :
    0 ≤ handlePotential D := by
  unfold handlePotential handleWeighted handleWeight
  refine Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg ?_ ?_) (hD _)
  · positivity
  · have := k.isLt
    omega

/-- Removing a handle chip lowers the number of handle chips by one. -/
theorem handleInterior_sub_one_chip (D : CFDiv (handleGraph G x y m)) (k : Fin (m + 1)) :
    handleInterior (D - one_chip (handleInr k)) = handleInterior D - 1 := by
  simp only [handleInterior, Pi.sub_apply, Finset.sum_sub_distrib,
    one_chip_handleInr_apply_handleInr, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A divisor with a handle chip has a handle vertex carrying a chip. -/
theorem exists_handle_chip {D : CFDiv (handleGraph G x y m)} (h : 1 ≤ handleInterior D) :
    ∃ k : Fin (m + 1), 1 ≤ D (handleInr k) := by
  by_contra hne
  simp only [not_exists, not_le] at hne
  have : handleInterior D ≤ 0 := Finset.sum_nonpos fun k _ => by
    have := hne k
    omega
  omega

/-- An effective divisor with at least two handle chips has two of them, at indices `i ≤ j`
(on one vertex if `i = j`). -/
theorem exists_two_handle_chips {D : CFDiv (handleGraph G x y m)} (hD : effective D)
    (h : 2 ≤ handleInterior D) :
    ∃ i j : Fin (m + 1), i ≤ j ∧
      effective (D - one_chip (handleInr i) - one_chip (handleInr j)) := by
  obtain ⟨k₁, hk₁⟩ := exists_handle_chip (D := D) (by omega)
  have hD₁ := effective_sub_one_chip_aux hD hk₁
  have hI : 1 ≤ handleInterior (D - one_chip (handleInr k₁)) := by
    rw [handleInterior_sub_one_chip]
    omega
  obtain ⟨k₂, hk₂⟩ := exists_handle_chip hI
  have hD₂ := effective_sub_one_chip_aux hD₁ hk₂
  rcases le_total k₁ k₂ with h12 | h21
  · exact ⟨k₁, k₂, h12, hD₂⟩
  · exact ⟨k₂, k₁, h21, by rwa [sub_right_comm] at hD₂⟩

/-! ## Firing a block of the handle -/

/-- The script that fires the handle vertices `q_i, …, q_j` once each. -/
def handleBlockScript (i j : Fin (m + 1)) : firing_script (handleGraph G x y m) :=
  indicator_script (handleGraph G x y m) ((Finset.Icc i j).image handleInr)

/-- The block script vanishes on the old vertices. -/
theorem handleBlockScript_inl (i j : Fin (m + 1)) (b : G.V) :
    handleBlockScript (G := G) (x := x) (y := y) i j (handleInl b) = 0 := by
  simp only [handleBlockScript, indicator_script]
  rw [ite_eq_right]
  intro hb
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hb
  exact handleInl_ne_handleInr b k hk.symm

/-- The block script on the handle is the indicator of `[i, j]`. -/
theorem handleBlockScript_inr (i j k : Fin (m + 1)) :
    handleBlockScript (G := G) (x := x) (y := y) i j (handleInr k) =
      if i ≤ k ∧ k ≤ j then 1 else 0 := by
  simp only [handleBlockScript, indicator_script, handleInr_injective.mem_finset_image,
    Finset.mem_Icc]

/-- The block script at position `p` is the indicator of the positions `[i + 1, j + 1]`. -/
theorem handleBlockScript_point (i j : Fin (m + 1)) (p : ℕ) (hp : p ≤ m + 2) :
    handleBlockScript i j (handlePoint G x y m p) =
      if (i : ℕ) + 1 ≤ p ∧ p ≤ (j : ℕ) + 1 then 1 else 0 := by
  have hj := j.isLt
  rcases Nat.lt_or_ge (m + 1) p with h | h
  · obtain rfl : p = m + 2 := by omega
    rw [handlePoint_last, handleBlockScript_inl, ite_eq_right]
    omega
  · rcases p with _ | q
    · rw [handlePoint_zero, handleBlockScript_inl, ite_eq_right]
      omega
    · have hq : q < m + 1 := by omega
      have e := handlePoint_succ G x y m ⟨q, hq⟩
      simp only at e
      rw [e, handleBlockScript_inr]
      simp only [Fin.le_iff_val_le_val]
      split_ifs <;> omega

/-- The principal divisor of the block script at an old vertex: a chip arrives at `x` when the
block starts at `q_0`, and at `y` when it ends at `q_m`. -/
theorem prin_handleBlockScript_inl (i j : Fin (m + 1)) (b : G.V) :
    prin (handleGraph G x y m) (handleBlockScript i j) (handleInl b) =
      (if b = x then (if (i : ℕ) = 0 then 1 else 0) else 0) +
        (if b = y then (if (j : ℕ) = m then 1 else 0) else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [prin_handleGraph_inl]
  have h0 : (fun b => handleBlockScript (G := G) (x := x) (y := y) i j (handleInl b)) =
      fun _ => 0 := funext fun b => handleBlockScript_inl i j b
  have h1 : handleBlockScript i j (handlePoint G x y m 1) -
      handleBlockScript i j (handlePoint G x y m 0) = if (i : ℕ) = 0 then 1 else 0 := by
    rw [handleBlockScript_point i j 1 (by omega), handleBlockScript_point i j 0 (by omega)]
    split_ifs <;> omega
  have h2 : handleBlockScript i j (handlePoint G x y m (m + 1)) -
      handleBlockScript i j (handlePoint G x y m (m + 2)) = if (j : ℕ) = m then 1 else 0 := by
    rw [handleBlockScript_point i j (m + 1) (by omega),
      handleBlockScript_point i j (m + 2) le_rfl]
    split_ifs <;> omega
  rw [h0, h1, h2, prin_const, Pi.zero_apply, zero_add]

/-- The principal divisor of the block script on the handle: a chip arrives at the vertex before
`q_i` and at the vertex after `q_j`, and one chip leaves each of `q_i` and `q_j`. -/
theorem prin_handleBlockScript_inr (i j : Fin (m + 1)) (hij : i ≤ j) (k : Fin (m + 1)) :
    prin (handleGraph G x y m) (handleBlockScript i j) (handleInr k) =
      (if (k : ℕ) + 1 = i then 1 else 0) + (if (k : ℕ) = (j : ℕ) + 1 then 1 else 0) -
        (if (k : ℕ) = i then 1 else 0) - (if (k : ℕ) = j then 1 else 0) := by
  have hk : (k : ℕ) ≤ m := Nat.lt_succ_iff.mp k.isLt
  have hij' : (i : ℕ) ≤ j := hij
  rw [← handlePoint_succ G x y m k, prin_handleGraph_point G x y m _ hk,
    handleBlockScript_point i j (k : ℕ) (by omega),
    handleBlockScript_point i j ((k : ℕ) + 1) (by omega),
    handleBlockScript_point i j ((k : ℕ) + 2) (by omega)]
  split_ifs <;> omega

/-- The effect of the block firing on a weighted count of the handle chips. -/
theorem handleWeighted_prin_handleBlockScript (w : ℕ → ℤ) (i j : Fin (m + 1)) (hij : i ≤ j) :
    handleWeighted w (prin (handleGraph G x y m) (handleBlockScript i j)) =
      (if 1 ≤ (i : ℕ) then w ((i : ℕ) - 1) else 0) +
        (if (j : ℕ) + 1 ≤ m then w ((j : ℕ) + 1) else 0) - w i - w j := by
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
  have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
  have hi' : (i : ℕ) ≤ m + 1 := by omega
  simp only [handleWeighted, prin_handleBlockScript_inr i j hij, mul_add, mul_sub, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_fin_ite_succ_val_eq,
    sum_fin_ite_val_eq, ite_eq_left hi, ite_eq_left hj, hi', and_true]

/-- The potential weights change by `2 (i - j) - 2` under the block firing. -/
theorem handleWeight_block_change {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    (if 1 ≤ i then handleWeight m (i - 1) else 0) +
        (if j + 1 ≤ m then handleWeight m (j + 1) else 0) - handleWeight m i -
          handleWeight m j = 2 * (i : ℤ) - 2 * j - 2 := by
  have h1 : (if 1 ≤ i then handleWeight m (i - 1) else 0) = (i : ℤ) * ((m : ℤ) + 2 - i) := by
    split_ifs with h
    · rw [handleWeight, Nat.cast_sub h]
      push_cast
      ring
    · obtain rfl : i = 0 := by omega
      simp
  have h2 : (if j + 1 ≤ m then handleWeight m (j + 1) else 0) =
      ((j : ℤ) + 2) * ((m : ℤ) - j) := by
    split_ifs with h
    · rw [handleWeight]
      push_cast
      ring
    · obtain rfl : j = m := by omega
      simp
  rw [h1, h2, handleWeight, handleWeight]
  ring

/-! ## One step -/

/-- **One spreading step.** Two handle chips at indices `i ≤ j` are moved apart by firing
`q_i, …, q_j`; a chip that leaves the handle is recorded at `x` (`α₁`) or at `y` (`β₁`), and the
potential drops. -/
theorem exists_handle_step {E : CFDiv (handleGraph G x y m)} (hE : effective E)
    {i j : Fin (m + 1)} (hij : i ≤ j)
    (hE2 : effective (E - one_chip (handleInr i) - one_chip (handleInr j))) :
    ∃ (E₁ : CFDiv (handleGraph G x y m)) (α₁ β₁ : ℕ),
      effective E₁ ∧ linear_equiv (handleGraph G x y m) E E₁ ∧
      handleRestrict E₁ = handleRestrict E + (α₁ : ℤ) • one_chip x + (β₁ : ℤ) • one_chip y ∧
      handleInterior E₁ + α₁ + β₁ = handleInterior E ∧
      handleMoment E₁ + ((m : ℤ) + 2) * β₁ = handleMoment E ∧
      handlePotential E₁ < handlePotential E := by
  have hij' : (i : ℕ) ≤ j := hij
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
  have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
  refine ⟨E + prin (handleGraph G x y m) (handleBlockScript i j),
    if (i : ℕ) = 0 then 1 else 0, if (j : ℕ) = m then 1 else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rcases handleGraph_cases v with ⟨b, rfl⟩ | ⟨k, rfl⟩
    · rw [Pi.add_apply, prin_handleBlockScript_inl]
      have := hE (handleInl b)
      split_ifs <;> omega
    · rw [Pi.add_apply, prin_handleBlockScript_inr i j hij]
      have h := hE2 (handleInr k)
      rw [Pi.sub_apply, Pi.sub_apply, one_chip_handleInr_apply_handleInr,
        one_chip_handleInr_apply_handleInr] at h
      simp only [Fin.ext_iff] at h
      split_ifs at h ⊢ <;> omega
  · exact (principal_iff_eq_prin _ _).mpr ⟨handleBlockScript i j, add_sub_cancel_left _ _⟩
  · funext b
    simp only [handleRestrict_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      prin_handleBlockScript_inl, one_chip]
    push_cast
    split_ifs <;> omega
  · rw [handleInterior_eq_handleWeighted, handleInterior_eq_handleWeighted, handleWeighted_add,
      handleWeighted_prin_handleBlockScript _ i j hij]
    push_cast
    split_ifs <;> omega
  · rw [handleMoment_eq_handleWeighted, handleMoment_eq_handleWeighted, handleWeighted_add,
      handleWeighted_prin_handleBlockScript _ i j hij]
    push_cast
    split_ifs <;> omega
  · rw [handlePotential, handlePotential, handleWeighted_add,
      handleWeighted_prin_handleBlockScript _ i j hij, handleWeight_block_change hi hj]
    omega

/-! ## The iteration -/

/-- The collapse, by induction on a bound for the potential. -/
theorem exists_collapsed_representative_aux (n : ℕ) :
    ∀ E : CFDiv (handleGraph G x y m), effective E → handlePotential E < n →
    ∃ (E' : CFDiv (handleGraph G x y m)) (α β : ℕ),
      effective E' ∧ linear_equiv (handleGraph G x y m) E E' ∧ handleInterior E' ≤ 1 ∧
      handleRestrict E' = handleRestrict E + (α : ℤ) • one_chip x + (β : ℤ) • one_chip y ∧
      handleInterior E' + α + β = handleInterior E ∧
      handleMoment E' + ((m : ℤ) + 2) * β = handleMoment E := by
  induction n with
  | zero =>
    intro E hE hΦ
    have := handlePotential_nonneg hE
    omega
  | succ n ih =>
    intro E hE hΦ
    by_cases hI : handleInterior E ≤ 1
    · refine ⟨E, 0, 0, hE, linear_equiv.refl _ E, hI, ?_, by simp, by simp⟩
      simp
    · obtain ⟨i, j, hij, hE2⟩ := exists_two_handle_chips hE (by omega)
      obtain ⟨E₁, α₁, β₁, hE₁, hlin₁, hR₁, hI₁, hM₁, hΦ₁⟩ := exists_handle_step hE hij hE2
      obtain ⟨E', α', β', hE', hlin', hI', hR', hI'', hM'⟩ := ih E₁ hE₁ (by omega)
      refine ⟨E', α₁ + α', β₁ + β', hE', hlin₁.trans hlin', hI', ?_, ?_, ?_⟩
      · rw [hR', hR₁]
        funext a
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      · omega
      · push_cast
        linear_combination hM' + hM₁

/-- **Collapsing the handle.** Every effective divisor on the handle graph is linearly equivalent
to an effective divisor with at most one chip on the new vertices. The old part gains `α` chips
at `x` and `β` chips at `y`; the number of handle chips drops by `α + β`; and the moment drops by
`(m + 2) * β`. -/
theorem exists_collapsed_representative (E : CFDiv (handleGraph G x y m)) (hE : effective E) :
    ∃ (E' : CFDiv (handleGraph G x y m)) (α β : ℕ),
      effective E' ∧ linear_equiv (handleGraph G x y m) E E' ∧ handleInterior E' ≤ 1 ∧
      handleRestrict E' = handleRestrict E + (α : ℤ) • one_chip x + (β : ℤ) • one_chip y ∧
      handleInterior E' + α + β = handleInterior E ∧
      handleMoment E' + ((m : ℤ) + 2) * β = handleMoment E :=
  exists_collapsed_representative_aux ((handlePotential E).toNat + 1) E hE (by
    have := handlePotential_nonneg hE
    omega)

end Utilities
