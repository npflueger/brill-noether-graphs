module

public import DraismaVargasMarkedCount.MarkedCountGeneral.MarkedCount

@[expose] public section

/-!
# The parity of the diagonal count `N(g; g − 4, 0) = g(g − 3)/2`

The typed count of type `a = g − 4` in degree `d = g − 1` is `markedFormula g (g − 1) (g − 4) =
C(g, g − 2) − C(g, 1) = g(g − 1)/2 − g = g(g − 3)/2`, odd exactly when `g ≡ 1` or `2 (mod 4)`.
-/

namespace DiagonalSecant

open DraismaVargas.Count.MarkedCountGeneral

/-- The arithmetic of the diagonal type: `g + (g − 4) + 2 = 2(g − 1)` and `g − 1 ≤ g`. -/
theorem diagonal_degree {g : ℕ} (hg : 4 ≤ g) : g + (g - 4) + 2 = 2 * (g - 1) ∧ g - 1 ≤ g := by
  omega

/-- **`N(g; g − 4, 0) = g(g − 3)/2`** as an integer: `C(g, g − 2) = C(g, 2) = g(g − 1)/2` and
`C(g, 1) = g`. -/
theorem markedFormula_diagonal {g : ℕ} (hg : 4 ≤ g) :
    markedFormula g (g - 1) (g - 4) = ((g * (g - 3) / 2 : ℕ) : ℤ) := by
  unfold markedFormula
  rw [show g + 1 - (g - 1) + (g - 4) = g - 2 by omega, show g - (g - 1) = 1 by omega,
    Nat.choose_one_right, ← Nat.choose_symm (by omega : g - 2 ≤ g), show g - (g - 2) = 2 by omega,
    Nat.choose_two_right]
  have h1 : g * (g - 1) = g * (g - 3) + 2 * g := by
    have : g - 1 = (g - 3) + 2 := by omega
    rw [this, Nat.mul_add]
    ring
  have h2 : g * (g - 1) / 2 = g * (g - 3) / 2 + g := by
    rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  rw [h2]
  push_cast
  ring

/-- **The parity**: `g(g − 3)/2` is odd exactly when `g ≡ 1` or `2 (mod 4)`. -/
theorem odd_diagonal_iff {g : ℕ} (hg : 4 ≤ g) :
    Odd (g * (g - 3) / 2) ↔ g % 4 = 1 ∨ g % 4 = 2 := by
  have key : g * (g - 3) % 4 = if g % 4 = 1 ∨ g % 4 = 2 then 2 else 0 := by
    rw [Nat.mul_mod]
    have h3 : (g - 3) % 4 = (g % 4 + 1) % 4 := by omega
    rw [h3]
    have h4 : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases g % 4 <;> simp
  rw [Nat.odd_iff, ← Nat.mod_mul_right_div_self, show (2 : ℕ) * 2 = 4 by rfl, key]
  split_ifs <;> simp_all

/-- The two facts the assembly consumes, together. -/
theorem odd_markedFormula_diagonal {g : ℕ} (hg : 4 ≤ g) (hmod : g % 4 = 1 ∨ g % 4 = 2) :
    Odd (markedFormula g (g - 1) (g - 4)) := by
  rw [markedFormula_diagonal hg]
  exact_mod_cast (odd_diagonal_iff hg).mpr hmod

end DiagonalSecant
