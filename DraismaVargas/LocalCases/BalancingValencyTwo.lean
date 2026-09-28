import Utilities.IntegralGeometry.ConeWall
import Mathlib.Tactic

/-!
# DV local balancing: the valency-two, change-two cases

These are the exact positive determinant relations in the four substantive
subcases `w2-r2-nd3-M-11`, `w2-r2-nd3-M-1k`, `w2-r2-nd3-M-kk`, and
`w2-r2-nd3-P` of Draisma--Vargas Part I, Section 6.  The variables `c₁`,
`c₂`, `c₃`, and `s` are the common adjugate-row contributions attached
to the wall.  The three displayed values are the determinants of the three
candidate resolutions computed by the source's local construction.

The conclusions are deliberately phrased as positive finite balancing
relations.  Combined with `exists_opposite_of_balancing`, any nonzero incoming
candidate therefore has a candidate of the opposite determinant sign.  That the
source's three local constructions are valid gluing resolutions is a separate
statement, proved case by case in the modules treating the individual wall
cases.
-/

namespace DraismaVargas.LocalCases.BalancingValencyTwo

open DraismaVargas.Infrastructure
open Finset

/-- A finite positive balancing relation. -/
def PositiveBalance {n : ℕ} (weight value : Fin n → ℚ) : Prop :=
  (∀ i, 0 < weight i) ∧ ∑ i, weight i * value i = 0

/-- A positive finite balance contains an opposite-sign value to every
nonzero chosen member. -/
theorem exists_opposite_of_positiveBalance
    {n : ℕ} {weight value : Fin n → ℚ} (h : PositiveBalance weight value)
    {incoming : Fin n} (hincoming : value incoming ≠ 0) :
    ∃ outgoing, value incoming * value outgoing < 0 := by
  obtain ⟨outgoing, _, hopposite⟩ :=
    exists_opposite_of_balancing Finset.univ weight value
      (fun i _ ↦ h.1 i) h.2 (Finset.mem_univ incoming) hincoming
  exact ⟨outgoing, hopposite⟩

/-- Compatibility name for the three-candidate source cases. -/
abbrev PositiveBalanceThree (weight value : Fin 3 → ℚ) : Prop :=
  PositiveBalance weight value

theorem exists_opposite_of_positiveBalanceThree
    {weight value : Fin 3 → ℚ} (h : PositiveBalanceThree weight value)
    {incoming : Fin 3} (hincoming : value incoming ≠ 0) :
    ∃ outgoing, value incoming * value outgoing < 0 :=
  exists_opposite_of_positiveBalance h hincoming

/-! ## Case `w2-r2-nd3-M-11` -/

/-- Equation (6) of the source: the two singleton blocks and the joined block
have positive weights `1,1,4`. -/
theorem balance_M_11 {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0) :
    PositiveBalanceThree ![1, 1, 4]
      ![2 * c₁, 2 * c₂, c₃ / 2 + s] := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · simp [Fin.sum_univ_succ]
    linarith

theorem exists_opposite_M_11 {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0)
    {incoming : Fin 3}
    (hincoming : ![2 * c₁, 2 * c₂, c₃ / 2 + s] incoming ≠ 0) :
    ∃ outgoing,
      ![2 * c₁, 2 * c₂, c₃ / 2 + s] incoming *
        ![2 * c₁, 2 * c₂, c₃ / 2 + s] outgoing < 0 :=
  exists_opposite_of_positiveBalanceThree (balance_M_11 hleft hright) hincoming

/-! ## Case `w2-r2-nd3-M-1k` -/

/-- Equation (7) of the source, uniformly for every block size `k > 1`. -/
theorem balance_M_1k {k c₁ c₂ c₃ s : ℚ} (hk : 1 < k)
    (hleft : c₁ + c₂ / k + s = 0) (hright : c₃ / k + s = 0) :
    PositiveBalanceThree ![1, 2 * (k - 1), 2 * (k + 1)]
      ![2 * c₁, c₁ + c₂ / (k - 1) + s, c₃ / (k + 1) + s] := by
  have hk0 : k ≠ 0 := by linarith
  have hkm1 : k - 1 ≠ 0 := by linarith
  have hkp1 : k + 1 ≠ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    calc
      2 * c₁ + (2 * (k - 1) * (c₁ + c₂ / (k - 1) + s) +
          2 * (k + 1) * (c₃ / (k + 1) + s)) =
        2 * k * (c₁ + c₂ / k + s) +
          2 * k * (c₃ / k + s) := by
            field_simp [hk0, hkm1, hkp1]
            ring
      _ = 0 := by rw [hleft, hright]; ring

theorem exists_opposite_M_1k {k c₁ c₂ c₃ s : ℚ} (hk : 1 < k)
    (hleft : c₁ + c₂ / k + s = 0) (hright : c₃ / k + s = 0)
    {incoming : Fin 3}
    (hincoming :
      ![2 * c₁, c₁ + c₂ / (k - 1) + s, c₃ / (k + 1) + s] incoming ≠ 0) :
    ∃ outgoing,
      ![2 * c₁, c₁ + c₂ / (k - 1) + s, c₃ / (k + 1) + s] incoming *
        ![2 * c₁, c₁ + c₂ / (k - 1) + s,
          c₃ / (k + 1) + s] outgoing < 0 :=
  exists_opposite_of_positiveBalanceThree (balance_M_1k hk hleft hright) hincoming

/-! ## Case `w2-r2-nd3-M-kk` -/

/-- Equation (8) of the source, with both incoming blocks non-singleton. -/
theorem balance_M_kk {k₁ k₂ c₁ c₂ c₃ s : ℚ} (hk₁ : 1 < k₁) (hk₂ : 1 < k₂)
    (hleft : c₁ / k₁ + c₂ / k₂ + s = 0)
    (hright : c₃ / (k₁ + k₂ - 1) + s = 0) :
    PositiveBalanceThree ![k₁ - 1, k₂ - 1, k₁ + k₂]
      ![c₁ / (k₁ - 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ - 1) + s,
        c₃ / (k₁ + k₂) + s] := by
  have hk₁₀ : k₁ ≠ 0 := by linarith
  have hk₂₀ : k₂ ≠ 0 := by linarith
  have hk₁m1 : k₁ - 1 ≠ 0 := by linarith
  have hk₂m1 : k₂ - 1 ≠ 0 := by linarith
  have hksum : k₁ + k₂ ≠ 0 := by linarith
  have hksub : k₁ + k₂ - 1 ≠ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    calc
      (k₁ - 1) * (c₁ / (k₁ - 1) + c₂ / k₂ + s) +
          ((k₂ - 1) * (c₁ / k₁ + c₂ / (k₂ - 1) + s) +
          (k₁ + k₂) * (c₃ / (k₁ + k₂) + s)) =
        (k₁ + k₂ - 1) * (c₁ / k₁ + c₂ / k₂ + s) +
          (k₁ + k₂ - 1) * (c₃ / (k₁ + k₂ - 1) + s) := by
            field_simp [hk₁₀, hk₂₀, hk₁m1, hk₂m1, hksum, hksub]
            ring
      _ = 0 := by rw [hleft, hright]; ring

theorem exists_opposite_M_kk {k₁ k₂ c₁ c₂ c₃ s : ℚ}
    (hk₁ : 1 < k₁) (hk₂ : 1 < k₂)
    (hleft : c₁ / k₁ + c₂ / k₂ + s = 0)
    (hright : c₃ / (k₁ + k₂ - 1) + s = 0) {incoming : Fin 3}
    (hincoming :
      ![c₁ / (k₁ - 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ - 1) + s,
        c₃ / (k₁ + k₂) + s] incoming ≠ 0) :
    ∃ outgoing,
      ![c₁ / (k₁ - 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ - 1) + s,
        c₃ / (k₁ + k₂) + s] incoming *
      ![c₁ / (k₁ - 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ - 1) + s,
        c₃ / (k₁ + k₂) + s] outgoing < 0 :=
  exists_opposite_of_positiveBalanceThree (balance_M_kk hk₁ hk₂ hleft hright) hincoming

/-! ## Case `w2-r2-nd3-P` -/

/-- Equation (9) of the source, where both outside blocks meet the same side
of the contracted target edge. -/
theorem balance_P {k₁ k₂ c₁ c₂ c₃ s : ℚ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hleft : c₁ / k₁ + c₂ / k₂ + s = 0)
    (hright : c₃ / (k₁ + k₂ + 1) + s = 0) :
    PositiveBalanceThree ![k₁ + 1, k₂ + 1, k₁ + k₂]
      ![c₁ / (k₁ + 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ + 1) + s,
        c₃ / (k₁ + k₂) + s] := by
  have hk₁₀ : k₁ ≠ 0 := ne_of_gt hk₁
  have hk₂₀ : k₂ ≠ 0 := ne_of_gt hk₂
  have hk₁p1 : k₁ + 1 ≠ 0 := by linarith
  have hk₂p1 : k₂ + 1 ≠ 0 := by linarith
  have hksum : k₁ + k₂ ≠ 0 := by linarith
  have hksump1 : k₁ + k₂ + 1 ≠ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]
    calc
      (k₁ + 1) * (c₁ / (k₁ + 1) + c₂ / k₂ + s) +
          ((k₂ + 1) * (c₁ / k₁ + c₂ / (k₂ + 1) + s) +
          (k₁ + k₂) * (c₃ / (k₁ + k₂) + s)) =
        (k₁ + k₂ + 1) * (c₁ / k₁ + c₂ / k₂ + s) +
          (k₁ + k₂ + 1) * (c₃ / (k₁ + k₂ + 1) + s) := by
            field_simp [hk₁₀, hk₂₀, hk₁p1, hk₂p1, hksum, hksump1]
            ring
      _ = 0 := by rw [hleft, hright]; ring

theorem exists_opposite_P {k₁ k₂ c₁ c₂ c₃ s : ℚ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hleft : c₁ / k₁ + c₂ / k₂ + s = 0)
    (hright : c₃ / (k₁ + k₂ + 1) + s = 0) {incoming : Fin 3}
    (hincoming :
      ![c₁ / (k₁ + 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ + 1) + s,
        c₃ / (k₁ + k₂) + s] incoming ≠ 0) :
    ∃ outgoing,
      ![c₁ / (k₁ + 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ + 1) + s,
        c₃ / (k₁ + k₂) + s] incoming *
      ![c₁ / (k₁ + 1) + c₂ / k₂ + s,
        c₁ / k₁ + c₂ / (k₂ + 1) + s,
        c₃ / (k₁ + k₂) + s] outgoing < 0 :=
  exists_opposite_of_positiveBalanceThree (balance_P hk₁ hk₂ hleft hright) hincoming

end DraismaVargas.LocalCases.BalancingValencyTwo
