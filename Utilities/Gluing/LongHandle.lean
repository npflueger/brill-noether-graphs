import Utilities.Gluing.HandleRestriction
import Utilities.Gluing.HandleSpread
import Utilities.Foundations.RankInvariance

/-!
# The long-handle lemma

Let `G` be a connected graph and `x`, `y` two of its vertices. Attach a path of `m + 2` edges
from `x` to `y`, with `m` even and the handle long: `2 * (d * (|V(G)| - 1)) < m + 2`. If the
handle graph has a divisor of degree `d` and rank at least one, then `G` has an effective divisor
of degree `d` and rank at least one with a chip at `x` and a chip at `y`
(`exists_pencil_through_ends_of_handle`).

This is the tropical form of a node: a pencil on a curve with `x` and `y` identified is a pencil
on the normalization with `x` and `y` in a common fibre. A prose proof is in
`Research/long-handle-lemma.md`.

The proof. Take an effective representative `E` with a chip at the midpoint of the handle.

* If that chip is alone on the handle, it can be dropped: the old part of `E` has rank at least
  one on `G`, in degree `d - 1` (`rank_handleRestrict_ge_one_of_single_chip`). Move it to a
  representative through `x` and add a chip at `y`.
* Otherwise collapse the handle (`exists_collapsed_representative`): at most one chip stays, `α`
  chips have left at `x` and `β` at `y`. Push the remaining chip to its nearer end
  (`rank_handleRestrict_ge_one_of_single_chip`, `rank_handleRestrict_ge_one_of_interior_zero`).
  The moment of the handle chips is conserved, and a chip at the midpoint keeps it strictly
  between `1/2` and `n - 1/2` times the length, so both ends receive a chip.
-/

namespace Utilities

universe u

section Generic

variable {H : CFGraph.{u}}

/-- Adding back a subtracted divisor: if `D - C` is equivalent to `E₀`, then `D` is equivalent
to `E₀ + C`. -/
theorem linear_equiv_add_of_sub {D C E₀ : CFDiv H} (h : linear_equiv H (D - C) E₀) :
    linear_equiv H D (E₀ + C) := by
  unfold linear_equiv at h ⊢
  have hEq : E₀ + C - D = E₀ - (D - C) := by abel
  rw [hEq]
  exact h

end Generic

variable {G : CFGraph.{u}} {x y : G.V} {m : ℕ}

/-! ## Divisors with at most one chip on the handle -/

/-- With at most one chip on the handle, an effective divisor has none there or exactly one. -/
theorem handleInterior_le_one_cases {D : CFDiv (handleGraph G x y m)} (hD : effective D)
    (hInt : handleInterior D ≤ 1) :
    (∀ i : Fin (m + 1), D (handleInr i) = 0) ∨
      ∃ i₀ : Fin (m + 1), D (handleInr i₀) = 1 ∧
        ∀ i : Fin (m + 1), i ≠ i₀ → D (handleInr i) = 0 := by
  by_cases hZero : ∀ i : Fin (m + 1), D (handleInr i) = 0
  · exact Or.inl hZero
  · right
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hZero
    have hNonneg := hD (handleInr i₀)
    have hSplit : handleInterior D =
        D (handleInr i₀) + ∑ i ∈ Finset.univ.erase i₀, D (handleInr i) :=
      (Finset.add_sum_erase Finset.univ (fun i => D (handleInr i)) (Finset.mem_univ i₀)).symm
    have hRest : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, D (handleInr i) :=
      Finset.sum_nonneg fun i _ => hD (handleInr i)
    refine ⟨i₀, by omega, ?_⟩
    intro i hi
    have hLe : D (handleInr i) ≤ ∑ j ∈ Finset.univ.erase i₀, D (handleInr j) :=
      Finset.single_le_sum (f := fun j => D (handleInr j)) (fun j _ => hD (handleInr j))
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    have hNonneg' := hD (handleInr i)
    omega

theorem handleInterior_eq_zero_of_forall {D : CFDiv (handleGraph G x y m)}
    (h : ∀ i : Fin (m + 1), D (handleInr i) = 0) : handleInterior D = 0 :=
  Finset.sum_eq_zero fun i _ => h i

theorem handleMoment_eq_zero_of_forall {D : CFDiv (handleGraph G x y m)}
    (h : ∀ i : Fin (m + 1), D (handleInr i) = 0) : handleMoment D = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]

theorem handleInterior_eq_one_of_single {D : CFDiv (handleGraph G x y m)} {i₀ : Fin (m + 1)}
    (hOne : D (handleInr i₀) = 1)
    (hOther : ∀ i : Fin (m + 1), i ≠ i₀ → D (handleInr i) = 0) : handleInterior D = 1 := by
  unfold handleInterior
  rw [Finset.sum_eq_single i₀ (fun i _ hi => hOther i hi)
    (fun h => absurd (Finset.mem_univ _) h), hOne]

theorem handleMoment_eq_of_single {D : CFDiv (handleGraph G x y m)} {i₀ : Fin (m + 1)}
    (hOne : D (handleInr i₀) = 1)
    (hOther : ∀ i : Fin (m + 1), i ≠ i₀ → D (handleInr i) = 0) :
    handleMoment D = (i₀ : ℤ) + 1 := by
  unfold handleMoment
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hOther i hi, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), hOne, mul_one]

/-! ## The moment of a divisor with a chip at a given handle vertex -/

/-- Every handle chip has position at least one, and the chip at `handleInr μ` has position
`μ + 1`. -/
theorem add_handleInterior_le_handleMoment {D : CFDiv (handleGraph G x y m)} (hD : effective D)
    (μ : Fin (m + 1)) (hμ : 1 ≤ D (handleInr μ)) :
    (μ : ℤ) + handleInterior D ≤ handleMoment D := by
  have hDiff : handleMoment D - handleInterior D =
      ∑ i : Fin (m + 1), (i : ℤ) * D (handleInr i) := by
    unfold handleMoment handleInterior
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hSingle : (μ : ℤ) * D (handleInr μ) ≤ ∑ i : Fin (m + 1), (i : ℤ) * D (handleInr i) :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => (i : ℤ) * D (handleInr i))
      (fun i _ => mul_nonneg (Int.natCast_nonneg _) (hD (handleInr i))) (Finset.mem_univ μ)
  have hμ0 : (0 : ℤ) ≤ (μ : ℤ) := Int.natCast_nonneg _
  have hMul : (μ : ℤ) ≤ (μ : ℤ) * D (handleInr μ) := by nlinarith
  linarith

/-- Every handle chip has position at most `m + 1`, and the chip at `handleInr μ` has position
`μ + 1`. -/
theorem handleMoment_add_le {D : CFDiv (handleGraph G x y m)} (hD : effective D)
    (μ : Fin (m + 1)) (hμ : 1 ≤ D (handleInr μ)) :
    handleMoment D + ((m : ℤ) - μ) ≤ ((m : ℤ) + 1) * handleInterior D := by
  have hDiff : ((m : ℤ) + 1) * handleInterior D - handleMoment D =
      ∑ i : Fin (m + 1), ((m : ℤ) - i) * D (handleInr i) := by
    unfold handleMoment handleInterior
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hSingle : ((m : ℤ) - μ) * D (handleInr μ) ≤
      ∑ i : Fin (m + 1), ((m : ℤ) - i) * D (handleInr i) :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => ((m : ℤ) - i) * D (handleInr i))
      (fun i _ => mul_nonneg (by have := i.isLt; omega) (hD (handleInr i))) (Finset.mem_univ μ)
  have hμm : (0 : ℤ) ≤ (m : ℤ) - μ := by have := μ.isLt; omega
  have hMul : (m : ℤ) - μ ≤ ((m : ℤ) - μ) * D (handleInr μ) := by nlinarith
  linarith

/-! ## The lemma -/

/-- **The long-handle lemma.** If `G` with a long handle from `x` to `y` has a divisor of degree
`d` and rank at least one, then `G` has an effective divisor of degree `d` and rank at least one
with a chip at `x` and a chip at `y`. -/
theorem exists_pencil_through_ends_of_handle (hG : graph_connected G) (d : ℤ) (hEven : Even m)
    (hLong : 2 * (d * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2)
    (hExists : BNExists (handleGraph G x y m) 1 d) :
    ∃ F : CFDiv G, effective F ∧ deg F = d ∧ rank G F ≥ 1 ∧ 1 ≤ F x ∧ 1 ≤ F y := by
  obtain ⟨D, hDeg, hRank⟩ := hExists
  obtain ⟨K, hK⟩ := hEven
  have hKlt : K < m + 1 := by omega
  obtain ⟨μ, hμval⟩ : ∃ μ : Fin (m + 1), (μ : ℕ) = K := ⟨⟨K, hKlt⟩, rfl⟩
  have hmK : (m : ℤ) = 2 * (K : ℤ) := by exact_mod_cast (by omega : m = 2 * K)
  have hμK : ((μ : ℕ) : ℤ) = (K : ℤ) := by exact_mod_cast hμval
  have hK0 : (0 : ℤ) ≤ (K : ℤ) := Int.natCast_nonneg _
  -- An effective representative with a chip at the midpoint.
  obtain ⟨E₀, hE₀mem, hEquiv₀⟩ :=
    (rank_ge_one_iff_winnable_sub_one_chip _ D).mp hRank (handleInr μ)
  have hE₀ : effective E₀ := hE₀mem
  obtain ⟨E, hEdef⟩ : ∃ E : CFDiv (handleGraph G x y m),
      E = E₀ + one_chip (handleInr μ) := ⟨_, rfl⟩
  have hEeff : effective E := by
    rw [hEdef]
    intro v
    exact add_nonneg (hE₀ v) (eff_one_chip (handleInr μ) v)
  have hEquiv : linear_equiv (handleGraph G x y m) D E := by
    rw [hEdef]
    exact linear_equiv_add_of_sub hEquiv₀
  have hEdeg : deg E = d := by
    rw [← linear_equiv_preserves_deg _ D E hEquiv]
    exact hDeg
  have hErank : rank (handleGraph G x y m) E ≥ 1 := by
    rw [← rank_eq_of_linear_equiv _ hEquiv]
    exact hRank
  have hEμ : 1 ≤ E (handleInr μ) := by
    have h0 := hE₀ (handleInr μ)
    rw [hEdef, Pi.add_apply, one_chip_apply_v]
    omega
  have hLongE : 2 * (deg E * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2 := by
    rw [hEdeg]
    exact hLong
  have hn1 : 1 ≤ handleInterior E := by
    have hLe : E (handleInr μ) ≤ handleInterior E :=
      Finset.single_le_sum (f := fun i => E (handleInr i)) (fun i _ => hEeff (handleInr i))
        (Finset.mem_univ μ)
    omega
  have hMlow := add_handleInterior_le_handleMoment hEeff μ hEμ
  have hMup := handleMoment_add_le hEeff μ hEμ
  have hDegSplit := deg_handleGraph E
  rcases eq_or_lt_of_le hn1 with hn | hn
  · -- The midpoint chip is alone on the handle: drop it.
    obtain hZero | ⟨i₀, hOne, hOther⟩ := handleInterior_le_one_cases hEeff (le_of_eq hn.symm)
    · have := hZero μ
      omega
    · have hi₀ : μ = i₀ := by
        by_contra hne
        have := hOther μ hne
        omega
      subst hi₀
      have hMid : 2 * ((μ : ℕ) + 1) = m + 2 := by omega
      have hRankR : rank G (handleRestrict E) ≥ 1 :=
        (rank_handleRestrict_ge_one_of_single_chip hG hEeff hLongE hErank μ hOne hOther).2.2 hMid
      obtain ⟨F₀, hF₀mem, hF₀equiv⟩ :=
        (rank_ge_one_iff_winnable_sub_one_chip G _).mp hRankR x
      have hF₀ : effective F₀ := hF₀mem
      have hF₀deg := linear_equiv_preserves_deg G _ F₀ hF₀equiv
      rw [deg.map_sub, deg_one_chip] at hF₀deg
      refine ⟨F₀ + one_chip x + one_chip y, ?_, ?_, ?_, ?_, ?_⟩
      · intro v
        exact add_nonneg (add_nonneg (hF₀ v) (eff_one_chip x v)) (eff_one_chip y v)
      · rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip]
        omega
      · apply rank_add_effective_ge G _ _ (eff_one_chip y) 1
        rw [← rank_eq_of_linear_equiv G (linear_equiv_add_of_sub hF₀equiv)]
        exact hRankR
      · have h1 := hF₀ x
        have h2 := eff_one_chip y x
        rw [Pi.add_apply, Pi.add_apply, one_chip_apply_v]
        omega
      · have h1 := hF₀ y
        have h2 := eff_one_chip x y
        rw [Pi.add_apply, Pi.add_apply, one_chip_apply_v]
        omega
  · -- At least two chips on the handle: collapse, then push the last chip to its nearer end.
    obtain ⟨E', α, β, hE'eff, hE'equiv, hE'int, hRestr, hCount, hMoment⟩ :=
      exists_collapsed_representative E hEeff
    have hE'deg : deg E' = d := by
      rw [← linear_equiv_preserves_deg _ E E' hE'equiv]
      exact hEdeg
    have hE'rank : rank (handleGraph G x y m) E' ≥ 1 := by
      rw [← rank_eq_of_linear_equiv _ hE'equiv]
      exact hErank
    have hLongE' : 2 * (deg E' * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2 := by
      rw [hE'deg]
      exact hLong
    have hDegSplit' := deg_handleGraph E'
    have hα0 : (0 : ℤ) ≤ (α : ℤ) := Int.natCast_nonneg _
    have hβ0 : (0 : ℤ) ≤ (β : ℤ) := Int.natCast_nonneg _
    have hRestrEff := effective_handleRestrict hE'eff
    have hx : (α : ℤ) ≤ handleRestrict E' x := by
      have h1 := effective_handleRestrict hEeff x
      have h2 : 0 ≤ (β : ℤ) * one_chip y x := mul_nonneg hβ0 (eff_one_chip y x)
      rw [hRestr]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_chip_apply_v, mul_one]
      linarith
    have hy : (β : ℤ) ≤ handleRestrict E' y := by
      have h1 := effective_handleRestrict hEeff y
      have h2 : 0 ≤ (α : ℤ) * one_chip x y := mul_nonneg hα0 (eff_one_chip x y)
      rw [hRestr]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_chip_apply_v, mul_one]
      linarith
    -- The two products that occur in the moment bounds, as linear atoms.
    have hProd : ((m : ℤ) + 2) * handleInterior E - ((m : ℤ) + 1) * handleInterior E =
        handleInterior E := by ring
    obtain hZero | ⟨i₀, hOne, hOther⟩ := handleInterior_le_one_cases hE'eff hE'int
    · -- Nothing is left on the handle.
      have hInt0 := handleInterior_eq_zero_of_forall hZero
      have hMom0 := handleMoment_eq_zero_of_forall hZero
      rw [hInt0] at hCount hDegSplit'
      rw [hMom0] at hMoment
      have hβ1 : (1 : ℤ) ≤ (β : ℤ) := by
        by_contra hlt
        have hβ : (β : ℤ) = 0 := by omega
        rw [hβ] at hMoment
        linarith
      have hα1 : (1 : ℤ) ≤ (α : ℤ) := by
        by_contra hlt
        have hα : (α : ℤ) = 0 := by omega
        have hβn : (β : ℤ) = handleInterior E := by linarith
        rw [hβn] at hMoment
        linarith
      refine ⟨handleRestrict E', hRestrEff, by linarith,
        rank_handleRestrict_ge_one_of_interior_zero hG hE'eff hLongE' hE'rank hZero,
        by linarith, by linarith⟩
    · -- One chip is left, at `handleInr i₀`.
      have hInt1 := handleInterior_eq_one_of_single hOne hOther
      have hMom1 := handleMoment_eq_of_single hOne hOther
      rw [hInt1] at hCount hDegSplit'
      rw [hMom1] at hMoment
      have hRanks :=
        rank_handleRestrict_ge_one_of_single_chip hG hE'eff hLongE' hE'rank i₀ hOne hOther
      by_cases hHalf : 2 * ((i₀ : ℕ) + 1) ≤ m + 2
      · have hHalfZ : 2 * (((i₀ : ℕ) : ℤ) + 1) ≤ (m : ℤ) + 2 := by exact_mod_cast hHalf
        have hβ1 : (1 : ℤ) ≤ (β : ℤ) := by
          by_contra hlt
          have hβ : (β : ℤ) = 0 := by omega
          rw [hβ] at hMoment
          linarith
        refine ⟨handleRestrict E' + one_chip x, ?_, ?_, hRanks.1 hHalf, ?_, ?_⟩
        · intro v
          exact add_nonneg (hRestrEff v) (eff_one_chip x v)
        · rw [deg.map_add, deg_one_chip]
          linarith
        · have h1 := hRestrEff x
          rw [Pi.add_apply, one_chip_apply_v]
          linarith
        · have h2 := eff_one_chip x y
          rw [Pi.add_apply]
          linarith
      · have hHalf' : m + 2 ≤ 2 * ((i₀ : ℕ) + 1) := by omega
        have hHalfZ : (m : ℤ) + 2 < 2 * (((i₀ : ℕ) : ℤ) + 1) := by
          exact_mod_cast (by omega : m + 2 < 2 * ((i₀ : ℕ) + 1))
        have hα1 : (1 : ℤ) ≤ (α : ℤ) := by
          by_contra hlt
          have hα : (α : ℤ) = 0 := by omega
          have hβn : (β : ℤ) = handleInterior E - 1 := by linarith
          rw [hβn] at hMoment
          have hExpand : ((m : ℤ) + 2) * (handleInterior E - 1) =
              ((m : ℤ) + 2) * handleInterior E - ((m : ℤ) + 2) := by ring
          linarith
        refine ⟨handleRestrict E' + one_chip y, ?_, ?_, hRanks.2.1 hHalf', ?_, ?_⟩
        · intro v
          exact add_nonneg (hRestrEff v) (eff_one_chip y v)
        · rw [deg.map_add, deg_one_chip]
          linarith
        · have h2 := eff_one_chip y x
          rw [Pi.add_apply]
          linarith
        · have h1 := hRestrEff y
          rw [Pi.add_apply, one_chip_apply_v]
          linarith

end Utilities
