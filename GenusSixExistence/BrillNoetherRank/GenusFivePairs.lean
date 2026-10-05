module

public import Utilities.Gluing.LongHandle
public import GenusSixExistence.BrillNoetherRank.Reduction
public import GenusSixExistence.OnceMarked

@[expose] public section

/-!
# Pairs in genus five, from genus six

For a connected genus-five graph `G`, **every** pair of vertices lies on a degree-four divisor of
rank at least one (`markedRankOneCompletion_genus_five`). Equivalently `w^1_4(G) ≥ 1`
(`bnRankGe_one_four_one_genus_five`).

The diagonal case `x = y` attaches a cycle at `x`
(`GenusSixExistence.markedRankOneCompletion_diagonal_genus_five`). For `x ≠ y` attach a long
path from `x` to `y` instead. The handle graph is connected of genus six, so
`GenusSixExistence.criticalPencil` gives it a degree-four pencil, and the long-handle lemma
(`Utilities.exists_pencil_through_ends_of_handle`) brings the pencil back to `G` with a chip at
`x` and a chip at `y`. No algebraic input and no odd subdivision is used.

Consequences:

* `transmissionExists_genus_five`: the twice-marked transmission condition with the marked
  two-corner profile, at every pair of marks;
* `bnRankGe_through_five`: the expected Brill--Noether rank through genus five,
  `w^r_d ≥ min(ρ, d - r)`, with no hypothesis;
* `bnNumber_le_bnRank_through_five`: the same as `ρ ≤ w^r_d` in the natural degree range;
* `bnRankGe_through_six_of_triples`: through genus six, the only further input is the genus-six
  triple witness (`w^1_5 ≥ 2`, as `BrillNoetherRank.OddCompletionWitness G 1 2`), and
  `bnNumber_le_bnRank_through_six_of_triples` is its form `ρ ≤ w^r_d`. The triple witness is
  `GenusSixExistence.tripleWitness`, and the unconditional theorems are
  `GenusSixExistence.bnRankGe_through_six` and `GenusSixExistence.bnNumber_le_bnRank_through_six`
  (`GenusSixExistence/BrillNoetherRank.lean`).

The long-handle lemma is in `Utilities/Gluing/LongHandle.lean`, with a prose proof in
`Research/long-handle-lemma.md`. Prose for this module: `Research/genus-six-brill-noether-rank.md`,
§1.5 (Genus five: pairs from a long handle) and §1.4 (The two remaining cases).
-/

namespace GenusSixExistence

open Utilities MarkedGraphs

universe u

/-- **Pairs in genus five.** Every pair of vertices `x`, `y` of a connected genus-five graph
can be completed by two chips to a degree-four divisor of rank at least one. -/
theorem markedRankOneCompletion_genus_five (G : CFGraph.{u}) (hG : graph_connected G)
    (hGenus : genus G = 5) (x y : G.V) : MarkedRankOneCompletion G x y := by
  by_cases hxy : x = y
  · subst hxy
    exact GenusSixExistence.markedRankOneCompletion_diagonal_genus_five G hG hGenus x
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 8 * Fintype.card G.V := ⟨_, rfl⟩
    have hW := graph_connected_handleGraph G x y m hG
    have hWGenus : genus (handleGraph G x y m) = 6 := by
      rw [genus_handleGraph, hGenus]
      norm_num
    have hPencil : BNExists (handleGraph G x y m) 1 4 :=
      GenusSixExistence.criticalPencil _ hW hWGenus
    have hEven : Even m := ⟨4 * Fintype.card G.V, by omega⟩
    have hmZ : (m : ℤ) = 8 * (Fintype.card G.V : ℤ) := by exact_mod_cast hm
    have hLong : 2 * ((4 : ℤ) * ((Fintype.card G.V : ℤ) - 1)) < (m : ℤ) + 2 := by
      rw [hmZ]
      linarith
    obtain ⟨F, hF, hFdeg, hFrank, hFx, hFy⟩ :=
      exists_pencil_through_ends_of_handle hG 4 hEven hLong hPencil
    refine ⟨F - one_chip x - one_chip y, ?_, ?_, ?_⟩
    · intro v
      have hv := hF v
      show F v - one_chip x v - one_chip y v ≥ 0
      simp only [one_chip]
      by_cases hvx : v = x
      · have hvy : ¬ v = y := fun h => hxy (hvx.symm.trans h)
        rw [ite_eq_left hvx, ite_eq_right hvy, hvx]
        omega
      · by_cases hvy : v = y
        · rw [ite_eq_right hvx, ite_eq_left hvy, hvy]
          omega
        · rw [ite_eq_right hvx, ite_eq_right hvy]
          omega
    · rw [deg.map_sub, deg.map_sub, deg_one_chip, deg_one_chip, hFdeg]
      norm_num
    · have hEq : one_chip x + one_chip y + (F - one_chip x - one_chip y) = F := by abel
      rw [hEq]
      exact hFrank

/-- **Twice-marked transmission in genus five.** Every permutation with the marked two-corner
profile (`rank D ≥ 1` and `rank (D - x - y) ≥ 0`) has a transmission divisor at every pair of
marks of every connected genus-five graph. -/
theorem transmissionExists_genus_five (G : CFGraph.{u}) (hG : graph_connected G)
    (hGenus : genus G = 5) (x y : G.V) (τ : AspPerm)
    (hProfile : MarkedGenusFiveTransmissionProfile τ) : TransmissionExists G x y τ :=
  (transmissionExists_iff_markedRankOneCompletion_genus_five G hG hGenus x y τ hProfile).mpr
    (markedRankOneCompletion_genus_five G hG hGenus x y)

/-- **`w^1_4(G) ≥ 1` in genus five.** Every effective divisor of degree two on a connected
genus-five graph is contained in a degree-four divisor of rank at least one. -/
theorem bnRankGe_one_four_one_genus_five (G : CFGraph.{u}) (hG : graph_connected G)
    (hGenus : genus G = 5) : BNRankGe G 1 4 1 := by
  intro A hA hAdeg
  obtain ⟨x, y, rfl⟩ := exists_chip_pair_of_effective_deg_two G A hA (by omega)
  obtain ⟨E, hE, hEdeg, hErank⟩ := markedRankOneCompletion_genus_five G hG hGenus x y
  refine ⟨one_chip x + one_chip y + E, ?_, hErank, ?_⟩
  · rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, hEdeg]
    norm_num
  · have hEq : one_chip x + one_chip y + E - (one_chip x + one_chip y) = E := by abel
    rw [hEq]
    exact winnable_of_effective G E hE

/-- **The expected Brill--Noether rank through genus five.** For every connected graph of genus
at most five and all `r ≥ 0`, `ρ ≥ 0`: `w^r_d ≥ min(ρ, d - r)`. -/
theorem bnRankGe_through_five (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 5)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNRankGe G r d (min (bnNumber G r d) (d - r)) := by
  apply BrillNoetherRank.reduction hG (by omega) ?_ ?_ ?_ hr hρ
  · intro r d _ hρ
    obtain ⟨D, hRank, hDeg⟩ :=
      AtanasovRanganathan.brillNoetherExistenceThroughFive G hG hg r d
        (by simpa [bnNumber, rectangleWidth] using hρ)
    exact ⟨D, hDeg, hRank⟩
  · intro h5
    exact bnRankGe_one_four_one_genus_five G hG h5
  · intro h6
    omega

/-- The same in the natural degree range: `ρ ≤ w^r_d` whenever `d ≤ g + r`. -/
theorem bnNumber_le_bnRank_through_five (G : CFGraph.{0}) (hG : graph_connected G)
    (hg : genus G ≤ 5) {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d)
    (hd : d ≤ genus G + r) : bnNumber G r d ≤ bnRank G r d := by
  apply (bnRankGe_iff_le_bnRank hr hρ).mp
  have hm : bnNumber G r d ≤ d - r := by
    unfold bnNumber rectangleWidth
    nlinarith [mul_nonneg hr (show 0 ≤ genus G - d + r by omega)]
  simpa only [min_eq_left hm] using bnRankGe_through_five G hG hg hr hρ

/-- **Through genus six, from the triple witness.** The expected Brill--Noether rank through
genus six follows from the genus-six triple witness alone (`w^1_5 ≥ 2` in genus six). -/
theorem bnRankGe_through_six_of_triples
    (htriples : ∀ G : CFGraph.{0}, graph_connected G → genus G = 6 →
      BrillNoetherRank.OddCompletionWitness G 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNRankGe G r d (min (bnNumber G r d) (d - r)) := by
  apply BrillNoetherRank.reduction hG hg ?_ ?_ ?_ hr hρ
  · intro r d _ hρ
    obtain ⟨D, hRank, hDeg⟩ :=
      GenusSixExistence.brillNoetherExistenceThroughSix G hG hg r d
        (by simpa [bnNumber, rectangleWidth] using hρ)
    exact ⟨D, hDeg, hRank⟩
  · intro h5
    exact bnRankGe_one_four_one_genus_five G hG h5
  · intro h6
    exact BrillNoetherRank.one_five G (htriples G hG h6)

/-- The same in the natural degree range: from the genus-six triple witness, `ρ ≤ w^r_d` for
every connected graph of genus at most six whenever `d ≤ g + r`. -/
theorem bnNumber_le_bnRank_through_six_of_triples
    (htriples : ∀ G : CFGraph.{0}, graph_connected G → genus G = 6 →
      BrillNoetherRank.OddCompletionWitness G 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d)
    (hd : d ≤ genus G + r) : bnNumber G r d ≤ bnRank G r d := by
  apply (bnRankGe_iff_le_bnRank hr hρ).mp
  have hm : bnNumber G r d ≤ d - r := by
    unfold bnNumber rectangleWidth
    nlinarith [mul_nonneg hr (show 0 ≤ genus G - d + r by omega)]
  simpa only [min_eq_left hm] using
    bnRankGe_through_six_of_triples htriples G hG hg hr hρ

end GenusSixExistence
