module

public import GenusSixOddDescent.Main
public import Utilities.Subdivision.OddSubdivisionDescent
public import Utilities.Foundations.RiemannRochWinnable
public import LowGenus.AtanasovRanganathanExistence

@[expose] public section

/-!
# Brill--Noether rank through genus six: the reduction

`reduction` reduces the expected Brill--Noether rank `w^r_d ≥ min(ρ, d - r)` on a connected
graph of genus at most six to three inputs: Brill--Noether existence, `w^1_4 ≥ 1` in genus five,
and `w^1_5 ≥ 2` in genus six. Every other case with `ρ ≥ 0` is elementary: rank zero
(`rank_zero`), the non-special range `d ≥ g + r` (`nonspecial`), width one by a canonical
complement (`width_one`), and `ρ = 0`, which is existence. The minimum with `d - r` is needed in
a statement over all degrees: above `d = g + r` the number `ρ` exceeds what any divisor can
absorb.

The genus-six input is stated as an odd specialization witness, `OddCompletionWitness G 1 2`:
every effective divisor of degree three on the vertices of `G` has a completion by two chips to
a divisor of rank at least one on some odd subdivision of `G`. The odd scale may depend on the
prescribed divisor. Two-chip rounding brings the completion back to `G`
(`of_oddCompletionWitness`, `one_five`).

`throughSix` and `throughSix_expected` are the theorem with all three inputs as hypotheses, the
first two in their odd-subdivision forms. Prose: `Research/genus-six-brill-noether-rank.md`,
§1.3 (The elementary cases), §1.4 (The two remaining cases) and §2.2 (Descent with two residual
chips). On a general curve of genus six, the completions of a degree-three divisor `P + Q + R`
by two points form the length-nine secant scheme of `|K - P - Q - R|` (§2.3); that count
motivates the witness and is not used here.
-/

namespace GenusSixExistence.BrillNoetherRank

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- Rank zero absorbs every effective divisor of the given degree. -/
theorem rank_zero (G : CFGraph) (d : ℤ) : BNRankGe G 0 d d := by
  intro E hE hdeg
  refine ⟨E, by simpa using hdeg, ?_, ?_⟩
  · exact (rank_geq_iff G E 0).mp
      ((rank_nonneg_iff_winnable G E).mpr (winnable_of_effective G E hE))
  · rw [sub_self]
    exact winnable_of_effective G 0 (by intro v; rfl)

/-- At `d ≥ g + r`, every effective divisor of degree `d` has rank at least `r`. -/
theorem nonspecial {G : CFGraph} (hG : graph_connected G) {r d : ℤ}
    (hd : genus G + r ≤ d) : BNRankGe G r d (d - r) := by
  intro E hE hdeg
  refine ⟨E, by omega, ?_, ?_⟩
  · apply (rank_geq_iff G E r).mp
    intro F hF
    apply winnable_of_deg_ge_genus hG (E - F)
    rw [deg.map_sub, hdeg, hF.2]
    omega
  · rw [sub_self]
    exact winnable_of_effective G 0 (by intro v; rfl)

/-- Width one also has the expected BN rank, by a canonical complement. -/
theorem width_one {G : CFGraph} (hG : graph_connected G) {r d : ℤ}
    (hr : 0 ≤ r) (hq : rectangleWidth G r d = 1)
    (hρ : 0 ≤ bnNumber G r d) : BNRankGe G r d (bnNumber G r d) := by
  have hd : d = genus G - 1 + r := by unfold rectangleWidth at hq; omega
  have hρeq : bnNumber G r d = genus G - 1 - r := by
    unfold bnNumber
    rw [hq]
    ring
  intro E hE hdeg
  have hEdeg : deg E = genus G - 1 := by rw [hρeq] at hdeg; omega
  obtain ⟨H, hH, hlin⟩ :=
    (degree_genus_sub_one_winnable_iff_complement_winnable hG E hEdeg).mp
      (winnable_of_effective G E hE)
  have hHdeg : deg H = genus G - 1 := by
    rw [← linear_equiv_preserves_deg G _ _ hlin, deg.map_sub,
      degree_of_canonical_divisor, hEdeg]
    ring
  have hsplitdeg : deg H = (bnNumber G r d).toNat + r.toNat := by
    rw [Int.toNat_of_nonneg hρ, Int.toNat_of_nonneg hr, hHdeg, hρeq]
    ring
  obtain ⟨F, B, hF, hB, hFdeg, hBdeg, hsplit⟩ :=
    effective_divisor_decomposition G H (bnNumber G r d).toNat r.toNat hH hsplitdeg
  have hFdeg' : deg F = genus G - 1 - r := by
    rw [hFdeg, Int.toNat_of_nonneg hρ, hρeq]
  refine ⟨canonical_divisor G - F, ?_, ?_, ?_⟩
  · rw [deg.map_sub, degree_of_canonical_divisor, hFdeg', hd]
    ring
  · exact (canonical_sub_rank_ge_iff_winnable_of_degree hG F r hFdeg').mpr
      (winnable_of_effective G F hF)
  · refine ⟨B, hB, ?_⟩
    unfold linear_equiv at hlin ⊢
    rw [hsplit] at hlin
    convert hlin using 1; abel

/-- **Odd specialization, one prescribed divisor at a time**, in the unit presentation of `G`
(which only relabels the vertices of `G`). Every effective `E` of degree `r + k` has a
completion by two chips to a divisor of rank at least `r` on some odd subdivision of `G`; the
odd scale may depend on `E`. -/
def OddCompletionWitness (G : CFGraph) (r k : ℤ) : Prop :=
  ∀ E : CFDiv (UnitSubdivisionPresentation.spec G).graph,
    effective E → deg E = r + k →
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      ∃ F : CFDiv ((UnitSubdivisionPresentation.spec G).scale N hN).graph,
        effective F ∧ deg F = 2 ∧
        rank ((UnitSubdivisionPresentation.spec G).scale N hN).graph
          ((UnitSubdivisionPresentation.spec G).embed N hN E + F) ≥ r

/-- Abstract two-chip completion, keeping divisor algebra away from the
concrete unit-subdivision vertex type. -/
private theorem coarse_completion {n p : ℕ} (spec : Spec n p)
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) {r : ℤ}
    (E : CFDiv spec.graph) (F : CFDiv (spec.scale N hN).graph)
    (hFeff : effective F) (hFdeg : deg F = 2)
    (hrank : rank (spec.scale N hN).graph (spec.embed N hN E + F) ≥ r) :
    ∃ B : CFDiv spec.graph, effective B ∧ deg B = 2 ∧ rank spec.graph (E + B) ≥ r := by
  obtain ⟨y₁, y₂, hF⟩ := exists_chip_pair_of_effective_deg_two _ F hFeff hFdeg
  subst hF
  have hsum2 : (∑ i : Fin 2, one_chip (![y₁, y₂] i) : CFDiv (spec.scale N hN).graph)
      = one_chip y₁ + one_chip y₂ := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrank2 : rank (spec.scale N hN).graph
      (spec.embed N hN E + ∑ i : Fin 2, one_chip (![y₁, y₂] i)) ≥ r := by
    rw [hsum2]
    exact hrank
  have hbudget : (∑ i : Fin 2, (spec.roundDist N hN (![y₁, y₂] i) : ℤ)) < N := by
    have h1 := spec.two_mul_roundDist_lt N hN hodd y₁
    have h2 := spec.two_mul_roundDist_lt N hN hodd y₂
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hcoarse := spec.rank_ge_of_rank_scale_ge_nearest N hN ![y₁, y₂] E r hbudget hrank2
  rw [Fin.sum_univ_two] at hcoarse
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcoarse
  have heff : effective (one_chip (spec.nearest N hN y₁) + one_chip (spec.nearest N hN y₂)
      : CFDiv spec.graph) := by
    intro v
    exact add_nonneg (eff_one_chip (spec.nearest N hN y₁) v)
      (eff_one_chip (spec.nearest N hN y₂) v)
  have hdegB : deg (one_chip (spec.nearest N hN y₁) + one_chip (spec.nearest N hN y₂)
      : CFDiv spec.graph) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  exact ⟨_, heff, hdegB, hcoarse⟩

/-- **Descent with two residual chips.** Nearest rounding at an odd scale preserves every
prescribed chip, and moves the two residual chips to vertices of `G`. -/
theorem of_oddCompletionWitness {G : CFGraph} {r k : ℤ}
    (h : OddCompletionWitness G r k) : BNRankGe G r (r + k + 2) k := by
  refine ((UnitSubdivisionPresentation.laplacianEquiv G).bnRankGe_iff
    r (r + k + 2) k).mp ?_
  intro E hE hdeg
  obtain ⟨N, hN, hodd, F, hF, hFdeg, hFrank⟩ := h E hE hdeg
  obtain ⟨B, hB, hBdeg, hBrank⟩ :=
    coarse_completion (UnitSubdivisionPresentation.spec G) N hN hodd (r := r) E F hF hFdeg hFrank
  refine ⟨E + B, ?_, hBrank, ?_⟩
  · rw [deg.map_add, hdeg, hBdeg]
  · rw [add_sub_cancel_left]
    exact winnable_of_effective _ _ hB

/-- In genus six, the triple witness gives `w^1_5 ≥ 2`. -/
theorem one_five (G : CFGraph) (h : OddCompletionWitness G 1 2) :
    BNRankGe G 1 5 2 := by
  simpa using of_oddCompletionWitness h

/-- **Reduction for every genus at most six.** Once existence is known, the only cases with
`ρ > 0` that are not elementary are `(g, r, d) = (5, 1, 4)` and `(6, 1, 5)`. -/
theorem reduction {G : CFGraph} (hG : graph_connected G) (hg : genus G ≤ 6)
    (hex : ∀ r d : ℤ, 0 ≤ r → 0 ≤ bnNumber G r d → BNExists G r d)
    (hfive : genus G = 5 → BNRankGe G 1 4 1)
    (hsix : genus G = 6 → BNRankGe G 1 5 2)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNRankGe G r d (min (bnNumber G r d) (d - r)) := by
  by_cases hr0 : r = 0
  · subst r
    simpa [bnNumber, rectangleWidth] using rank_zero G d
  have hr1 : 1 ≤ r := by omega
  by_cases hq0 : rectangleWidth G r d ≤ 0
  · have hd : genus G + r ≤ d := by unfold rectangleWidth at hq0; omega
    have hm : d - r ≤ bnNumber G r d := by
      unfold bnNumber rectangleWidth
      nlinarith
    rw [min_eq_right hm]
    exact nonspecial hG hd
  have hq1 : 1 ≤ rectangleWidth G r d := by omega
  have hm : bnNumber G r d ≤ d - r := by
    unfold bnNumber rectangleWidth at *
    nlinarith
  rw [min_eq_left hm]
  by_cases hqeq : rectangleWidth G r d = 1
  · exact width_one hG hr hqeq hρ
  by_cases hzero : bnNumber G r d = 0
  · rw [hzero]
    exact (bnRankGe_zero_iff_bnExists G r d hr).mpr (hex r d hr hρ)
  have hq2 : 2 ≤ rectangleWidth G r d := by omega
  have harea : (r + 1) * rectangleWidth G r d < genus G := by
    unfold bnNumber at hρ hzero
    omega
  have hrEq : r = 1 := by nlinarith
  subst r
  have hqEq : rectangleWidth G 1 d = 2 := by omega
  have hgenus : genus G = 5 ∨ genus G = 6 := by omega
  rcases hgenus with h5 | h6
  · have hd : d = 4 := by unfold rectangleWidth at hqEq; omega
    subst d
    simpa [bnNumber, rectangleWidth, h5] using hfive h5
  · have hd : d = 5 := by unfold rectangleWidth at hqEq; omega
    subst d
    simpa [bnNumber, rectangleWidth, h6] using hsix h6

/-- **The all-degree conditional theorem.** The three inputs are the genus-six odd-subdivision
witness of degree four (Brill--Noether existence in genus six), the genus-five odd pair witness,
and the genus-six triple witness. No descent or arithmetic obligation remains in the
conclusion. -/
theorem throughSix
    (hcritical : GenusSixOddDescent.GenusSixOddSubdivisionWitness.{0})
    (hpairs : ∀ G : CFGraph.{0}, graph_connected G → genus G = 5 →
      Gonality.OddPairWitness G)
    (htriples : ∀ G : CFGraph.{0}, graph_connected G → genus G = 6 →
      OddCompletionWitness G 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNRankGe G r d (min (bnNumber G r d) (d - r)) := by
  apply reduction hG hg ?_ ?_ ?_ hr hρ
  · intro r d hr hρ
    by_cases h5 : genus G ≤ 5
    · obtain ⟨D, hRank, hDeg⟩ :=
        AtanasovRanganathan.brillNoetherExistenceThroughFive G hG h5 r d
          (by simpa [bnNumber, rectangleWidth] using hρ)
      exact ⟨D, hDeg, hRank⟩
    · exact GenusSixOddDescent.bnExists_genus_six_of_oddWitness
        hcritical G hG (by omega) hr hρ
  · intro h5
    exact Gonality.bnRankGe_one_four_of_oddPairWitness G (hpairs G hG h5)
  · intro h6
    exact one_five G (htriples G hG h6)

/-- The requested inequality in its natural degree range. -/
theorem throughSix_expected
    (hcritical : GenusSixOddDescent.GenusSixOddSubdivisionWitness.{0})
    (hpairs : ∀ G : CFGraph.{0}, graph_connected G → genus G = 5 →
      Gonality.OddPairWitness G)
    (htriples : ∀ G : CFGraph.{0}, graph_connected G → genus G = 6 →
      OddCompletionWitness G 1 2)
    (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G ≤ 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d)
    (hd : d ≤ genus G + r) : bnNumber G r d ≤ bnRank G r d := by
  apply (bnRankGe_iff_le_bnRank hr hρ).mp
  have hm : bnNumber G r d ≤ d - r := by
    unfold bnNumber rectangleWidth
    nlinarith [mul_nonneg hr (show 0 ≤ genus G - d + r by omega)]
  simpa only [min_eq_left hm] using throughSix hcritical hpairs htriples G hG hg hr hρ

end GenusSixExistence.BrillNoetherRank
