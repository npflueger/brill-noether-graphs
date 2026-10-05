module

public import Utilities.Foundations.ElementaryExistence
public import Utilities.Foundations.Duality
public import Utilities.Gonality.GonalityTransport
public import Utilities.Iso.FossilTopology

@[expose] public section

/-!
# Genus six reduces to a single critical pencil

`LowGenus/LowGenusExistence.lean` reduces Brill--Noether existence in genus at
most five to *two* rank-one statements, one per genus.  This file does the
same arithmetic at genus six, and the answer is better than the pattern
suggests: genus six needs **one** critical pencil, not two or three.

## The three non-elementary pairs

`Utilities.BNExists_elementary` settles every pair with `r = 0` or rectangle
width `q = g - d + r` at most one.  Outside that range `r >= 1` and `q >= 2`,
and admissibility `0 <= rho = g - (r + 1) q` forces `(r + 1) q <= 6`, hence
`r + 1 <= 3`.  Enumerating:

| `(r, d)` | `q` | `rho` |
|---|---|---|
| `(1, 4)` | 3 | 0 |
| `(1, 5)` | 2 | 2 |
| `(2, 6)` | 2 | 0 |

and nothing else.  `(1, 4)` is the critical pencil, `rho(6, 1, 4) = 0`.

## Why the other two are free

* **`(2, 6)` is `(1, 4)`.**  Riemann--Roch duality sends degree `d` to
  `2g - 2 - d = 4` and rank `r` to `g - d + r - 1 = 1`.  That is exactly
  `Utilities.BNExists_dual_iff`, which the shared library already proves, so
  `(2, 6)` costs a rewrite.  Concretely: `deg D = 6` and `rank D >= 2` give
  `rank (K - D) = rank D - 1 >= 1` with `deg (K - D) = 4`, and conversely
  `deg E = 4`, `rank E >= 1` give `rank (K - E) = rank E + 1 >= 2` with
  `deg (K - E) = 6`.  The equivalence is exact in both directions, not a
  one-way implication.
* **`(1, 5)` follows from `(1, 4)`.**  Add a chip: rank does not drop when an
  effective divisor is added (`Utilities.Gonality.rank_ge_of_add_effective`).  So
  `(1, 5)`, despite `rho = 2 > 0`, needs no separate argument.

So `GenusSixRankOneExistence` below is the whole geometric content of
Brill--Noether existence at genus six.

## Structural reduction through the fossil

The canonical first reduction is passage to `Utilities.fossil`, the
degree-one Abel--Jacobi image / 2-edge-connectivization.  It preserves genus,
rank and Brill--Noether existence and produces a graph with the two-edge cut
condition in one step.  Thus a genus-six argument may work directly on fossils
rather than recursively pruning leaves and bridges; this is how
`GenusSixOddDescent.bnExists_genus_six_of_oddWitness` removes every
bridgelessness hypothesis.

Explicit reductions are also available where a concrete presentation or
marked-point transport is required:

* leaf pruning -- `Utilities.Certificate.LeafReduction.bnExists_rank_one_of_leafless`
  takes `targetGenus` and `degree` as parameters, so it applies at
  `(6, 4)` with no change at all;
* `genus_deleteLeaf`, `graph_connected_deleteLeaf` and the strictly decreasing
  vertex count that drives its induction are genus-free;
* the vertex-cut genus split
  (`Utilities.Certificate.CoreVertexCut.Data.leftGenus_add_rightGenus_eq_graph_genus`)
  and the loop-aware pseudocore presentation are stated over `Core n p` for
  arbitrary `n, p`.

The guarding-set glue of the low-genus existence proofs,
`AtanasovRanganathan.Guarding.GuardingSet` (`LowGenus/GuardingSet.lean`), is
likewise generic in `(n, p)`, with `chips_deg` fixed at four, which is precisely
this critical pencil.
-/

namespace GenusSixOddDescent

open Utilities

/-- The genus-six geometric heart: every connected genus-six graph carries a
degree-four divisor of rank at least one. -/
def GenusSixRankOneExistence : Prop :=
  ∀ (G : CFGraph.{0}), graph_connected G → genus G = 6 → BNExists G 1 4

/-- A fossil-facing formulation of the genus-six geometric heart.  It asks
for the critical pencil only after all separating bridges have been
canonically contracted. -/
def GenusSixFossilRankOneExistence : Prop :=
  ∀ (G : CFGraph.{0}), graph_connected G → genus G = 6 →
    BNExists (fossil G) 1 4

/-- A critical-pencil theorem on fossils already implies the original
genus-six critical pencil. -/
theorem genusSixRankOneExistence_of_fossil
    (critical : GenusSixFossilRankOneExistence) :
    GenusSixRankOneExistence := by
  intro G hConnected hGenus
  exact (BNExists_fossil_iff G hConnected 1 4).mpr
    (critical G hConnected hGenus)

/-- `rho >= 0` is the rectangle-area bound, at any genus. -/
theorem bnNumber_nonneg_iff_rectangle_area_le (G : CFGraph) (r d : ℤ) :
    0 ≤ bnNumber G r d ↔ (r + 1) * rectangleWidth G r d ≤ genus G := by
  unfold bnNumber
  omega

/-- **The degree-five pencil is free.**  Adding one chip to a degree-four
rank-one divisor gives a degree-five rank-one divisor. -/
theorem bnExists_one_five_of_one_four {G : CFGraph}
    (hCritical : BNExists G 1 4) : BNExists G 1 5 := by
  obtain ⟨D, hDegree, hRank⟩ := hCritical
  let v : G.V := Classical.arbitrary G.V
  refine ⟨D + one_chip v, ?_, ?_⟩
  · rw [deg.map_add, hDegree, deg_one_chip]; norm_num
  · exact Gonality.rank_ge_of_add_effective (eff_one_chip v) hRank

/-- **The rank-two degree-six pencil is the critical pencil.**  Riemann--Roch
duality carries `(2, 6)` to `(1, 4)` and back. -/
theorem bnExists_two_six_iff_one_four {G : CFGraph} (hG : graph_connected G)
    (hGenus : genus G = 6) : BNExists G 2 6 ↔ BNExists G 1 4 := by
  have hDual := BNExists_dual_iff hG 2 6
  have hr : dualRank G 2 6 = 1 := by
    simp [dualRank, rectangleWidth, hGenus]
  have hd : dualDegree G 6 = 4 := by
    simp [dualDegree, hGenus]
  rw [hr, hd] at hDual
  exact hDual

/-- **In genus six, `r = 1`, `d = 4` is the only pair outside the elementary
range that needs an argument.** -/
theorem bnExists_genus_six_of_rankOneDegreeFour
    {G : CFGraph} (hG : graph_connected G) (hGenus : genus G = 6)
    (hCritical : BNExists G 1 4) {r d : ℤ}
    (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  by_cases hEasy : r = 0 ∨ rectangleWidth G r d ≤ 1
  · exact BNExists_elementary hG hR hRho hEasy
  · push Not at hEasy
    obtain ⟨hr0, hWidth⟩ := hEasy
    have hr1 : 1 ≤ r := by omega
    have hq2 : 2 ≤ rectangleWidth G r d := by omega
    have hArea : (r + 1) * rectangleWidth G r d ≤ 6 := by
      rw [bnNumber_nonneg_iff_rectangle_area_le] at hRho
      omega
    -- `(r + 1) * q <= 6` with `r >= 1`, `q >= 2` leaves `r <= 2`
    have hr2 : r ≤ 2 := by nlinarith
    have hWidthDef : rectangleWidth G r d = 6 - d + r := by
      unfold rectangleWidth; omega
    interval_cases r
    · -- r = 1: the width is 2 or 3, i.e. d = 5 or d = 4
      have hq3 : rectangleWidth G 1 d ≤ 3 := by omega
      have : d = 4 ∨ d = 5 := by omega
      rcases this with hd | hd
      · simpa [hd] using hCritical
      · simpa [hd] using bnExists_one_five_of_one_four hCritical
    · -- r = 2: the width is exactly 2, i.e. d = 6
      have hq2' : rectangleWidth G 2 d = 2 := by omega
      have hd : d = 6 := by omega
      subst hd
      exact (bnExists_two_six_iff_one_four hG hGenus).mpr hCritical

/-- The critical pencil implies Brill--Noether existence for every
nonnegative rank and every admissible parameter pair at genus six. -/
theorem bnExists_of_genus_six_of_criticalPencil
    (critical : GenusSixRankOneExistence)
    {G : CFGraph.{0}} (hG : graph_connected G) (hGenus : genus G = 6)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d :=
  bnExists_genus_six_of_rankOneDegreeFour hG hGenus (critical G hG hGenus) hR hRho

/-- **The genus-six Brill--Noether conjecture from one pencil.** -/
theorem brillNoetherConjecture_of_genus_six_of_criticalPencil
    (critical : GenusSixRankOneExistence)
    (G : CFGraph.{0}) (hG : graph_connected G) (hGenus : genus G = 6)
    (r d : ℤ) : brill_noether_conjecture hG r d := by
  show 0 ≤ genus G - (r + 1) * (genus G - d + r) →
    ∃ D : CFDiv G, rank G D ≥ r ∧ deg D = d
  intro hRho
  by_cases hR : 0 ≤ r
  · obtain ⟨D, hDegree, hRank⟩ :=
      bnExists_of_genus_six_of_criticalPencil critical hG hGenus hR
        (by simpa [bnNumber, rectangleWidth] using hRho)
    exact ⟨D, hRank, hDegree⟩
  · let u : G.V := Classical.arbitrary G.V
    refine ⟨d • one_chip u, ?_, ?_⟩
    · have hLower := rank_geq_neg_one G (d • one_chip u)
      omega
    · rw [map_zsmul, deg_one_chip]
      ring

end GenusSixOddDescent
