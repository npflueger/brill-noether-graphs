import Utilities.Foundations.EdgeAddition
import Utilities.Foundations.Parameters

/-!
# Conditional edge induction

This module isolates two mathematical inputs for an induction on the genus
that adds one edge at a time. `NearRectangle` is a two-point secant-existence
condition on the lower-genus graph. `EdgeNormalizes` asserts that one phase of
every such divisor retains the target rank after the edge is added.

The composition theorem below is unconditional; its content lies in the two
named hypotheses, which this module establishes only in rank zero
(`NearRectangle_rank_zero`, `EdgeNormalizes_rank_zero`).
-/

namespace MarkedGraphs

open Utilities

/-- A divisor satisfying the rank condition and the two-point secant condition
on the lower-genus graph. -/
def NearRectangle (H : CFGraph) (x y : H.V) (r d : ℤ) : Prop :=
  ∃ D : CFDiv H,
    deg D = d ∧
    rank H D ≥ r ∧
    rank H (D - one_chip x - one_chip y) ≥ r - 1

/-- Every near-rectangle divisor has a phase of the required rank after adding
the edge. -/
def EdgeNormalizes
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (r d : ℤ) : Prop :=
  ∀ D : CFDiv H,
    deg D = d →
    rank H D ≥ r →
    rank H (D - one_chip x - one_chip y) ≥ r - 1 →
    ∃ n : ℤ,
      rank (addEdge H x y hxy) (D + n • seamDivisor x y) ≥ r

/-- Near-rectangle existence and edge normalization compose to give the
desired Brill--Noether witness on the graph with the added edge. -/
theorem BNExists_addEdge_of_nearRectangle_of_normalizes
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (r d : ℤ)
    (hNear : NearRectangle H x y r d)
    (hNormalizes : EdgeNormalizes H x y hxy r d) :
    BNExists (addEdge H x y hxy) r d := by
  obtain ⟨D, hDegree, hRank, hSecant⟩ := hNear
  obtain ⟨n, hn⟩ := hNormalizes D hDegree hRank hSecant
  refine ⟨D + n • seamDivisor x y, ?_, hn⟩
  rw [deg_on_addEdge, deg_add_zsmul_seamDivisor, hDegree]

/-- Rank-zero edge normalization follows from divisor-level phase transfer and
does not require a Brill--Noether inequality. -/
theorem EdgeNormalizes_rank_zero
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (d : ℤ) :
    EdgeNormalizes H x y hxy 0 d := by
  intro D _hDegree hRank _hSecant
  have hRankGeq : rank_geq H D 0 :=
    (rank_geq_iff H D 0).mpr hRank
  have hWinnable : winnable H D :=
    (rank_nonneg_iff_winnable H D).mp hRankGeq
  obtain ⟨n, hn⟩ := winnable_phase_transfer H x y hxy D hWinnable
  refine ⟨n, (rank_geq_iff (addEdge H x y hxy)
    (D + n • seamDivisor x y) 0).mp ?_⟩
  exact (rank_nonneg_iff_winnable (addEdge H x y hxy)
    (D + n • seamDivisor x y)).mpr hn

/-- Rank-zero near rectangles exist in every nonnegative degree. -/
theorem NearRectangle_rank_zero
    (H : CFGraph) (x y : H.V) {d : ℤ} (hd : 0 ≤ d) :
    NearRectangle H x y 0 d := by
  let v : H.V := Classical.arbitrary H.V
  let D : CFDiv H := d.toNat • one_chip v
  have hEffective : effective D :=
    (Eff H).nsmul_mem (eff_one_chip v) d.toNat
  have hDegree : deg D = d := by
    dsimp [D]
    simpa [Int.toNat_of_nonneg hd] using
      (AddMonoidHom.map_nsmul deg d.toNat (one_chip v))
  have hRankGeq : rank_geq H D 0 :=
    (rank_nonneg_iff_winnable H D).mpr
      (winnable_of_effective H D hEffective)
  refine ⟨D, hDegree, (rank_geq_iff H D 0).mp hRankGeq, ?_⟩
  simpa using rank_geq_neg_one H (D - one_chip x - one_chip y)

end MarkedGraphs
