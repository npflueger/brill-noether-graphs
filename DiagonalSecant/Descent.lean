module

public import DiagonalSecant.Defs
public import Utilities.Subdivision.OddSubdivisionDescent

@[expose] public section

/-!
# Descent of the diagonal witness to the graph itself

This is the descent with two residual chips of `Research/genus-six-brill-noether-rank.md` §2.2.
Nearest rounding at an odd scale, with the chips at `u` fixed, moves the two residual chips to
vertices of the unit presentation (`Spec.exists_coarse_completion_two`, as in
`GenusSixExistence.BrillNoetherRank.of_oddCompletionWitness`); the transport to `G` itself is the
unit-presentation equivalence `UnitSubdivisionPresentation.laplacianEquiv G`.
-/

namespace DiagonalSecant

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- **Descent with two residual chips** for the diagonal witness: nearest rounding at the odd
scale keeps the chips at `u` and moves the two residual chips to vertices of the unit
presentation. -/
theorem exists_completion_of_diagonalOddWitness {G : CFGraph.{0}} {m : ℕ}
    {u : (UnitSubdivisionPresentation.spec G).graph.V} (h : DiagonalOddWitness G m u) :
    ∃ B : CFDiv (UnitSubdivisionPresentation.spec G).graph, effective B ∧ deg B = 2 ∧
      rank (UnitSubdivisionPresentation.spec G).graph (m • one_chip u + B) ≥ 1 := by
  obtain ⟨N, hN, hodd, F, hF, hFdeg, hFrank⟩ := h
  exact Spec.exists_coarse_completion_two _ N hN hodd (m • one_chip u) F hF hFdeg hFrank

/-- **Transport to `G` itself** along the unit presentation. -/
theorem exists_completion_on_graph {G : CFGraph.{0}} {m : ℕ} (u : G.V)
    (h : DiagonalOddWitness G m ((UnitSubdivisionPresentation.laplacianEquiv G) u)) :
    ∃ F : CFDiv G, effective F ∧ deg F = 2 ∧ rank G (m • one_chip u + F) ≥ 1 := by
  set L := UnitSubdivisionPresentation.laplacianEquiv G
  obtain ⟨B, hB, hBdeg, hBrank⟩ := exists_completion_of_diagonalOddWitness h
  refine ⟨L.symm.mapDiv B, (L.symm.effective_mapDiv_iff B).mpr hB,
    by rw [L.symm.deg_mapDiv]; exact hBdeg, ?_⟩
  have hmap : L.mapDiv (m • one_chip u + L.symm.mapDiv B) = m • one_chip (L u) + B := by
    rw [L.mapDiv_add, L.mapDiv_symm]
    congr 1
    change (fun y ↦ (m • one_chip u) (L.toEquiv.symm y)) = m • one_chip (L u)
    rw [← L.mapDiv_one_chip]
    rfl
  rw [← L.rank_mapDiv_ge_iff, hmap]
  exact hBrank

end DiagonalSecant
