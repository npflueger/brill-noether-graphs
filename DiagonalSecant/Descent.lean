module

public import DiagonalSecant.Defs
public import Utilities.Subdivision.OddSubdivisionDescent

@[expose] public section

/-!
# Descent of the diagonal witness to the graph itself

This is the descent with two residual chips of `Research/genus-six-brill-noether-rank.md` §2.2.
The public `BrillNoetherRank.of_oddCompletionWitness`
(`GenusSixExistence/BrillNoetherRank/Reduction.lean`) does exactly this for
`OddCompletionWitness`, through the private lemma `coarse_completion` (nearest rounding at an odd
scale with `D₀ = E` fixed and two chips, `Spec.rank_ge_of_rank_scale_ge_nearest` with the budget
`2 · roundDist < N` of `two_mul_roundDist_lt`). `coarse_completion` is `private`, so its
proof is repeated here for the one divisor `m • one_chip u`; the transport to `G` itself is the
unit-presentation equivalence `UnitSubdivisionPresentation.laplacianEquiv G`.
-/

namespace DiagonalSecant

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- Abstract two-chip completion (a copy of the private
`GenusSixExistence.BrillNoetherRank.coarse_completion`), keeping divisor algebra away from the
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

/-- **Descent with two residual chips** for the diagonal witness: nearest rounding at the odd
scale keeps the chips at `u` and moves the two residual chips to vertices of the unit
presentation. -/
theorem exists_completion_of_diagonalOddWitness {G : CFGraph.{0}} {m : ℕ}
    {u : (UnitSubdivisionPresentation.spec G).graph.V} (h : DiagonalOddWitness G m u) :
    ∃ B : CFDiv (UnitSubdivisionPresentation.spec G).graph, effective B ∧ deg B = 2 ∧
      rank (UnitSubdivisionPresentation.spec G).graph (m • one_chip u + B) ≥ 1 := by
  obtain ⟨N, hN, hodd, F, hF, hFdeg, hFrank⟩ := h
  exact coarse_completion _ N hN hodd (m • one_chip u) F hF hFdeg hFrank

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
