module

public import DraismaVargas.LocalCases.BalancingRemaining
public import DraismaVargas.LocalCases.ResolutionM1k

@[expose] public section

/-!
# Coarse/fine two-candidate wall resolutions

The source cases for Equations (4) and (5) have the same partition geometry.
One candidate retains the wall partition and the other uses an existing
endpoint refinement on the new edge. Both contract to the same wall. Their
new target has one divalent and one trivalent endpoint. The divalent check is
automatic; the trivalent check is reduced below to the exact induced-block
count inequality that the exterior incidence data must supply.
-/

namespace DraismaVargas.LocalCases.ResolutionCoarseFine

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.BalancingRemaining
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k

/-- The refined member of a coarse/fine resolution pair. -/
def fineResolution (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) : LocalResolution d where
  left := fine
  right := wall
  newEdge := fine
  edge_refines_left := SheetPartition.Refines.refl fine
  edge_refines_right := hFine

theorem fineResolution_contracts (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) :
    (fineResolution wall fine hFine).ContractsTo wall :=
  SheetPartition.isJoin_right_of_refines hFine

theorem fineResolution_left_riemannHurwitzAtBlock
    (wall fine external : SheetPartition d) (hFine : fine.Refines wall)
    (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (fineResolution wall fine hFine).left
      [(fineResolution wall fine hFine).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

/-- A trivalent endpoint satisfies Riemann--Hurwitz once its three induced
block counts dominate the endpoint block cardinality plus two. -/
theorem riemannHurwitzAtBlock_trivalent_of_counts
    (wall endpoint firstEdge secondEdge thirdEdge : SheetPartition d)
    (anchor : Fin d)
    (hCounts : ∀ sheet, wall.Rel anchor sheet →
      firstEdge.blockCountWithin endpoint sheet +
        secondEdge.blockCountWithin endpoint sheet +
        thirdEdge.blockCountWithin endpoint sheet ≥
          endpoint.blockCard sheet + 2) :
    LocalResolution.RiemannHurwitzAtBlock wall
      endpoint [firstEdge, secondEdge, thirdEdge] anchor := by
  intro sheet hSheet
  have h := hCounts sheet hSheet
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  norm_num
  omega

theorem fineResolution_right_riemannHurwitzAtBlock
    (wall fine firstExternal secondExternal : SheetPartition d)
    (hFine : fine.Refines wall) (anchor : Fin d)
    (hCounts : ∀ sheet, wall.Rel anchor sheet →
      fine.blockCountWithin wall sheet +
        firstExternal.blockCountWithin wall sheet +
        secondExternal.blockCountWithin wall sheet ≥
          wall.blockCard sheet + 2) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (fineResolution wall fine hFine).right
      [(fineResolution wall fine hFine).newEdge,
        firstExternal, secondExternal] anchor :=
  riemannHurwitzAtBlock_trivalent_of_counts _ _ _ _ _ _ hCounts

/-- Equation (4): the full block of size `k₂+k₃` and its two-block
refinement give the two valid resolutions. -/
theorem w3_nd3_t3_block_resolution
    {d : ℕ} (wall fine : SheetPartition d) (first second : Fin d)
    (hFine : fine.Refines wall) (_hWallTogether : wall.Rel first second)
    (_hFineSeparate : ¬fine.Rel first second)
    (k₂ k₃ : ℕ) (hFineFirst : fine.blockCard first = k₂)
    (hFineSecond : fine.blockCard second = k₃)
    (hWallCard : wall.blockCard first = k₂ + k₃)
    (coarseExternalLeft coarseExternalRight₁ coarseExternalRight₂
      fineExternalLeft fineExternalRight₁ fineExternalRight₂ : SheetPartition d)
    (hCoarseExternalLeft : coarseExternalLeft.Refines wall)
    (hCoarseExternalRight₁ : coarseExternalRight₁.Refines wall)
    (hCoarseExternalRight₂ : coarseExternalRight₂.Refines wall)
    (hFineExternalLeft : fineExternalLeft.Refines fine)
    (hFineExternalRight₁ : fineExternalRight₁.Refines wall)
    (hFineExternalRight₂ : fineExternalRight₂.Refines wall)
    (hCoarseCounts : ∀ sheet, wall.Rel first sheet →
      wall.blockCountWithin wall sheet +
        coarseExternalRight₁.blockCountWithin wall sheet +
        coarseExternalRight₂.blockCountWithin wall sheet ≥
          wall.blockCard sheet + 2)
    (hFineCounts : ∀ sheet, wall.Rel first sheet →
      fine.blockCountWithin wall sheet +
        fineExternalRight₁.blockCountWithin wall sheet +
        fineExternalRight₂.blockCountWithin wall sheet ≥
          wall.blockCard sheet + 2)
    {c₂ c₃ c₄ s₃ s₄ : ℚ}
    (h₃ : c₂ / (k₂ : ℚ) + c₃ / (k₃ : ℚ) + s₃ = 0)
    (h₄ : c₄ / ((k₂ : ℚ) + k₃) + s₄ = 0) :
    (thirdResolution wall).ContractsTo wall ∧
      (fineResolution wall fine hFine).ContractsTo wall ∧
      coarseExternalLeft.Refines (thirdResolution wall).left ∧
      coarseExternalRight₁.Refines (thirdResolution wall).right ∧
      coarseExternalRight₂.Refines (thirdResolution wall).right ∧
      fineExternalLeft.Refines (fineResolution wall fine hFine).left ∧
      fineExternalRight₁.Refines (fineResolution wall fine hFine).right ∧
      fineExternalRight₂.Refines (fineResolution wall fine hFine).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).left
        [(thirdResolution wall).newEdge, coarseExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).right
        [(thirdResolution wall).newEdge, coarseExternalRight₁,
          coarseExternalRight₂] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (fineResolution wall fine hFine).left
        [(fineResolution wall fine hFine).newEdge, fineExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (fineResolution wall fine hFine).right
        [(fineResolution wall fine hFine).newEdge, fineExternalRight₁,
          fineExternalRight₂] first ∧
      (thirdResolution wall).newEdge.blockCard first = k₂ + k₃ ∧
      (fineResolution wall fine hFine).newEdge.blockCard first = k₂ ∧
      (fineResolution wall fine hFine).newEdge.blockCard second = k₃ ∧
      PositiveBalance ![1, 1]
        ![c₄ / ((k₂ : ℚ) + k₃) + s₃,
          c₂ / (k₂ : ℚ) + c₃ / (k₃ : ℚ) + s₄] := by
  refine ⟨thirdResolution_contracts wall, fineResolution_contracts wall fine hFine,
    hCoarseExternalLeft, hCoarseExternalRight₁, hCoarseExternalRight₂,
    hFineExternalLeft, hFineExternalRight₁, hFineExternalRight₂,
    thirdResolution_left_riemannHurwitzAtBlock wall coarseExternalLeft first,
    riemannHurwitzAtBlock_trivalent_of_counts wall wall wall
      coarseExternalRight₁ coarseExternalRight₂ first hCoarseCounts,
    fineResolution_left_riemannHurwitzAtBlock wall fine fineExternalLeft hFine
      first,
    fineResolution_right_riemannHurwitzAtBlock wall fine fineExternalRight₁
      fineExternalRight₂ hFine first hFineCounts, ?_, hFineFirst, hFineSecond,
    balance_w3_nd3_t3 h₃ h₄⟩
  change wall.blockCard first = k₂ + k₃
  exact hWallCard

/-- Equation (5): the full block of size `k+1` and its residual block of size
`k` give the two valid resolutions. -/
theorem w3_nd2_block_resolution
    {d : ℕ} (wall fine : SheetPartition d) (anchor : Fin d)
    (hFine : fine.Refines wall) (k : ℕ)
    (hFineCard : fine.blockCard anchor = k)
    (hWallCard : wall.blockCard anchor = k + 1)
    (coarseExternalLeft coarseExternalRight₁ coarseExternalRight₂
      fineExternalLeft fineExternalRight₁ fineExternalRight₂ : SheetPartition d)
    (hCoarseExternalLeft : coarseExternalLeft.Refines wall)
    (hCoarseExternalRight₁ : coarseExternalRight₁.Refines wall)
    (hCoarseExternalRight₂ : coarseExternalRight₂.Refines wall)
    (hFineExternalLeft : fineExternalLeft.Refines fine)
    (hFineExternalRight₁ : fineExternalRight₁.Refines wall)
    (hFineExternalRight₂ : fineExternalRight₂.Refines wall)
    (hCoarseCounts : ∀ sheet, wall.Rel anchor sheet →
      wall.blockCountWithin wall sheet +
        coarseExternalRight₁.blockCountWithin wall sheet +
        coarseExternalRight₂.blockCountWithin wall sheet ≥
          wall.blockCard sheet + 2)
    (hFineCounts : ∀ sheet, wall.Rel anchor sheet →
      fine.blockCountWithin wall sheet +
        fineExternalRight₁.blockCountWithin wall sheet +
        fineExternalRight₂.blockCountWithin wall sheet ≥
          wall.blockCard sheet + 2)
    {c s₃ s₄ : ℚ}
    (h₃ : c / (k : ℚ) + s₃ = 0)
    (h₄ : c / ((k : ℚ) + 1) + s₄ = 0) :
    (thirdResolution wall).ContractsTo wall ∧
      (fineResolution wall fine hFine).ContractsTo wall ∧
      coarseExternalLeft.Refines (thirdResolution wall).left ∧
      coarseExternalRight₁.Refines (thirdResolution wall).right ∧
      coarseExternalRight₂.Refines (thirdResolution wall).right ∧
      fineExternalLeft.Refines (fineResolution wall fine hFine).left ∧
      fineExternalRight₁.Refines (fineResolution wall fine hFine).right ∧
      fineExternalRight₂.Refines (fineResolution wall fine hFine).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).left
        [(thirdResolution wall).newEdge, coarseExternalLeft] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).right
        [(thirdResolution wall).newEdge, coarseExternalRight₁,
          coarseExternalRight₂] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (fineResolution wall fine hFine).left
        [(fineResolution wall fine hFine).newEdge, fineExternalLeft] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (fineResolution wall fine hFine).right
        [(fineResolution wall fine hFine).newEdge, fineExternalRight₁,
          fineExternalRight₂] anchor ∧
      (thirdResolution wall).newEdge.blockCard anchor = k + 1 ∧
      (fineResolution wall fine hFine).newEdge.blockCard anchor = k ∧
      PositiveBalance ![1, 1]
        ![c / ((k : ℚ) + 1) + s₃, c / (k : ℚ) + s₄] := by
  refine ⟨thirdResolution_contracts wall, fineResolution_contracts wall fine hFine,
    hCoarseExternalLeft, hCoarseExternalRight₁, hCoarseExternalRight₂,
    hFineExternalLeft, hFineExternalRight₁, hFineExternalRight₂,
    thirdResolution_left_riemannHurwitzAtBlock wall coarseExternalLeft anchor,
    riemannHurwitzAtBlock_trivalent_of_counts wall wall wall
      coarseExternalRight₁ coarseExternalRight₂ anchor hCoarseCounts,
    fineResolution_left_riemannHurwitzAtBlock wall fine fineExternalLeft hFine
      anchor,
    fineResolution_right_riemannHurwitzAtBlock wall fine fineExternalRight₁
      fineExternalRight₂ hFine anchor hFineCounts, ?_, hFineCard,
    balance_w3_nd2 h₃ h₄⟩
  change wall.blockCard anchor = k + 1
  exact hWallCard

end DraismaVargas.LocalCases.ResolutionCoarseFine
