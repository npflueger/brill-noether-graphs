import DraismaVargas.LocalCases.ResolutionMkk

/-!
# The local resolutions in case `w2-r2-nd3-P`

Figure 35 has two endpoint blocks of sizes `k₁` and `k₂` plus a dangling
singleton.  Candidates 1 and 2 merge that singleton into the first or second
block, producing indices `k₁+1,k₂` and `k₁,k₂+1`.  Candidate 3 instead keeps
the endpoint wall block and detaches the singleton on the new edge, leaving
the displayed residual index `k₁+k₂`.

Every new endpoint is divalent.  The receipt below verifies contraction,
refinement, blockwise Riemann--Hurwitz, the exact indices, and Equation (9).
-/

namespace DraismaVargas.LocalCases.ResolutionP

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k

/-- Merge a dangling endpoint block into one chosen block and use that same
partition on the new edge. -/
def attachedResolution (wall endpoint : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra) : LocalResolution d where
  left := endpoint.mergeBlocks first extra hSeparate
  right := wall
  newEdge := endpoint.mergeBlocks first extra hSeparate
  edge_refines_left := SheetPartition.Refines.refl _
  edge_refines_right := endpoint.mergeBlocks_refines_coarse wall first extra
    hSeparate hEndpointRefines hWallTogether

theorem attachedResolution_contracts (wall endpoint : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra) :
    (attachedResolution wall endpoint first extra hSeparate hEndpointRefines
      hWallTogether).ContractsTo wall :=
  SheetPartition.isJoin_right_of_refines
    (endpoint.mergeBlocks_refines_coarse wall first extra hSeparate
      hEndpointRefines hWallTogether)

theorem attachedResolution_left_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (attachedResolution wall endpoint first extra hSeparate hEndpointRefines
        hWallTogether).left
      [(attachedResolution wall endpoint first extra hSeparate hEndpointRefines
        hWallTogether).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem attachedResolution_right_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (attachedResolution wall endpoint first extra hSeparate hEndpointRefines
        hWallTogether).right
      [(attachedResolution wall endpoint first extra hSeparate hEndpointRefines
        hWallTogether).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem attachedResolution_newEdge_blockCard_first
    (wall endpoint : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra)
    (hExtraSingleton : endpoint.block extra = {extra}) :
    (attachedResolution wall endpoint first extra hSeparate hEndpointRefines
      hWallTogether).newEdge.blockCard first = endpoint.blockCard first + 1 :=
  endpoint.mergeBlocks_blockCard_first_of_singleton first extra hSeparate
    hExtraSingleton

theorem attachedResolution_newEdge_blockCard_other
    (wall endpoint : SheetPartition d)
    (first extra other : Fin d) (hSeparate : ¬endpoint.Rel first extra)
    (hEndpointRefines : endpoint.Refines wall)
    (hWallTogether : wall.Rel first extra)
    (hOtherFirst : ¬endpoint.Rel other first)
    (hOtherExtra : ¬endpoint.Rel other extra) :
    (attachedResolution wall endpoint first extra hSeparate hEndpointRefines
      hWallTogether).newEdge.blockCard other = endpoint.blockCard other :=
  endpoint.mergeBlocks_blockCard_of_separate first extra other hSeparate
    hOtherFirst hOtherExtra

/-- Candidate 3 keeps the wall at both endpoints but detaches the dangling
singleton on the new edge. -/
def residualResolution (wall : SheetPartition d) (extra remainder : Fin d)
    (hne : extra ≠ remainder) (hTogether : wall.Rel extra remainder) :
    LocalResolution d where
  left := wall
  right := wall
  newEdge := wall.detachSheet extra remainder hne hTogether
  edge_refines_left := wall.detachSheet_refines extra remainder hne hTogether
  edge_refines_right := wall.detachSheet_refines extra remainder hne hTogether

theorem residualResolution_contracts (wall : SheetPartition d)
    (extra remainder : Fin d) (hne : extra ≠ remainder)
    (hTogether : wall.Rel extra remainder) :
    (residualResolution wall extra remainder hne hTogether).ContractsTo wall :=
  SheetPartition.isJoin_left_of_refines (SheetPartition.Refines.refl wall)

theorem residualResolution_left_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (extra remainder : Fin d)
    (hne : extra ≠ remainder) (hTogether : wall.Rel extra remainder)
    (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (residualResolution wall extra remainder hne hTogether).left
      [(residualResolution wall extra remainder hne hTogether).newEdge,
        external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem residualResolution_right_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (extra remainder : Fin d)
    (hne : extra ≠ remainder) (hTogether : wall.Rel extra remainder)
    (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (residualResolution wall extra remainder hne hTogether).right
      [(residualResolution wall extra remainder hne hTogether).newEdge,
        external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem residualResolution_newEdge_blockCard_remainder
    (wall : SheetPartition d) (extra remainder : Fin d)
    (hne : extra ≠ remainder) (hTogether : wall.Rel extra remainder)
    (k₁ k₂ : ℕ) (hCard : wall.blockCard extra = k₁ + k₂ + 1) :
    (residualResolution wall extra remainder hne hTogether).newEdge.blockCard
      remainder = k₁ + k₂ := by
  rw [residualResolution,
    wall.detachSheet_blockCard_remainder extra remainder hne hTogether, hCard]
  omega

/-- The arbitrary-degree local receipt for Figure 35 and Equation (9). -/
theorem p_block_resolution
    {d : ℕ} (wall endpoint : SheetPartition d)
    (first second extra : Fin d)
    (hEndpointRefines : endpoint.Refines wall)
    (hFirstSecond : ¬endpoint.Rel first second)
    (hFirstExtra : ¬endpoint.Rel first extra)
    (hSecondExtra : ¬endpoint.Rel second extra)
    (hWallFirstSecond : wall.Rel first second)
    (hWallFirstExtra : wall.Rel first extra)
    (hExtraSingleton : endpoint.block extra = {extra})
    (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hFirstCard : endpoint.blockCard first = k₁)
    (hSecondCard : endpoint.blockCard second = k₂)
    (hWallCard : wall.blockCard first = k₁ + k₂ + 1)
    (firstExternalLeft firstExternalRight secondExternalLeft
      secondExternalRight thirdExternalLeft thirdExternalRight :
      SheetPartition d)
    (hFirstExternalLeft : firstExternalLeft.Refines
      (endpoint.mergeBlocks first extra hFirstExtra))
    (hFirstExternalRight : firstExternalRight.Refines wall)
    (hSecondExternalLeft : secondExternalLeft.Refines
      (endpoint.mergeBlocks second extra hSecondExtra))
    (hSecondExternalRight : secondExternalRight.Refines wall)
    (hThirdExternalLeft : thirdExternalLeft.Refines wall)
    (hThirdExternalRight : thirdExternalRight.Refines wall)
    {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ / (k₁ : ℚ) + c₂ / (k₂ : ℚ) + s = 0)
    (hright : c₃ / ((k₁ : ℚ) + k₂ + 1) + s = 0) :
    let firstCandidate := attachedResolution wall endpoint first extra
      hFirstExtra hEndpointRefines hWallFirstExtra
    let secondCandidate := attachedResolution wall endpoint second extra
      hSecondExtra hEndpointRefines (hWallFirstSecond.symm.trans hWallFirstExtra)
    let thirdCandidate := residualResolution wall extra first
      (fun h ↦ hFirstExtra (congrArg endpoint.repr h.symm))
      hWallFirstExtra.symm
    firstCandidate.ContractsTo wall ∧
      secondCandidate.ContractsTo wall ∧
      thirdCandidate.ContractsTo wall ∧
      firstExternalLeft.Refines firstCandidate.left ∧
      firstExternalRight.Refines firstCandidate.right ∧
      secondExternalLeft.Refines secondCandidate.left ∧
      secondExternalRight.Refines secondCandidate.right ∧
      thirdExternalLeft.Refines thirdCandidate.left ∧
      thirdExternalRight.Refines thirdCandidate.right ∧
      LocalResolution.RiemannHurwitzAtBlock wall firstCandidate.left
        [firstCandidate.newEdge, firstExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall firstCandidate.right
        [firstCandidate.newEdge, firstExternalRight] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall secondCandidate.left
        [secondCandidate.newEdge, secondExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall secondCandidate.right
        [secondCandidate.newEdge, secondExternalRight] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall thirdCandidate.left
        [thirdCandidate.newEdge, thirdExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall thirdCandidate.right
        [thirdCandidate.newEdge, thirdExternalRight] first ∧
      firstCandidate.newEdge.blockCard first = k₁ + 1 ∧
      firstCandidate.newEdge.blockCard second = k₂ ∧
      secondCandidate.newEdge.blockCard first = k₁ ∧
      secondCandidate.newEdge.blockCard second = k₂ + 1 ∧
      thirdCandidate.newEdge.blockCard first = k₁ + k₂ ∧
      PositiveBalanceThree
        ![(k₁ : ℚ) + 1, (k₂ : ℚ) + 1, (k₁ : ℚ) + k₂]
        ![c₁ / ((k₁ : ℚ) + 1) + c₂ / (k₂ : ℚ) + s,
          c₁ / (k₁ : ℚ) + c₂ / ((k₂ : ℚ) + 1) + s,
          c₃ / ((k₁ : ℚ) + k₂) + s] := by
  dsimp only
  have hWallSecondExtra : wall.Rel second extra :=
    hWallFirstSecond.symm.trans hWallFirstExtra
  have hExtraNeFirst : extra ≠ first := by
    intro h
    subst extra
    exact hFirstExtra rfl
  have hFirstSecondSymm : ¬endpoint.Rel second first :=
    fun h ↦ hFirstSecond h.symm
  have hWallExtraCard : wall.blockCard extra = k₁ + k₂ + 1 := by
    unfold SheetPartition.blockCard at hWallCard ⊢
    rw [← wall.block_eq_of_rel hWallFirstExtra]
    exact hWallCard
  have hk₁Q : (0 : ℚ) < (k₁ : ℚ) := by exact_mod_cast hk₁
  have hk₂Q : (0 : ℚ) < (k₂ : ℚ) := by exact_mod_cast hk₂
  refine ⟨attachedResolution_contracts wall endpoint first extra hFirstExtra
      hEndpointRefines hWallFirstExtra,
    attachedResolution_contracts wall endpoint second extra hSecondExtra
      hEndpointRefines hWallSecondExtra,
    residualResolution_contracts wall extra first hExtraNeFirst
      hWallFirstExtra.symm,
    hFirstExternalLeft, hFirstExternalRight,
    hSecondExternalLeft, hSecondExternalRight,
    hThirdExternalLeft, hThirdExternalRight,
    attachedResolution_left_riemannHurwitzAtBlock wall endpoint
      firstExternalLeft first extra hFirstExtra hEndpointRefines
      hWallFirstExtra first,
    attachedResolution_right_riemannHurwitzAtBlock wall endpoint
      firstExternalRight first extra hFirstExtra hEndpointRefines
      hWallFirstExtra first,
    attachedResolution_left_riemannHurwitzAtBlock wall endpoint
      secondExternalLeft second extra hSecondExtra hEndpointRefines
      hWallSecondExtra first,
    attachedResolution_right_riemannHurwitzAtBlock wall endpoint
      secondExternalRight second extra hSecondExtra hEndpointRefines
      hWallSecondExtra first,
    residualResolution_left_riemannHurwitzAtBlock wall thirdExternalLeft extra
      first hExtraNeFirst hWallFirstExtra.symm first,
    residualResolution_right_riemannHurwitzAtBlock wall thirdExternalRight extra
      first hExtraNeFirst hWallFirstExtra.symm first, ?_, ?_, ?_, ?_, ?_,
    balance_P hk₁Q hk₂Q hleft hright⟩
  · rw [attachedResolution_newEdge_blockCard_first wall endpoint first extra
      hFirstExtra hEndpointRefines hWallFirstExtra hExtraSingleton, hFirstCard]
  · exact (attachedResolution_newEdge_blockCard_other wall endpoint first extra
      second hFirstExtra hEndpointRefines hWallFirstExtra hFirstSecondSymm
      hSecondExtra).trans hSecondCard
  · exact (attachedResolution_newEdge_blockCard_other wall endpoint second extra
      first hSecondExtra hEndpointRefines hWallSecondExtra hFirstSecond
      hFirstExtra).trans hFirstCard
  · rw [attachedResolution_newEdge_blockCard_first wall endpoint second extra
      hSecondExtra hEndpointRefines hWallSecondExtra hExtraSingleton, hSecondCard]
  · exact residualResolution_newEdge_blockCard_remainder wall extra first
      hExtraNeFirst hWallFirstExtra.symm k₁ k₂ hWallExtraCard

end DraismaVargas.LocalCases.ResolutionP
