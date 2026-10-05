module

public import DraismaVargas.LocalCases.ResolutionM1k

@[expose] public section

/-!
# The local resolutions in case `w2-r2-nd3-M-kk`

Figure 34 starts with two distinct blocks of sizes `k₁` and `k₂` at one side
of the wall.  Candidate 1 detaches one sheet from the first block, candidate 2
does the same to the second block, and candidate 3 retains the joined wall
block.  The unlisted detached singleton accounts for the one-unit discrepancy
in the displayed non-dangling indices.

All candidates have divalent new endpoints, so their Riemann--Hurwitz checks
follow uniformly from positivity of induced block counts.  The final receipt
combines the exact indices with Equation (8).
-/

namespace DraismaVargas.LocalCases.ResolutionMkk

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k

/-- Detach one sheet from a chosen endpoint block and join the other endpoint
to the whole wall partition. -/
def detachedResolution (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) : LocalResolution d where
  left := endpoint
  right := wall
  newEdge := endpoint.detachSheet single remainder hne hTogether
  edge_refines_left :=
    endpoint.detachSheet_refines single remainder hne hTogether
  edge_refines_right :=
    (endpoint.detachSheet_refines single remainder hne hTogether).trans
      hEndpointRefines

theorem detachedResolution_contracts (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (detachedResolution wall endpoint single remainder hne hTogether
      hEndpointRefines).ContractsTo wall :=
  SheetPartition.isJoin_right_of_refines hEndpointRefines

theorem detachedResolution_left_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (detachedResolution wall endpoint single remainder hne hTogether
        hEndpointRefines).left
      [(detachedResolution wall endpoint single remainder hne hTogether
        hEndpointRefines).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem detachedResolution_right_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (detachedResolution wall endpoint single remainder hne hTogether
        hEndpointRefines).right
      [(detachedResolution wall endpoint single remainder hne hTogether
        hEndpointRefines).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem detachedResolution_newEdge_blockCard_single
    (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (detachedResolution wall endpoint single remainder hne hTogether
      hEndpointRefines).newEdge.blockCard single = 1 :=
  endpoint.detachSheet_blockCard_single single remainder hne hTogether

theorem detachedResolution_newEdge_blockCard_remainder
    (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (k : ℕ)
    (hCard : endpoint.blockCard single = k) :
    (detachedResolution wall endpoint single remainder hne hTogether
      hEndpointRefines).newEdge.blockCard remainder = k - 1 := by
  rw [detachedResolution,
    endpoint.detachSheet_blockCard_remainder single remainder hne hTogether,
    hCard]

/-- A block disjoint from the detached sheet keeps its old index. -/
theorem detachedResolution_newEdge_blockCard_other
    (wall endpoint : SheetPartition d)
    (single remainder other : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall)
    (hOther : ¬endpoint.Rel single other) :
    (detachedResolution wall endpoint single remainder hne hTogether
      hEndpointRefines).newEdge.blockCard other = endpoint.blockCard other :=
  endpoint.detachSheet_blockCard_of_not_rel single remainder other hne hTogether
    hOther

/-- The full arbitrary-degree local receipt for Figure 34 and Equation (8). -/
theorem mkk_block_resolution
    {d : ℕ} (wall endpoint : SheetPartition d)
    (first firstRemainder second secondRemainder : Fin d)
    (hEndpointRefines : endpoint.Refines wall)
    (_hWallTogether : wall.Rel first second)
    (hSeparate : ¬endpoint.Rel first second)
    (hFirstTogether : endpoint.Rel first firstRemainder)
    (hSecondTogether : endpoint.Rel second secondRemainder)
    (hneFirst : first ≠ firstRemainder)
    (hneSecond : second ≠ secondRemainder)
    (k₁ k₂ : ℕ) (hk₁ : 1 < k₁) (hk₂ : 1 < k₂)
    (hFirstCard : endpoint.blockCard first = k₁)
    (hSecondCard : endpoint.blockCard second = k₂)
    (hWallCard : wall.blockCard first = k₁ + k₂)
    (firstExternalLeft firstExternalRight secondExternalLeft
      secondExternalRight thirdExternalLeft thirdExternalRight :
      SheetPartition d)
    (hFirstExternalLeft : firstExternalLeft.Refines endpoint)
    (hFirstExternalRight : firstExternalRight.Refines wall)
    (hSecondExternalLeft : secondExternalLeft.Refines endpoint)
    (hSecondExternalRight : secondExternalRight.Refines wall)
    (hThirdExternalLeft : thirdExternalLeft.Refines wall)
    (hThirdExternalRight : thirdExternalRight.Refines wall)
    {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ / (k₁ : ℚ) + c₂ / (k₂ : ℚ) + s = 0)
    (hright : c₃ / ((k₁ : ℚ) + k₂ - 1) + s = 0) :
    let firstCandidate := detachedResolution wall endpoint first firstRemainder
      hneFirst hFirstTogether hEndpointRefines
    let secondCandidate := detachedResolution wall endpoint second secondRemainder
      hneSecond hSecondTogether hEndpointRefines
    firstCandidate.ContractsTo wall ∧
      secondCandidate.ContractsTo wall ∧
      (thirdResolution wall).ContractsTo wall ∧
      firstExternalLeft.Refines firstCandidate.left ∧
      firstExternalRight.Refines firstCandidate.right ∧
      secondExternalLeft.Refines secondCandidate.left ∧
      secondExternalRight.Refines secondCandidate.right ∧
      thirdExternalLeft.Refines (thirdResolution wall).left ∧
      thirdExternalRight.Refines (thirdResolution wall).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall firstCandidate.left
        [firstCandidate.newEdge, firstExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall firstCandidate.right
        [firstCandidate.newEdge, firstExternalRight] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall secondCandidate.left
        [secondCandidate.newEdge, secondExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall secondCandidate.right
        [secondCandidate.newEdge, secondExternalRight] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).left
        [(thirdResolution wall).newEdge, thirdExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).right
        [(thirdResolution wall).newEdge, thirdExternalRight] first ∧
      firstCandidate.newEdge.blockCard first = 1 ∧
      firstCandidate.newEdge.blockCard firstRemainder = k₁ - 1 ∧
      firstCandidate.newEdge.blockCard second = k₂ ∧
      secondCandidate.newEdge.blockCard second = 1 ∧
      secondCandidate.newEdge.blockCard secondRemainder = k₂ - 1 ∧
      secondCandidate.newEdge.blockCard first = k₁ ∧
      (thirdResolution wall).newEdge.blockCard first = k₁ + k₂ ∧
      PositiveBalanceThree
        ![(k₁ : ℚ) - 1, (k₂ : ℚ) - 1, (k₁ : ℚ) + k₂]
        ![c₁ / ((k₁ : ℚ) - 1) + c₂ / (k₂ : ℚ) + s,
          c₁ / (k₁ : ℚ) + c₂ / ((k₂ : ℚ) - 1) + s,
          c₃ / ((k₁ : ℚ) + k₂) + s] := by
  dsimp only
  have hSeparateSymm : ¬endpoint.Rel second first := by
    intro h
    exact hSeparate h.symm
  have hk₁Q : (1 : ℚ) < (k₁ : ℚ) := by exact_mod_cast hk₁
  have hk₂Q : (1 : ℚ) < (k₂ : ℚ) := by exact_mod_cast hk₂
  refine ⟨detachedResolution_contracts wall endpoint first firstRemainder
      hneFirst hFirstTogether hEndpointRefines,
    detachedResolution_contracts wall endpoint second secondRemainder
      hneSecond hSecondTogether hEndpointRefines,
    thirdResolution_contracts wall,
    hFirstExternalLeft, hFirstExternalRight,
    hSecondExternalLeft, hSecondExternalRight,
    hThirdExternalLeft, hThirdExternalRight,
    detachedResolution_left_riemannHurwitzAtBlock wall endpoint
      firstExternalLeft first firstRemainder hneFirst hFirstTogether
      hEndpointRefines first,
    detachedResolution_right_riemannHurwitzAtBlock wall endpoint
      firstExternalRight first firstRemainder hneFirst hFirstTogether
      hEndpointRefines first,
    detachedResolution_left_riemannHurwitzAtBlock wall endpoint
      secondExternalLeft second secondRemainder hneSecond hSecondTogether
      hEndpointRefines first,
    detachedResolution_right_riemannHurwitzAtBlock wall endpoint
      secondExternalRight second secondRemainder hneSecond hSecondTogether
      hEndpointRefines first,
    thirdResolution_left_riemannHurwitzAtBlock wall thirdExternalLeft first,
    thirdResolution_right_riemannHurwitzAtBlock wall thirdExternalRight first,
    detachedResolution_newEdge_blockCard_single wall endpoint first
      firstRemainder hneFirst hFirstTogether hEndpointRefines,
    detachedResolution_newEdge_blockCard_remainder wall endpoint first
      firstRemainder hneFirst hFirstTogether hEndpointRefines k₁ hFirstCard,
    (detachedResolution_newEdge_blockCard_other wall endpoint first
      firstRemainder second hneFirst hFirstTogether hEndpointRefines
      hSeparate).trans hSecondCard,
    detachedResolution_newEdge_blockCard_single wall endpoint second
      secondRemainder hneSecond hSecondTogether hEndpointRefines,
    detachedResolution_newEdge_blockCard_remainder wall endpoint second
      secondRemainder hneSecond hSecondTogether hEndpointRefines k₂ hSecondCard,
    (detachedResolution_newEdge_blockCard_other wall endpoint second
      secondRemainder first hneSecond hSecondTogether hEndpointRefines
      hSeparateSymm).trans hFirstCard, ?_,
    balance_M_kk hk₁Q hk₂Q hleft hright⟩
  change wall.blockCard first = k₁ + k₂
  exact hWallCard


/-! ## Block counting: `detachedResolution` is not the genus-preserving shape

`GlobalResolution.sourceGraph_genus_eq_iff_block_card` says a resolution keeps
the source genus exactly when

`#newEdge.Blocks + #wall.Blocks = #left.Blocks + #right.Blocks`.

`detachedResolution` above detaches on the new edge only and keeps the whole
wall partition at the retained endpoint, so its left-hand side is one too
large: over `t₁` the detached singleton and the residual class join the same
two ends, which is the parallel pair over `t₁` that Draisma--Vargas exclude by
the no-cycle argument in their description of Position II.b (Part I, Case
`{w3}`).  `bothDetachedResolution` below is the shape
the source actually produces -- Figure 29's Position II.b, and equally
Figure 34's `M⁽¹⁾`, whose retained class `A⁽¹⁾ = e₃` has `|A₀| - 1` sheets --
and its Euler count closes exactly.  Both counts are recorded here as
`detachedResolution_card_blocks` and `bothDetachedResolution_card_blocks`; the
genus consequences are drawn in `W3ShiftShrinkExistence`.

`detachedResolution` and the lemmas about it are kept unchanged, since other
modules use them; where the source genus must be preserved,
`bothDetachedResolution` is the shape to use.
-/

private theorem card_blocks_eq_card_filter (partition : SheetPartition d) :
    Fintype.card partition.Blocks =
      ((Finset.univ : Finset (Fin d)).filter fun sheet ↦
        partition.repr sheet = sheet).card := by
  change Fintype.card {sheet : Fin d // partition.repr sheet = sheet} = _
  rw [Fintype.card_subtype]

/-- **Detaching one sheet adds exactly one block.**  A general `SheetPartition`
fact, stated here next to its use. -/
theorem card_blocks_detachSheet (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    Fintype.card (partition.detachSheet single remainder hne hTogether).Blocks =
      Fintype.card partition.Blocks + 1 := by
  classical
  have hReprRel : partition.Rel single (partition.repr single) :=
    partition.rel_repr_right single
  have hMemS : partition.repr single ∈
      (Finset.univ : Finset (Fin d)).filter (fun sheet ↦ partition.repr sheet = sheet) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, partition.repr_idem single⟩
  have hEq : ((Finset.univ : Finset (Fin d)).filter fun sheet ↦
        (partition.detachSheet single remainder hne hTogether).repr sheet = sheet) =
      insert single (insert remainder
        (((Finset.univ : Finset (Fin d)).filter fun sheet ↦
          partition.repr sheet = sheet).erase (partition.repr single))) := by
    ext sheet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_erase]
    constructor
    · intro hFixed
      by_cases hSingle : sheet = single
      · exact Or.inl hSingle
      · by_cases hBlock : partition.Rel single sheet
        · refine Or.inr (Or.inl ?_)
          rw [partition.detachSheet_repr_of_rel_of_ne single remainder sheet hne
            hTogether hSingle hBlock] at hFixed
          exact hFixed.symm
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · intro hRepr
            exact hBlock (hRepr ▸ hReprRel)
          · rw [partition.detachSheet_repr_of_not_rel single remainder sheet hne
              hTogether hBlock] at hFixed
            exact hFixed
    · rintro (hSheet | hSheet | ⟨hNeRepr, hFixed⟩)
      · rw [hSheet]
        exact partition.detachSheet_repr_single single remainder hne hTogether
      · rw [hSheet]
        exact partition.detachSheet_repr_of_rel_of_ne single remainder remainder hne
          hTogether hne.symm hTogether
      · have hBlock : ¬partition.Rel single sheet := by
          intro hRel
          exact hNeRepr (by rw [show partition.repr single = partition.repr sheet from hRel,
            hFixed])
        rw [partition.detachSheet_repr_of_not_rel single remainder sheet hne
          hTogether hBlock]
        exact hFixed
  have hRemainderNotMem : remainder ∉
      (((Finset.univ : Finset (Fin d)).filter fun sheet ↦
        partition.repr sheet = sheet).erase (partition.repr single)) := by
    intro hMem
    obtain ⟨hNe, hFix⟩ := Finset.mem_erase.mp hMem
    exact hNe ((show partition.repr single = partition.repr remainder from hTogether).trans
      (Finset.mem_filter.mp hFix).2).symm
  have hSingleNotMem : single ∉ insert remainder
      (((Finset.univ : Finset (Fin d)).filter fun sheet ↦
        partition.repr sheet = sheet).erase (partition.repr single)) := by
    intro hMem
    rcases Finset.mem_insert.mp hMem with hSwap | hErase
    · exact hne hSwap
    · exact (Finset.mem_erase.mp hErase).1 (Finset.mem_filter.mp
        (Finset.mem_of_mem_erase hErase)).2.symm
  have hPos : 0 < ((Finset.univ : Finset (Fin d)).filter fun sheet ↦
      partition.repr sheet = sheet).card := Finset.card_pos.mpr ⟨_, hMemS⟩
  rw [card_blocks_eq_card_filter, card_blocks_eq_card_filter, hEq,
    Finset.card_insert_of_notMem hSingleNotMem,
    Finset.card_insert_of_notMem hRemainderNotMem,
    Finset.card_erase_of_mem hMemS]
  omega

/-- **The Euler defect of `detachedResolution`: one too many new-edge blocks.**
This is the exact failure of
`GlobalResolution.sourceGraph_genus_eq_iff_block_card`, recorded on the
definition as it stands. -/
theorem detachedResolution_card_blocks (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    Fintype.card (detachedResolution wall endpoint single remainder hne hTogether
          hEndpointRefines).newEdge.Blocks +
        Fintype.card wall.Blocks =
      Fintype.card (detachedResolution wall endpoint single remainder hne hTogether
          hEndpointRefines).left.Blocks +
        Fintype.card (detachedResolution wall endpoint single remainder hne hTogether
          hEndpointRefines).right.Blocks + 1 := by
  show Fintype.card (endpoint.detachSheet single remainder hne hTogether).Blocks +
      Fintype.card wall.Blocks =
    Fintype.card endpoint.Blocks + Fintype.card wall.Blocks + 1
  rw [card_blocks_detachSheet endpoint single remainder hne hTogether]
  omega

/-- **Position II.b's local resolution, detaching on both sides.**  The
divalent endpoint keeps its own class, the new edge is that class with one
sheet detached, and the retained endpoint detaches the *same* sheet from the
whole wall block.  This is the shape the source produces wherever a `k - 1`
new-edge index appears next to an unchanged endpoint class: Figure 29's
Position II.b (`A⁽ᵠ⁾ = A₀ ∖ {x}`, Part I, Case `{w3}`) and Figure 34's `M⁽¹⁾`
(`A⁽¹⁾ = e₃`, of `|A₀| - 1` sheets, Case `{w2-r2-nd3-M-kk}`).

Identical in content to `W3ShiftSourceCandidates.shrinkResolution`; it is
stated here as well, next to `detachedResolution`, so that users of that shape
can reach this one without importing the `w3Shift` case. -/
def bothDetachedResolution (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) : LocalResolution d where
  left := endpoint
  right := wall.detachSheet single remainder hne hWallTogether
  newEdge := endpoint.detachSheet single remainder hne hTogether
  edge_refines_left :=
    endpoint.detachSheet_refines single remainder hne hTogether
  edge_refines_right :=
    SheetPartition.refines_detachSheet_of_block_singleton _ wall single remainder
      hne hWallTogether
      ((endpoint.detachSheet_refines single remainder hne hTogether).trans
        hEndpointRefines)
      (endpoint.detachSheet_block_single single remainder hne hTogether)

@[simp] theorem bothDetachedResolution_left (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).left = endpoint := rfl

@[simp] theorem bothDetachedResolution_right (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).right =
      wall.detachSheet single remainder hne hWallTogether := rfl

@[simp] theorem bothDetachedResolution_newEdge (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).newEdge =
      endpoint.detachSheet single remainder hne hTogether := rfl

/-- The two endpoints join back to the wall partition.  The residual new-edge
class is what carries the join across, so this is where `2 ≤ k` is consumed:
the detached sheet's own class must still meet the residual wall block. -/
theorem bothDetachedResolution_contracts (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).ContractsTo wall := by
  classical
  have hDetachedRefines :
      (wall.detachSheet single remainder hne hWallTogether).Refines wall :=
    wall.detachSheet_refines single remainder hne hWallTogether
  have hStep : ∀ sheet, wall.Rel single sheet →
      Relation.EqvGen (fun a b ↦ endpoint.Rel a b ∨
          (wall.detachSheet single remainder hne hWallTogether).Rel a b)
        single sheet := by
    intro sheet hSheet
    by_cases hSingle : sheet = single
    · subst sheet
      exact Relation.EqvGen.refl _
    · refine Relation.EqvGen.trans single remainder sheet
        (Relation.EqvGen.rel _ _ (Or.inl hTogether)) ?_
      refine Relation.EqvGen.rel _ _ (Or.inr ?_)
      show (wall.detachSheet single remainder hne hWallTogether).repr remainder =
        (wall.detachSheet single remainder hne hWallTogether).repr sheet
      rw [wall.detachSheet_repr_of_rel_of_ne single remainder remainder hne
          hWallTogether hne.symm hWallTogether,
        wall.detachSheet_repr_of_rel_of_ne single remainder sheet hne hWallTogether
          hSingle hSheet]
  intro first second
  constructor
  · intro hRel
    by_cases hFirst : wall.Rel single first
    · exact Relation.EqvGen.trans first single second
        (Relation.EqvGen.symm _ _ (hStep first hFirst))
        (hStep second (hFirst.trans hRel))
    · have hSecond : ¬wall.Rel single second := fun h ↦ hFirst (h.trans hRel.symm)
      refine Relation.EqvGen.rel _ _ (Or.inr ?_)
      show (wall.detachSheet single remainder hne hWallTogether).repr first =
        (wall.detachSheet single remainder hne hWallTogether).repr second
      rw [wall.detachSheet_repr_of_not_rel single remainder first hne hWallTogether
          hFirst,
        wall.detachSheet_repr_of_not_rel single remainder second hne hWallTogether
          hSecond]
      exact hRel
  · intro hGenerated
    induction hGenerated with
    | rel _ _ hRelation =>
        exact hRelation.elim (fun h ↦ hEndpointRefines.rel h)
          (fun h ↦ hDetachedRefines.rel h)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem bothDetachedResolution_left_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).left
      [(bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem bothDetachedResolution_right_riemannHurwitzAtBlock
    (wall endpoint external : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).right
      [(bothDetachedResolution wall endpoint single remainder hne hWallTogether
        hTogether hEndpointRefines).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem bothDetachedResolution_newEdge_blockCard_single
    (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).newEdge.blockCard single = 1 :=
  endpoint.detachSheet_blockCard_single single remainder hne hTogether

/-- Figure 29's displayed index `|e'| = k - 1`. -/
theorem bothDetachedResolution_newEdge_blockCard_remainder
    (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (k : ℕ)
    (hCard : endpoint.blockCard single = k) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).newEdge.blockCard remainder = k - 1 := by
  rw [bothDetachedResolution_newEdge,
    endpoint.detachSheet_blockCard_remainder single remainder hne hTogether, hCard]

/-- A block disjoint from the detached sheet keeps its old index. -/
theorem bothDetachedResolution_newEdge_blockCard_other
    (wall endpoint : SheetPartition d)
    (single remainder other : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall)
    (hOther : ¬endpoint.Rel single other) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).newEdge.blockCard other =
      endpoint.blockCard other :=
  endpoint.detachSheet_blockCard_of_not_rel single remainder other hne hTogether
    hOther

/-- The retained endpoint's class is the source's `A⁽ᵠ⁾`, one sheet smaller
than the wall block. -/
theorem bothDetachedResolution_right_blockCard_remainder
    (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) (a : ℕ)
    (hCard : wall.blockCard single = a) :
    (bothDetachedResolution wall endpoint single remainder hne hWallTogether
      hTogether hEndpointRefines).right.blockCard remainder = a - 1 := by
  rw [bothDetachedResolution_right,
    wall.detachSheet_blockCard_remainder single remainder hne hWallTogether, hCard]

/-- **The Euler count closes.**  Detaching the same sheet on the new edge and
on the retained endpoint adds one block to each side of
`GlobalResolution.sourceGraph_genus_eq_iff_block_card`, so a candidate built
on this resolution preserves the source genus -- see
`W3ShiftShrinkExistence`. -/
theorem bothDetachedResolution_card_blocks (wall endpoint : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hWallTogether : wall.Rel single remainder)
    (hTogether : endpoint.Rel single remainder)
    (hEndpointRefines : endpoint.Refines wall) :
    Fintype.card (bothDetachedResolution wall endpoint single remainder hne
          hWallTogether hTogether hEndpointRefines).newEdge.Blocks +
        Fintype.card wall.Blocks =
      Fintype.card (bothDetachedResolution wall endpoint single remainder hne
          hWallTogether hTogether hEndpointRefines).left.Blocks +
        Fintype.card (bothDetachedResolution wall endpoint single remainder hne
          hWallTogether hTogether hEndpointRefines).right.Blocks := by
  show Fintype.card (endpoint.detachSheet single remainder hne hTogether).Blocks +
      Fintype.card wall.Blocks =
    Fintype.card endpoint.Blocks +
      Fintype.card (wall.detachSheet single remainder hne hWallTogether).Blocks
  rw [card_blocks_detachSheet endpoint single remainder hne hTogether,
    card_blocks_detachSheet wall single remainder hne hWallTogether]
  omega

end DraismaVargas.LocalCases.ResolutionMkk
