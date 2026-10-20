module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowStable
public import DraismaVargas.LocalCases.StableSourceMatrix

@[expose] public section

/-!
# Regrowth, part 8: the length matrix of the regrown datum

The matrix of the regrowth is `A_{ψ;u} ⊕ diag(1/s_i; 1/2, …; 2, …)`. The natural length matrix
`StableSourceMatrix.matrix` of `regrowDatum β`, at the rows of `stablePathEquiv` and the columns of
`occEquiv`, is block diagonal:

* a marked row of `ψ` over an old edge: the natural marked matrix of `ψ` (`matrix_inl_oldE`);
* the row of a tail slot over its own slot: `tailDiag t`, which is `1/|P_i|` over a path slot,
  `1/2` over a bridge, and `2` over a leaf edge (two edges of index one);
* zero everywhere else.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount (MarkedStablePath markedRow markedMatrix)

namespace CatBranching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-! ## 1.  Indices -/

theorem sourceEdgeIndex_psiSE (F : ψ.SourceEdge) :
    β.regrowDatum.sourceEdgeIndex (β.psiSE F) = ψ.sourceEdgeIndex F := by
  unfold GluingDatum.sourceEdgeIndex
  simp only [psiSE, ep_oldE, liftPart_blockCard_old]

theorem sourceEdgeIndex_tailSE (t : TE c) (q : Fin d) :
    β.regrowDatum.sourceEdgeIndex (β.tailSE t q) =
      if q ∈ β.eB t then (β.eB t).card else 1 := by
  unfold tailSE
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, ep_tailE]
  split_ifs with h
  · exact blockPart_blockCard_of_mem (β.eA_anchored t) h
  · exact blockPart_blockCard_of_not_mem (β.eA_anchored t) h

/-- **The diagonal entry of the row of a tail slot**: the sum of `1/index` over its surviving
edges. -/
def tailDiag (t : TE c) : ℚ :=
  ∑ q : {q // q ∈ β.rowIdx t}, (1 : ℚ) / β.regrowDatum.sourceEdgeIndex (β.tailSE t q.1)

theorem tailDiag_pos (t : TE c) : 0 < β.tailDiag t := by
  unfold tailDiag
  have hne : (Finset.univ : Finset {q // q ∈ β.rowIdx t}).Nonempty :=
    ⟨⟨_, β.rowAnchor_mem t⟩, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun q _ ↦ ?_) hne
  have := GluingDatum.sourceEdgeIndex_pos β.regrowDatum (β.tailSE t q.1)
  positivity

/-- The diagonal entry over a leaf edge is `2`. -/
theorem tailDiag_loop (j : Fin k) (i : Fin (c j + 1)) : β.tailDiag ⟨j, loop i⟩ = 2 := by
  unfold tailDiag
  have h1 : ∀ q : {q // q ∈ β.rowIdx ⟨j, loop i⟩},
      (1 : ℚ) / β.regrowDatum.sourceEdgeIndex (β.tailSE ⟨j, loop i⟩ q.1) = 1 := by
    intro q
    rw [sourceEdgeIndex_tailSE,
      ite_eq_right (show q.1 ∉ β.eB ⟨j, loop i⟩ from Finset.notMem_empty _)]
    norm_num
  rw [Fintype.sum_congr _ _ h1, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    card_rowIdx, ite_eq_left ⟨i, rfl⟩]
  norm_num

/-- The diagonal entry over a path or bridge slot is `1/|block|`. -/
theorem tailDiag_of_not_loop {t : TE c} (ht : ∀ i, t.2 ≠ loop i) :
    β.tailDiag t = 1 / (β.eB t).card := by
  unfold tailDiag
  have hidx : β.rowIdx t = {β.eA t} := (β.chain t.1).rowIdx_of_not_loop ht
  have hmem : β.eA t ∈ β.eB t := (β.valid t.1).eA_mem ht
  have h1 : ∀ q : {q // q ∈ β.rowIdx t},
      (1 : ℚ) / β.regrowDatum.sourceEdgeIndex (β.tailSE t q.1) = 1 / (β.eB t).card := by
    rintro ⟨q, hq⟩
    rw [hidx, Finset.mem_singleton] at hq
    subst hq
    rw [sourceEdgeIndex_tailSE, ite_eq_left hmem]
  rw [Fintype.sum_congr _ _ h1, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hidx,
    Finset.card_singleton, one_smul]

/-! ## 2.  The entries -/

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)

include hψ hT hT0 hMark

open Classical in
/-- An entry of the natural matrix of the regrowth, by rows. -/
theorem matrix_tagPath (tag : MarkedStablePath ψ β.marks ⊕ TE c)
    (col : (catTarget c T β.x).edges) :
    StableSourceMatrix.matrix β.regrowDatum (β.tagPath hψ hT hT0 hMark tag) col =
      (∑ F : NonDanglingEdge ψ,
          if Sum.inl (markedRow β.marks F) = tag ∧ oldE c β.x F.1.1.1 = col
            then (1 : ℚ) / ψ.sourceEdgeIndex F.1 else 0) +
        ∑ t, ∑ q : {q // q ∈ β.rowIdx t},
          if Sum.inr t = tag ∧ tailE c β.x t = col
            then (1 : ℚ) / β.regrowDatum.sourceEdgeIndex (β.tailSE t q.1) else 0 := by
  rw [MarkedCount.Regrow.matrix_eq_sum, β.sum_nonDanglingEdge hψ hT hT0 hMark]
  simp only [stablePath_eq_tagPath_iff, rowTag_oldND, rowTag_tailND]
  congr 1
  refine Fintype.sum_congr _ _ fun F ↦ ?_
  simp only [oldND, psiSE_target, sourceEdgeIndex_psiSE]

open Classical in
theorem matrix_inl_oldE (P : MarkedStablePath ψ β.marks) (ε : T.edges) :
    StableSourceMatrix.matrix β.regrowDatum (β.tagPath hψ hT hT0 hMark (.inl P)) (oldE c β.x ε) =
      ∑ F : NonDanglingEdge ψ,
        if markedRow β.marks F = P ∧ F.1.1.1 = ε then (1 : ℚ) / ψ.sourceEdgeIndex F.1 else 0 := by
  rw [matrix_tagPath]
  simp

theorem matrix_inl_tailE (P : MarkedStablePath ψ β.marks) (t : TE c) :
    StableSourceMatrix.matrix β.regrowDatum (β.tagPath hψ hT hT0 hMark (.inl P)) (tailE c β.x t) =
      0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_inr_oldE (t : TE c) (ε : T.edges) :
    StableSourceMatrix.matrix β.regrowDatum (β.tagPath hψ hT hT0 hMark (.inr t)) (oldE c β.x ε) =
      0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_inr_tailE (t t' : TE c) :
    StableSourceMatrix.matrix β.regrowDatum (β.tagPath hψ hT hT0 hMark (.inr t)) (tailE c β.x t') =
      if t = t' then β.tailDiag t else 0 := by
  classical
  rw [matrix_tagPath]
  simp only [reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, zero_add, Sum.inr.injEq,
    tailE_inj]
  rw [Finset.sum_eq_single t]
  · by_cases h : t = t'
    · subst h
      simp only [and_self, ite_true]
      rfl
    · simp [h]
  · intro t'' _ ht''
    exact Finset.sum_eq_zero fun q _ ↦ ite_eq_right fun h ↦ ht'' h.1
  · simp

end CatBranching

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
