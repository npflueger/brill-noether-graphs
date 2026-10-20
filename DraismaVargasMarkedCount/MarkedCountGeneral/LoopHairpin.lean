module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DenomRow
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropIso
public import DraismaVargasMarkedCount.MarkedCountGeneral.LoopCubic
public import DraismaVargasMarkedCount.MarkedCountGeneral.LoopSwap
public import DraismaVargasCount.PassOnceLollipop

@[expose] public section

/-!
# The loop case of the drop lemma, part 3: the hairpin, and the loop reversal

**The hairpin** (`hairpin`; Part I `lemma-loop-bridge`, the length-two clause of Part II's
`lm:bridge-and-loop`). Let `s` be a loop of the marked core at `A`, and `e, e'` the two surviving
occurrences of its row at `A`. Then `e` and `e'` lie over one target edge `t` (a leaf edge), their
sheets lie in one block at both ends of `t` (at `A`, and at the vertex `C` over the leaf), and
`m(A) = 2`. The public statements are for unmarked full-dimensional presentations, so they are
read on the regrowth of `DenomRegrow` (a caterpillar tail at every mark, one shed sheet per mark),
where `A` is a trivalent branch vertex, the loop row is the stable row `DenomRegrow.path` with the
same occurrences (`DenomRegrow.onRow_psiSE`), and the old sheets and blocks are kept
(`CatRegrow.liftPart`):

* both ends of the row lie over the leaf edge (`PassOnceLollipop.onRow_target_eq_leafEdge_of_loopRow`,
  with the leaf of `LollipopLeafRow.exists_leafRow_eq_of_loopRow`);
* over the leaf only one source vertex survives (`LollipopDivalentWitness.eq_coreVertex_of_surviving`);
* `m(A) = 2` (`LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two`).

**The loop reversal** (`exists_loop_reversal_of_cubic`). With `m(A) = 2` the sheets `i, i'` of `e`,
`e'` make up the block of `A`, so `e`, `e'` are singleton blocks over `t`, and the sheet swap
`(i i')` over `t` (`LoopSwap.exists_swap`) is an automorphism of the typed frame carrying `e` to
`e'`.

The regrowth needs the marks to be distinct source vertices (`IsMarkedCubic`).

**Imports.** Like `DenomRegrow`, this module avoids `RegrowFrame`, `RegrowAssemble` and
`Restriction`, whose closure contains `RigidSpine` (whose `MarkedCountGeneral.eq_or_eq_otherEnd`
would shadow `W4StableSource.eq_or_eq_otherEnd` in `DropUnique`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.RowWalk (OnRow)
open Utilities.Certificate.ExplicitPotential (Core)

namespace LoopHairpin

open CatRegrow

/-- **Over a leaf of a full-dimensional presentation at most one source vertex survives.** -/
theorem eq_of_surviving_over_leaf {target : CFGraph.{0}} {degree : ℕ}
    {data : GluingDatum target degree} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fd : FullDimensionalSourcePresentation data coordinate)
    {u : target.V} (hu : Count.IsLeafVertex target u) {X Y : data.SourceVertex}
    (hX : X.1.1 = u) (hY : Y.1.1 = u) (hXp : 0 < nonDanglingValency data X)
    (hYp : 0 < nonDanglingValency data Y) : X = Y := by
  have key : ∀ Z : data.SourceVertex, Z.1.1 = u → 0 < nonDanglingValency data Z →
      Z = LeafFibre.coreVertex fd hu := by
    intro Z hZ hZp
    subst hZ
    exact LollipopDivalentWitness.eq_coreVertex_of_surviving fd hZp hu
  exact (key X hX hXp).trans (key Y hY hYp).symm

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  (φ : TypedFrame core mark types degree) (hc : IsMarkedCubic core mark)

local notation "β" => DenomRegrow.branching φ

/-- An occurrence is incident to the source vertex over either end of its target edge, through its
own sheet. -/
theorem incident_sourceEndpoint {target : CFGraph} {d : ℕ} (data : GluingDatum target d)
    (E : data.SourceEdge) {v : target.V}
    (hv : (E.1.1 : target.V × target.V).1 = v ∨ (E.1.1 : target.V × target.V).2 = v) :
    Incident data E (data.sourceEndpoint v E.1.2) := by
  rcases hv with h | h
  · left; rw [← h]; rfl
  · right; rw [← h]; rfl

include hc in
/-- **The hairpin** (Part I `lemma-loop-bridge`). The two surviving occurrences `e, e'` of the row
of a loop slot `s` at its branch vertex `A` lie over one target edge, their sheets lie in one block
at both ends of it, and `m(A) = 2`. -/
theorem hairpin {s : Fin p} (hLoop : core.tail s = core.head s)
    {e e' : NonDanglingEdge φ.data}
    (he : Incident φ.data e.1 (φ.ident.vertex.symm (core.tail s)).1)
    (he' : Incident φ.data e'.1 (φ.ident.vertex.symm (core.tail s)).1)
    (hRe : φ.ident.row (markedRow (markSet φ.markSource) e) = s)
    (hRe' : φ.ident.row (markedRow (markSet φ.markSource) e') = s) :
    e'.1.1.1 = e.1.1.1 ∧
      (∀ v, ((e.1.1.1 : φ.target.V × φ.target.V).1 = v ∨
          (e.1.1.1 : φ.target.V × φ.target.V).2 = v) →
        (φ.data.vertexPartition v).Rel e.1.1.2 e'.1.1.2) ∧
      markIndex φ.data (φ.ident.vertex.symm (core.tail s)).1 = 2 := by
  set A := (φ.ident.vertex.symm (core.tail s)).1 with hA
  set fd := DenomRegrow.fullDim φ hc
  have hPs : markedRow (markSet φ.markSource) e = φ.ident.row.symm s :=
    (Equiv.eq_symm_apply _).mpr hRe
  have hP' : markedRow (markSet φ.markSource) e' = markedRow (markSet φ.markSource) e :=
    φ.ident.row.injective (hRe'.trans hRe.symm)
  -- the branch vertex and the loop row in the regrowth
  have hBr : 3 ≤ nonDanglingValency (β).regrowDatum ((β).psiSV A) :=
    ((β).three_le_nonDanglingValency_psiSV_iff (DenomRegrow.hψ φ) (DenomRegrow.hT φ)
      (DenomRegrow.hT0 φ) (DenomRegrow.hMark φ) (DenomRegrow.hInj φ hc) A).mpr
      (φ.ident.vertex.symm (core.tail s)).2
  have hTwo : StablePathCount.incidenceCount (β).regrowDatum ((β).psiSV A)
      (DenomRegrow.path φ (markedRow (markSet φ.markSource) e)) = 2 := by
    refine ((β).incidenceCount_psiSV_inl (DenomRegrow.hψ φ) (DenomRegrow.hT φ)
      (DenomRegrow.hT0 φ) (DenomRegrow.hMark φ) A _).trans ?_
    have h := φ.ident.incidence (φ.ident.vertex.symm (core.tail s)) s
    rw [Equiv.apply_symm_apply] at h
    rw [hPs]
    refine h.trans ?_
    rw [Count.coreIncidence, ite_eq_left rfl, ite_eq_left hLoop.symm]
  obtain ⟨leaf, hLeaf, hLeafRow⟩ :=
    LollipopLeafRow.exists_leafRow_eq_of_loopRow fd (by omega) hTwo
  have hOn : OnRow (β).regrowDatum (DenomRegrow.path φ (markedRow (markSet φ.markSource) e))
      ((β).psiSE e.1) := DenomRegrow.onRow_psiSE φ e
  have hOn' : OnRow (β).regrowDatum (DenomRegrow.path φ (markedRow (markSet φ.markSource) e))
      ((β).psiSE e'.1) := by
    rw [← hP']; exact DenomRegrow.onRow_psiSE φ e'
  have hT1 := PassOnceLollipop.onRow_target_eq_leafEdge_of_loopRow fd hBr hTwo hLeaf hLeafRow
    hOn (((β).incident_psiSE_psiSV _ _).mpr he)
  have hT2 := PassOnceLollipop.onRow_target_eq_leafEdge_of_loopRow fd hBr hTwo hLeaf hLeafRow
    hOn' (((β).incident_psiSE_psiSV _ _).mpr he')
  have ht : e'.1.1.1 = e.1.1.1 := by
    have h := hT2.trans hT1.symm
    simpa only [CatBranching.psiSE_target, oldE_inj] using h
  refine ⟨ht, ?_, ?_⟩
  · -- the two ends of `t`
    intro v hv
    have hInc := (incident_iff_target_mem_and_rel φ.data e.1 A).mp he
    have hInc' := (incident_iff_target_mem_and_rel φ.data e'.1 A).mp he'
    by_cases hva : v = A.1.1
    · subst hva
      exact hInc.2.symm.trans hInc'.2
    · -- `v` is the far end, the leaf
      have haEnd : (e.1.1.1 : φ.target.V × φ.target.V).1 = A.1.1 ∨
          (e.1.1.1 : φ.target.V × φ.target.V).2 = A.1.1 := (Finset.mem_filter.mp hInc.1).2
      have hLeafMem := Count.leafEdge_mem hLeaf
      rw [← hT1] at hLeafMem
      have hLeafEnd := (Finset.mem_filter.mp hLeafMem).2
      simp only [CatBranching.psiSE_target, oldE_ends] at hLeafEnd
      have hDiv := LollipopDivalent.card_incidentEdges_eq_two_of_incidenceCount_eq_two fd hBr hTwo
      have hLeafNe : leaf ≠ oldV (DenomRegrow.cc types) (β).x A.1.1 := by
        intro h
        have h1 : (GluingDatum.incidentEdges leaf).card = 1 := hLeaf
        rw [h] at h1
        change (GluingDatum.incidentEdges (oldV (DenomRegrow.cc types) (β).x A.1.1)).card = 2
          at hDiv
        omega
      have hvLeaf : oldV (DenomRegrow.cc types) (β).x v = leaf := by
        rcases hv with hv | hv <;> rcases haEnd with ha | ha <;> rcases hLeafEnd with hl | hl
        · exact absurd (hv.symm.trans ha) hva
        · exact absurd (hv.symm.trans ha) hva
        · rw [← hv]; exact hl
        · exact absurd (hl.symm.trans (by rw [ha])) hLeafNe
        · exact absurd (hl.symm.trans (by rw [ha])) hLeafNe
        · rw [← hv]; exact hl
        · exact absurd (hv.symm.trans ha) hva
        · exact absurd (hv.symm.trans ha) hva
      have hv' : (e'.1.1.1 : φ.target.V × φ.target.V).1 = v ∨
          (e'.1.1.1 : φ.target.V × φ.target.V).2 = v := by rw [ht]; exact hv
      -- the far ends survive and lie over the leaf
      obtain ⟨hS, -⟩ := hOn
      obtain ⟨hS', -⟩ := hOn'
      have hpos := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hS
        (((β).incident_psiSE_psiSV _ _).mpr (incident_sourceEndpoint φ.data e.1 hv))
      have hpos' := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hS'
        (((β).incident_psiSE_psiSV _ _).mpr (incident_sourceEndpoint φ.data e'.1 hv'))
      have hEq := eq_of_surviving_over_leaf fd hLeaf hvLeaf hvLeaf hpos hpos'
      rw [CatBranching.psiSV_inj] at hEq
      exact congrArg (fun Z : φ.data.SourceVertex ↦ Z.1.2) hEq
  · -- `m(A) = 2`
    have h := LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two fd hBr hTwo
    change (liftPart (β).e (φ.data.vertexPartition A.1.1)).blockCard (old (β).e A.1.2) = 2 at h
    rw [liftPart_blockCard_old] at h
    exact h

include hc in
/-- **The loop reversal, over a marked cubic core** (Part I `lemma-loop-bridge`): the two
surviving occurrences of the row of a loop slot at its branch vertex are exchanged by an
automorphism of the typed frame. -/
theorem exists_loop_reversal_of_cubic {s : Fin p} (hLoop : core.tail s = core.head s)
    {e e' : NonDanglingEdge φ.data}
    (he : Incident φ.data e.1 (φ.ident.vertex.symm (core.tail s)).1)
    (he' : Incident φ.data e'.1 (φ.ident.vertex.symm (core.tail s)).1)
    (hRe : φ.ident.row (markedRow (markSet φ.markSource) e) = s)
    (hRe' : φ.ident.row (markedRow (markSet φ.markSource) e') = s) :
    ∃ α : TypedFrameIso φ φ, α.datum.sourceEdgeEquiv e.1 = e'.1 := by
  by_cases hee : e = e'
  · subst hee
    exact ⟨TypedFrameIso.refl φ, rfl⟩
  obtain ⟨ht, hRel, hm⟩ := hairpin φ hc hLoop he he' hRe hRe'
  set A := (φ.ident.vertex.symm (core.tail s)).1 with hA
  set i := e.1.1.2
  set i' := e'.1.1.2
  have hne : i ≠ i' := by
    intro h
    exact hee (Subtype.ext (Subtype.ext (Prod.ext ht.symm h)))
  have hInc := (incident_iff_target_mem_and_rel φ.data e.1 A).mp he
  have hInc' := (incident_iff_target_mem_and_rel φ.data e'.1 A).mp he'
  -- the block of `A` is `{i, i'}`
  have hBlock : ∀ j, (φ.data.vertexPartition A.1.1).Rel A.1.2 j → j = i ∨ j = i' := by
    intro j hj
    have hSub : ({i, i', j} : Finset (Fin degree)) ⊆ (φ.data.vertexPartition A.1.1).block A.1.2 := by
      intro x hx
      rw [SheetPartition.mem_block_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hInc.2
      · exact hInc'.2
      · exact hj
    have hCard := Finset.card_le_card hSub
    have hm' : ((φ.data.vertexPartition A.1.1).block A.1.2).card = 2 := hm
    rw [hm'] at hCard
    by_contra hNo
    push Not at hNo
    rw [Finset.card_insert_of_notMem (by simp [hne, Ne.symm hNo.1]),
      Finset.card_pair (Ne.symm hNo.2)] at hCard
    omega
  -- the edge partition refines the vertex partition at `A`
  have hRefines : (φ.data.edgePartition e.1.1.1).Refines (φ.data.vertexPartition A.1.1) := by
    rcases (Finset.mem_filter.mp hInc.1).2 with h | h
    · rw [← h]; exact φ.data.refines_left _
    · rw [← h]; exact φ.data.refines_right _
  have hrep : (φ.data.edgePartition e.1.1.1).repr i = i := e.1.2
  have hrep' : (φ.data.edgePartition e.1.1.1).repr i' = i' := by
    have := e'.1.2
    rw [ht] at this
    exact this
  refine LoopSwap.exists_swap φ ht ?_ ?_ hRel (hRe.trans hRe'.symm)
  · intro j hj
    rcases hBlock j (hInc.2.trans (hRefines.rel hj)) with h | h
    · exact h
    · exfalso
      rw [h] at hj
      exact hne (hrep.symm.trans (hj.trans hrep'))
  · intro j hj
    rcases hBlock j (hInc'.2.trans (hRefines.rel hj)) with h | h
    · exfalso
      rw [h] at hj
      exact hne (hrep'.symm.trans (hj.trans hrep)).symm
    · exact h

end LoopHairpin

end DraismaVargas.Count.MarkedCountGeneral
