module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrFrameChain

@[expose] public section

/-!
# The inverse laws, part 8: a frame is the regrowth of its own tail chains

For the decomposition theorem (the fibre over the
tail is determined by the core map). For a member `M` over the tailed core, with restriction
`ψ = TailRestrict.dat` and branching `FrameChain.branching` (module `CorrFrameChain`):

* the target dictionary `vtxEquiv : catTarget c T' x ≃ M.target` (old vertices by inclusion, tail
  vertices to the restriction's `tailVertex`) and `edgeEquiv'` (old edges by inclusion, tail slots
  to the restriction's `tEdge`), with their ends (`ends_map`);
* **`frameIso`**: the regrown datum of the branching is `M.data`, over the target dictionary, with
  identity sheet permutations (`M.data` is `ψ` with its lone sheets put back, by
  `Sheets.extendSheets_restrictSheets`, over the kept part, and one block and singletons over the
  tails, by `CorrFrameChain`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace FrameChain

noncomputable section

open DraismaVargas.Infrastructure CatSlot
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow (TailChain blockPart catTarget oldV tailV
  oldE tailE occEquiv TE TV Vtx Occ)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree) (m : ℕ) (hm : m + TailRestrict.nShed T hc M = degree)

local notation "β" => branching T hc M m hm
local notation "Tr" => TailRestrict.rTarget T hc M

/-! ## 1.  The vertices -/

/-- The image of a mark in the restricted target is the restriction's `xMark`. -/
theorem vIncl_x (j : Fin k) : vIncl ((β).x j) = TailRestrict.xMark T M j :=
  congrArg (fun X : M.data.SourceVertex ↦ X.1.1) (TailRestrict.cSV_markSrc T hc M m hm j)

/-- A tail vertex of the regrown target, as the restriction names it in `M.target`. -/
def tailVtx (w : TV c) : M.target.V := TailRestrict.tailVertex T M ⟨w.1, Equiv.sumAssoc _ _ _ w.2⟩

theorem tailVtx_spine (j : Fin k) (i : Fin (c j)) :
    tailVtx T M ⟨j, CatRegrow.TailV.spine i⟩ = TailRestrict.xSpine T M j i := rfl
theorem tailVtx_bulb (j : Fin k) (i : Fin (c j + 1)) :
    tailVtx T M ⟨j, CatRegrow.TailV.bulb i⟩ = TailRestrict.xBulb T M j i := rfl
theorem tailVtx_tip (j : Fin k) (i : Fin (c j + 1)) :
    tailVtx T M ⟨j, CatRegrow.TailV.tip i⟩ = TailRestrict.xLeaf T M j i := rfl

include hc in
theorem tailVtx_injective : Function.Injective (tailVtx T M) := by
  intro a b h
  obtain ⟨j, w⟩ := a
  obtain ⟨j', w'⟩ := b
  have h1 := TailRestrict.tailVertex_injective T hc M h
  rcases Sigma.mk.inj_iff.mp h1 with ⟨rfl, h2⟩
  have h3 : w = w' := (Equiv.sumAssoc _ _ _).injective (eq_of_heq h2)
  subst h3
  rfl

/-- The vertex map of the target dictionary. -/
def vtxFun : Vtx c Tr → M.target.V := Sum.elim vIncl (tailVtx T M)

theorem vtxFun_bijective : Function.Bijective (vtxFun T hc M) := by
  constructor
  · rintro (v | w) (v' | w') h
    · exact congrArg Sum.inl (vIncl_injective h)
    · have h' : vIncl v = tailVtx T M w' := h
      exact absurd (h' ▸ vIncl_mem v) (TailRestrict.tailVertex_notMem_Keep T M _)
    · have h' : vIncl v' = tailVtx T M w := h.symm
      exact absurd (h' ▸ vIncl_mem v') (TailRestrict.tailVertex_notMem_Keep T M _)
    · exact congrArg Sum.inr (tailVtx_injective T hc M h)
  · intro v
    by_cases hv : v ∈ TailRestrict.Keep T M
    · exact ⟨Sum.inl (vRestrict v hv), rfl⟩
    · obtain ⟨⟨j, q⟩, hq⟩ := TailRestrict.exists_tailVertex_of_notMem T M hv
      refine ⟨Sum.inr ⟨j, (Equiv.sumAssoc _ _ _).symm q⟩, ?_⟩
      change TailRestrict.tailVertex T M ⟨j, _⟩ = v
      rw [Equiv.apply_symm_apply]
      exact hq

/-- **The vertex dictionary** of the regrown target with the frame's target. -/
def vtxEquiv : (catTarget c Tr (β).x).V ≃ M.target.V :=
  Equiv.ofBijective (vtxFun T hc M) (vtxFun_bijective T hc M)

@[simp] theorem vtxEquiv_oldV (v : (Tr).V) : vtxEquiv T hc M m hm (oldV c (β).x v) = vIncl v := rfl
@[simp] theorem vtxEquiv_tailV (w : TV c) :
    vtxEquiv T hc M m hm (tailV c (β).x w) = tailVtx T M w := rfl

/-! ## 2.  The edges -/

/-- The tail slots are the deleted target edges. -/
def tailEdgeEquiv : TE c ≃ {e : M.target.edges // ¬ KeptEdge (TailRestrict.Keep T M) e} :=
  Equiv.ofBijective (fun t ↦ ⟨TailRestrict.tEdge T hc M t.1 t.2, TailRestrict.not_keptEdge_tEdge T hc M _ _⟩)
    ⟨fun _ _ h ↦ TailRestrict.tailEdge_injective T hc M (congrArg Subtype.val h), fun e ↦ by
      obtain ⟨j, s, hs⟩ := (TailRestrict.not_keptEdge_iff T hc M e.1).mp e.2
      exact ⟨⟨j, s⟩, Subtype.ext hs.symm⟩⟩

/-- The occurrence map of the target dictionary. -/
def occMap : Occ c Tr ≃ M.target.edges := by
  classical
  exact (Equiv.sumCongr (edgeEquiv (Keep := TailRestrict.Keep T M)
    (hKeep := TailRestrict.Keep_nonempty T hc M)) (tailEdgeEquiv T hc M)).trans
    (Equiv.sumCompl (KeptEdge (TailRestrict.Keep T M)))

/-- **The edge dictionary** of the regrown target with the frame's target. -/
def edgeEquiv' : (catTarget c Tr (β).x).edges ≃ M.target.edges :=
  (occEquiv c (β).x).symm.trans (occMap T hc M)

@[simp] theorem edgeEquiv'_oldE (ε : (Tr).edges) :
    edgeEquiv' T hc M m hm (oldE c (β).x ε) = edgeIncl ε := by
  unfold edgeEquiv' oldE
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem edgeEquiv'_tailE (t : TE c) :
    edgeEquiv' T hc M m hm (tailE c (β).x t) = TailRestrict.tEdge T hc M t.1 t.2 := by
  unfold edgeEquiv' tailE
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- An edge at two distinct vertices has them as its ends. -/
theorem ends_of_mem {G : CFGraph.{0}} {e : G.edges} {a b : G.V}
    (ha : e ∈ GluingDatum.incidentEdges a) (hb : e ∈ GluingDatum.incidentEdges b) (hab : a ≠ b) :
    (e : G.V × G.V) = (a, b) ∨ (e : G.V × G.V) = (b, a) := by
  have ha' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges ha
  have hb' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges hb
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact absurd (ha'.symm.trans hb') hab
  · exact Or.inl (Prod.ext ha' hb')
  · exact Or.inr (Prod.ext hb' ha')
  · exact absurd (ha'.symm.trans hb') hab

/-- The tail end of a tail slot, in `M.target`. -/
theorem vtxEquiv_tailEnd_mem (t : TE c) :
    TailRestrict.tEdge T hc M t.1 t.2 ∈
      GluingDatum.incidentEdges (vtxEquiv T hc M m hm (CatRegrow.tailEnd c (β).x t)) := by
  obtain ⟨j, s⟩ := t
  rcases CatRegrow.slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · induction i using Fin.cases with
    | zero =>
      change _ ∈ GluingDatum.incidentEdges (vIncl ((β).x j))
      rw [vIncl_x, ← TailRestrict.lowerX_zero]
      exact TailRestrict.path_mem_lowerX T hc M j 0
    | succ i =>
      change _ ∈ GluingDatum.incidentEdges (TailRestrict.xSpine T M j i)
      rw [← TailRestrict.lowerX_succ]
      exact TailRestrict.path_mem_lowerX T hc M j _
  · change _ ∈ GluingDatum.incidentEdges (TailRestrict.xSpine T M j i)
    rw [TailRestrict.incidentEdges_xSpine T hc M]; simp [CatSlot.bridge]
  · change _ ∈ GluingDatum.incidentEdges (TailRestrict.xBulb T M j i)
    rw [TailRestrict.incidentEdges_xBulb T hc M]; simp [CatSlot.loop]

/-- The head end of a tail slot, in `M.target`. -/
theorem vtxEquiv_headEnd_mem (t : TE c) :
    TailRestrict.tEdge T hc M t.1 t.2 ∈
      GluingDatum.incidentEdges (vtxEquiv T hc M m hm (CatRegrow.headEnd c (β).x t)) := by
  obtain ⟨j, s⟩ := t
  rcases CatRegrow.slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · induction i using Fin.lastCases with
    | last =>
      have hH : CatRegrow.headEnd c (β).x ⟨j, path (Fin.last (c j))⟩ =
          tailV c (β).x ⟨j, CatRegrow.TailV.bulb (Fin.last (c j))⟩ := by
        simp [CatRegrow.headEnd]
      rw [hH, vtxEquiv_tailV, tailVtx_bulb, ← TailRestrict.upperX_last]
      exact TailRestrict.path_mem_upperX T hc M j _
    | cast i =>
      have hH : CatRegrow.headEnd c (β).x ⟨j, path i.castSucc⟩ =
          tailV c (β).x ⟨j, CatRegrow.TailV.spine i⟩ := by
        simp [CatRegrow.headEnd]
      rw [hH, vtxEquiv_tailV, tailVtx_spine, ← TailRestrict.upperX_castSucc]
      exact TailRestrict.path_mem_upperX T hc M j _
  · change _ ∈ GluingDatum.incidentEdges (TailRestrict.xBulb T M j i.castSucc)
    rw [TailRestrict.incidentEdges_xBulb T hc M, bulbBridge_castSucc]; simp [CatSlot.bridge]
  · change _ ∈ GluingDatum.incidentEdges (TailRestrict.xLeaf T M j i)
    rw [TailRestrict.incidentEdges_xLeaf T hc M]; simp [CatSlot.loop]

/-- **The ends correspond.** -/
theorem ends_map (e : (catTarget c Tr (β).x).edges) :
    UnorderedEnds (vtxEquiv T hc M m hm) (e : (catTarget c Tr (β).x).V × (catTarget c Tr (β).x).V)
      (edgeEquiv' T hc M m hm e : M.target.V × M.target.V) := by
  obtain ⟨o, rfl⟩ := (occEquiv c (β).x).surjective e
  rcases o with ε | t
  · left
    have h1 := edgeEquiv'_oldE T hc M m hm ε
    have h2 := CatRegrow.oldE_ends c (β).x ε
    change ((edgeEquiv' T hc M m hm (oldE c (β).x ε) : M.target.edges) : M.target.V × M.target.V) =
      (vtxEquiv T hc M m hm ((oldE c (β).x ε : (catTarget c Tr (β).x).edges) :
          (catTarget c Tr (β).x).V × (catTarget c Tr (β).x).V).1,
        vtxEquiv T hc M m hm ((oldE c (β).x ε : (catTarget c Tr (β).x).edges) :
          (catTarget c Tr (β).x).V × (catTarget c Tr (β).x).V).2)
    rw [h1, h2]
    rfl
  · change UnorderedEnds (vtxEquiv T hc M m hm)
      ((tailE c (β).x t : (catTarget c Tr (β).x).edges) :
        (catTarget c Tr (β).x).V × (catTarget c Tr (β).x).V)
      (edgeEquiv' T hc M m hm (tailE c (β).x t) : M.target.V × M.target.V)
    rw [edgeEquiv'_tailE, CatRegrow.tailE_ends]
    have hne : vtxEquiv T hc M m hm (CatRegrow.tailEnd c (β).x t) ≠
        vtxEquiv T hc M m hm (CatRegrow.headEnd c (β).x t) := by
      intro h
      exact CatRegrow.occEnds_ne c (β).x (.inr t) ((vtxEquiv T hc M m hm).injective h)
    exact ends_of_mem (vtxEquiv_tailEnd_mem T hc M m hm t) (vtxEquiv_headEnd_mem T hc M m hm t) hne

/-! ## 3.  The datum -/

theorem ext_vp (u : (Tr).V) :
    M.data.vertexPartition (vIncl u) =
      CatRegrow.liftPart (β).e ((TailRestrict.dat T hc M m hm).vertexPartition u) := by
  have h := congrArg (fun D ↦ D.vertexPartition u) (Sheets.extendSheets_restrictSheets
    (TailRestrict.rData T hc M) (TailRestrict.split T hc M m hm)
    (TailRestrict.isLone_split T hc M m hm) (TailRestrict.m_pos T hc M m hm))
  exact h.symm

theorem ext_ep (ε : (Tr).edges) :
    M.data.edgePartition (edgeIncl ε) =
      CatRegrow.liftPart (β).e ((TailRestrict.dat T hc M m hm).edgePartition ε) := by
  have h := congrArg (fun D ↦ D.edgePartition ε) (Sheets.extendSheets_restrictSheets
    (TailRestrict.rData T hc M) (TailRestrict.split T hc M m hm)
    (TailRestrict.isLone_split T hc M m hm) (TailRestrict.m_pos T hc M m hm))
  exact h.symm

/-- **A frame is the regrowth of its own tail chains** over its restriction: the regrown datum of
`branching` is `M.data`, over the target dictionary, with identity sheet permutations. -/
def frameIso : GeometricDatumIso (β).regrowDatum M.data where
  targetVertex := vtxEquiv T hc M m hm
  targetEdge := edgeEquiv' T hc M m hm
  ends := ends_map T hc M m hm
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    rw [Transport.DatumIso.relabel_refl]
    rcases v with u | ⟨j, (i | i) | i⟩
    · exact ext_vp T hc M m hm u
    · exact vp_xSpine T hc M j i
    · exact vp_xBulb T hc M j i
    · exact vp_xLeaf T hc M j i
  edgePartition e := by
    rw [Transport.DatumIso.relabel_refl]
    obtain ⟨o, rfl⟩ := (occEquiv c (β).x).surjective e
    rcases o with ε | ⟨j, i | i | i⟩
    · change M.data.edgePartition (edgeEquiv' T hc M m hm (oldE c (β).x ε)) =
        (β).regrowDatum.edgePartition (oldE c (β).x ε)
      rw [edgeEquiv'_oldE, CatRegrow.CatBranching.ep_oldE]
      exact ext_ep T hc M m hm ε
    · change M.data.edgePartition (edgeEquiv' T hc M m hm (tailE c (β).x ⟨j, Sum.inl i⟩)) =
        (β).regrowDatum.edgePartition (tailE c (β).x ⟨j, Sum.inl i⟩)
      rw [edgeEquiv'_tailE, CatRegrow.CatBranching.ep_tailE]
      exact ep_path T hc M j i
    · change M.data.edgePartition (edgeEquiv' T hc M m hm (tailE c (β).x ⟨j, Sum.inr (Sum.inl i)⟩)) =
        (β).regrowDatum.edgePartition (tailE c (β).x ⟨j, Sum.inr (Sum.inl i)⟩)
      rw [edgeEquiv'_tailE, CatRegrow.CatBranching.ep_tailE]
      exact ep_bridge T hc M j i
    · change M.data.edgePartition (edgeEquiv' T hc M m hm (tailE c (β).x ⟨j, Sum.inr (Sum.inr i)⟩)) =
        (β).regrowDatum.edgePartition (tailE c (β).x ⟨j, Sum.inr (Sum.inr i)⟩)
      rw [edgeEquiv'_tailE, CatRegrow.CatBranching.ep_tailE]
      exact ep_loop T hc M j i
  compatible _ _ _ _ := by
    simp only [Equiv.refl_apply, Equiv.refl_symm]
    rfl

theorem frameIso_psiSV (Y : (TailRestrict.dat T hc M m hm).SourceVertex) :
    (frameIso T hc M m hm).sourceVertexEquiv ((β).psiSV Y) = TailRestrict.cSV T hc M m hm Y := rfl

theorem frameIso_psiSE (F : (TailRestrict.dat T hc M m hm).SourceEdge) :
    (frameIso T hc M m hm).sourceEdgeEquiv ((β).psiSE F) = TailRestrict.cSE T hc M m hm F := by
  apply Subtype.ext
  apply Prod.ext
  · exact edgeEquiv'_oldE T hc M m hm F.1.1
  · rfl

theorem frameIso_targetEdge_tailE (t : TE c) :
    (frameIso T hc M m hm).targetEdge (tailE c (β).x t) = TailRestrict.tEdge T hc M t.1 t.2 :=
  edgeEquiv'_tailE T hc M m hm t

theorem frameIso_targetVertex_tailV (j : Fin k) (w : CatVertex (c j)) :
    (frameIso T hc M m hm).targetVertex (tailV c (β).x ⟨j, Sum.inl w⟩) =
      (TailAt.vSource M (T.vertexEquiv (.inr ⟨j, w⟩))).1.1 := by
  rcases w with i | i
  · rfl
  · exact TailRestrict.xBulb_eq T M j i

end

end FrameChain

end DraismaVargas.Count.MarkedCountGeneral
