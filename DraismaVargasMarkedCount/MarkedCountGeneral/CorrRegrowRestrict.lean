module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrFrameTarget
public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrChainIso

@[expose] public section

/-!
# The inverse laws, part 9: regrowth after restriction

For the decomposition theorem (the fibre over the
tail is determined by the core map). For a frame `f` over the tailed core, with restriction
`(J, κ, s) = restrictTailed T hc f`, the regrowth `regrowTailed T hc hd J κ s` is isomorphic to `f`
over the identity of `T.H` (`regrowTailed_restrictTailed_iso`):

* `f` is the regrowth of its own tail chains over `κ` (`FrameChain.frameIso`, module
  `CorrFrameTarget`);
* the regrowth by window chains and the regrowth by `f`'s chains have the same marks and the same
  slopes, so they are isomorphic (`CatRegrow.chainIso`, module `CorrChainIso`);
* the composite is over the identity of the core: on the old part by the restriction's
  `oldVertex_vertexEquiv` and `coreSlot_rowEquiv`, on the tails by the uniqueness of the spine
  and bulb vertices (`TailRestrict.eq_spineV_of_over`, `eq_bulbV_of_over`) and of the rows over
  the tail columns (`TailRestrict.tEdge_row`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (f : Frame T.H degree)

local notation "M" => DraismaVargas.Count.SegmentWalls.Frame.member f 0
local notation "Jf" => (Sigma.fst (restrictTailed T hc f))
local notation "κf" => (Prod.fst (Sigma.snd (restrictTailed T hc f)))
local notation "sf" => (Prod.snd (Sigma.snd (restrictTailed T hc f)))
local notation "mf" => degree - shed (Sigma.fst (restrictTailed T hc f))
local notation "hmf" => TailRestrict.mDegAt_add T hc f (Sigma.fst (restrictTailed T hc f)) fun _ ↦ rfl
local notation "βw" => branching hd (Sigma.fst (restrictTailed T hc f)) (Prod.fst (Sigma.snd (restrictTailed T hc f)))
  (Prod.snd (Sigma.snd (restrictTailed T hc f)))
local notation "βf" => FrameChain.branching T hc (DraismaVargas.Count.SegmentWalls.Frame.member f 0)
  (degree - shed (Sigma.fst (restrictTailed T hc f)))
  (TailRestrict.mDegAt_add T hc f (Sigma.fst (restrictTailed T hc f)) fun _ ↦ rfl)
local notation "G" => regrowTailed T hc hd (Sigma.fst (restrictTailed T hc f))
  (Prod.fst (Sigma.snd (restrictTailed T hc f))) (Prod.snd (Sigma.snd (restrictTailed T hc f)))

/-- The window chains and the frame's chains have the same slopes. -/
theorem hcard_restrict (j : Fin k) (i : Fin (c j + 1)) :
    (((βw).chain j).P i).card = (((βf).chain j).P i).card :=
  (card_P hd Jf κf sf j i).trans (FrameChain.card_P T hc M j i).symm

/-- **The comparison of data**: the window regrowth of the restriction, the regrowth of `f`'s
own chains, and `f`. -/
def lawIso : GeometricDatumIso (βw).regrowDatum (M).data :=
  (chainIso βw βf rfl (hcard_restrict T hc hd f)).trans (FrameChain.frameIso T hc M mf hmf)

theorem lawIso_sve (X : (βw).regrowDatum.SourceVertex) :
    (lawIso T hc hd f).sourceVertexEquiv X = (FrameChain.frameIso T hc M mf hmf).sourceVertexEquiv
      ((chainIso βw βf rfl (hcard_restrict T hc hd f)).sourceVertexEquiv X) := rfl

theorem lawIso_see (E : (βw).regrowDatum.SourceEdge) :
    (lawIso T hc hd f).sourceEdgeEquiv E = (FrameChain.frameIso T hc M mf hmf).sourceEdgeEquiv
      ((chainIso βw βf rfl (hcard_restrict T hc hd f)).sourceEdgeEquiv E) := rfl

include hc in
/-- The only survivor-carrying vertex over a spine or bulb image is the named one. -/
theorem eq_vSource_of_over_tail {y : Fin T.P → ℚ} (M' : FibreMember T.H y degree) (j : Fin k)
    (w : CatVertex (c j)) {X : M'.data.SourceVertex}
    (hX : X.1.1 = (TailAt.vSource M' (T.vertexEquiv (.inr ⟨j, w⟩))).1.1)
    (hNd : nonDanglingValency M'.data X ≠ 0) :
    X = TailAt.vSource M' (T.vertexEquiv (.inr ⟨j, w⟩)) := by
  rcases w with i | i
  · exact TailRestrict.eq_spineV_of_over T hc M' hX hNd
  · exact TailRestrict.eq_bulbV_of_over T M' (hX.trans (TailRestrict.xBulb_eq T M' j i).symm) hNd

/-- **Regrowth after restriction is the identity**, up to isomorphism over the identity of the
core. -/
def regrowRestrictIso : FrameIso (G) f where
  datum := lawIso T hc hd f
  overCore_vertex branch := by
    obtain ⟨z, rfl⟩ := (bvEquiv hd Jf κf sf hc).surjective branch
    have hR : (G).ident.vertex (bvEquiv hd Jf κf sf hc z) = vertexSum T Jf κf z := by
      change vertexSum T Jf κf ((bvEquiv hd Jf κf sf hc).symm (bvEquiv hd Jf κf sf hc z)) = _
      rw [Equiv.symm_apply_apply]
    rw [hR]
    rcases z with Y | ⟨j, w⟩
    · have hB : (lawIso T hc hd f).branchVertexEquiv (G).fullDim.valid.1
          (bvEquiv hd Jf κf sf hc (.inl Y)) = TailRestrict.branchOf T hc M mf hmf Y := by
        apply Subtype.ext
        exact congrArg (FrameChain.frameIso T hc M mf hmf).sourceVertexEquiv
          (chainIso_psiSV βw βf rfl (hcard_restrict T hc hd f) Y.1)
      refine (congrArg f.ident.vertex hB).trans ?_
      exact (TailRestrict.oldVertex_vertexEquiv T hc M mf hmf Y).symm
    · have hX : ((lawIso T hc hd f).branchVertexEquiv (G).fullDim.valid.1
          (bvEquiv hd Jf κf sf hc (.inr ⟨j, w⟩))).1 = TailAt.vSource M (T.vertexEquiv (.inr ⟨j, w⟩)) := by
        apply eq_vSource_of_over_tail T hc M j w
        · exact FrameChain.frameIso_targetVertex_tailV T hc M mf hmf j w
        · have := ((lawIso T hc hd f).branchVertexEquiv (G).fullDim.valid.1
            (bvEquiv hd Jf κf sf hc (.inr ⟨j, w⟩))).2
          omega
      have hEq : (lawIso T hc hd f).branchVertexEquiv (G).fullDim.valid.1
          (bvEquiv hd Jf κf sf hc (.inr ⟨j, w⟩)) =
          ⟨TailAt.vSource M (T.vertexEquiv (.inr ⟨j, w⟩)), TailAt.three_le_vSource M _⟩ :=
        Subtype.ext hX
      refine (congrArg f.ident.vertex hEq).trans ?_
      exact TailAt.ident_vSource M _
  overCore_row path := by
    obtain ⟨E, rfl⟩ := Quot.exists_rep path
    change f.ident.row ((lawIso T hc hd f).stablePathEquiv (G).fullDim.valid.1 E.stablePath) =
      (G).ident.row E.stablePath
    refine Eq.trans (congrArg f.ident.row (GeometricDatumIso.stablePathEquiv_mk _ _ E)) ?_
    refine Eq.trans ?_ (ident_row_stablePath T hc hd Jf κf sf E).symm
    rcases (βw).nonDanglingEdge_cases (hψ Jf κf) (hT Jf κf) (hT0 Jf κf) (hMark hd Jf κf sf) E with
      ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
    · rw [CatBranching.rowTag_oldND]
      have hE : (lawIso T hc hd f).nonDanglingEdgeEquiv (G).fullDim.valid.1
          ((βw).oldND (hψ Jf κf) (hT Jf κf) (hT0 Jf κf) (hMark hd Jf κf sf) F) =
          TailRestrict.ndInc T hc M mf hmf F := by
        apply Subtype.ext
        exact (congrArg (FrameChain.frameIso T hc M mf hmf).sourceEdgeEquiv
          (chainIso_psiSE βw βf rfl (hcard_restrict T hc hd f) F.1)).trans
          (FrameChain.frameIso_psiSE T hc M mf hmf F.1)
      refine (congrArg (fun E ↦ f.ident.row (NonDanglingEdge.stablePath E)) hE).trans ?_
      exact (TailRestrict.coreSlot_rowEquiv T hc M mf hmf F).symm
    · rw [CatBranching.rowTag_tailND]
      set E' := (lawIso T hc hd f).nonDanglingEdgeEquiv (G).fullDim.valid.1
        ((βw).tailND (hψ Jf κf) (hT Jf κf) (hT0 Jf κf) (hMark hd Jf κf sf) t hq)
      have hT' : E'.1.1.1 = TailRestrict.tEdge T hc M t.1 t.2 := by
        exact (congrArg (FrameChain.frameIso T hc M mf hmf).targetEdge
          (chainTE_tailE βw βf t)).trans (FrameChain.frameIso_targetEdge_tailE T hc M mf hmf t)
      have hRow := TailRestrict.tEdge_row T hc M t.1 t.2 E'.2 hT'
      refine (congrArg f.ident.row hRow).trans ?_
      exact Equiv.apply_symm_apply _ _

/-- **Regrowth after restriction is the identity** (the decomposition theorem). -/
theorem regrowTailed_restrictTailed_iso : Nonempty (FrameIso (G) f) :=
  ⟨regrowRestrictIso T hc hd f⟩

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
