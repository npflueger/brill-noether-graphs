module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailTyped
public import DraismaVargasMarkedCount.MarkedCountGeneral.SheetLoneIso
public import DraismaVargasCount.GeometricSegmentWalls
public import DraismaVargasCount.GeometricStableTransport

@[expose] public section

/-!
# Restriction over the tails is functorial on isomorphisms of frames

An isomorphism `iso : FrameIso f f'` over the identity of the tailed core `T.H`

1. fixes the tails: it carries the branch vertices to the branch vertices of the same name
   (`sourceVertexEquiv_vSource`), the rows to the rows (`stablePath_map_row`), hence the tail
   columns to the tail columns (`targetEdge_tcol`), the lone path edges to the lone path edges
   (`sourceEdgeEquiv_pathE`), the slopes to the slopes (`sPath_map`), and the deleted target
   vertices to the deleted ones (`targetVertex_tailVertex`, `targetVertex_mem_Keep`);
2. so it restricts to the kept target (`Restrict.restrictIso`), carries lone sheets to lone sheets
   (`Sheets.isLone_vertexPerm_iff`) and restricts again to the deletion of the lone sheets
   (`Sheets.restrictSheetsIso`): `datIso`;
3. which is an isomorphism of typed frames over the identity of the marked core (`typedIso`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count (GeometricDatumIso)
open DraismaVargas.Count.MarkedCountGeneral.Sheets (IsNew IsLone restrictSheets inclSV inclSE)
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {f f' : Frame T.H degree}
  (iso : FrameIso f f')

/-! ## 1.  The isomorphism fixes the tails -/

variable {T} in
/-- The isomorphism of data, read between the members. -/
def isoD : GeometricDatumIso (f.member 0).data (f'.member 0).data := iso.datum

variable {T} in
/-- The branch vertex of a given name goes to the branch vertex of that name. -/
theorem sourceVertexEquiv_vSource (v : Fin T.N) :
    (isoD iso).sourceVertexEquiv (TailAt.vSource (f.member 0) v) = TailAt.vSource (f'.member 0) v :=
  TailAt.eq_vSource_of_ident (f'.member 0)
    ((iso.overCore_vertex ⟨TailAt.vSource (f.member 0) v, TailAt.three_le_vSource (f.member 0) v⟩).trans
      (TailAt.ident_vSource (f.member 0) v))

/-- A survivor on the row of a slot goes to a survivor on the row of that slot. -/
theorem stablePath_map_row {w : Fin T.N} {c₀ : ℕ} (C : CaterpillarAt T.H w c₀) (s : CatSlot c₀)
    {F : NonDanglingEdge (f.member 0).data} (h : F.stablePath = TailAt.row C (f.member 0) s) :
    ((isoD iso).nonDanglingEdgeEquiv (f.member 0).fullDim.valid.1 F).stablePath =
      TailAt.row C (f'.member 0) s := by
  have h2 : f'.ident.row ((isoD iso).nonDanglingEdgeEquiv (f.member 0).fullDim.valid.1 F).stablePath =
      f.ident.row F.stablePath := iso.overCore_row F.stablePath
  have h3 : f.ident.row F.stablePath = C.slot s := by
    rw [h]; exact TailAt.ident_row C (f.member 0) s
  unfold TailAt.row
  rw [Equiv.eq_symm_apply]
  exact h2.trans h3

/-- **The tail columns go to the tail columns.** -/
theorem targetEdge_tcol {w : Fin T.N} {c₀ : ℕ} (C : CaterpillarAt T.H w c₀) (hH : T.H.Cubic)
    (s : CatSlot c₀) :
    (isoD iso).targetEdge (TailAt.tcol C (f.member 0) hH s) = TailAt.tcol C (f'.member 0) hH s := by
  obtain ⟨e, he, hS⟩ := (f.member 0).fullDim.noDanglingTargetFibres (TailAt.tcol C (f.member 0) hH s)
  have hr := TailAt.onRow_of_over_tcol C (f.member 0) hH s hS he
  have hr' := stablePath_map_row T iso C s hr
  have := TailAt.over_tcol_of_onRow C (f'.member 0) hH s hr'
  rw [← he]
  exact this

/-- **The lone path edges go to the lone path edges.** -/
theorem sourceEdgeEquiv_pathE {w : Fin T.N} {c₀ : ℕ} (C : CaterpillarAt T.H w c₀) (hH : T.H.Cubic)
    (i : Fin (c₀ + 1)) :
    (isoD iso).sourceEdgeEquiv (TailAt.pathE C (f.member 0) hH i).1 =
      (TailAt.pathE C (f'.member 0) hH i).1 := by
  refine TailAt.eq_pathE_of_over C (f'.member 0) hH i ?_ ?_
  · exact ((isoD iso).isDangling_map_iff (f.member 0).fullDim.valid.1 _).not.mpr
      (TailAt.pathE C (f.member 0) hH i).2
  · exact targetEdge_tcol T iso C hH (Sum.inl i)

include iso in
/-- **The slopes are invariant.** -/
theorem sPath_map (j : Fin k) (i : Fin (c j + 1)) :
    sPath T hc (f'.member 0) j i = sPath T hc (f.member 0) j i := by
  unfold sPath
  rw [← sourceEdgeEquiv_pathE T iso (cat T j) (T.cubic hc) i]
  exact (isoD iso).sourceEdgeIndex_map _

include iso in
theorem lowerNat_map (j : Fin k) : lowerNat T hc f' j = lowerNat T hc f j := by
  unfold lowerNat
  rw [sPath_map T hc iso]

include iso in
theorem lowerIdx_map : lowerIdx T hc f' = lowerIdx T hc f :=
  funext fun j ↦ Fin.ext (lowerNat_map T hc iso j)

/-- The loop leaf is not the bulb. -/
theorem vC_ne_uP {N P degree : ℕ} {H : Core N P} {y : Fin P → ℚ} (M : FibreMember H y degree)
    {ℓ : Fin P} (hℓ : H.tail ℓ = H.head ℓ) : LoopAt.vC M hℓ ≠ LoopAt.uP M hℓ := by
  intro h
  have h1 : (GluingDatum.incidentEdges (LoopAt.vC M hℓ)).card = 1 := LoopAt.vC_isLeaf M hℓ
  have h2 := LoopAt.uP_divalent M hℓ
  rw [h] at h1
  omega

include hc in
/-- **The deleted target vertices go to the deleted target vertices.** -/
theorem targetVertex_tailVertex (q : Σ j, TailV (c j)) :
    (isoD iso).targetVertex (tailVertex T (f.member 0) q) = tailVertex T (f'.member 0) q := by
  rcases q with ⟨j, i | i | i⟩
  · exact congrArg (fun X : (f'.member 0).data.SourceVertex ↦ X.1.1)
      (sourceVertexEquiv_vSource iso _)
  · change (isoD iso).targetVertex (xBulb T (f.member 0) j i) = xBulb T (f'.member 0) j i
    rw [xBulb_eq, xBulb_eq]
    exact congrArg (fun X : (f'.member 0).data.SourceVertex ↦ X.1.1)
      (sourceVertexEquiv_vSource iso _)
  · change (isoD iso).targetVertex (LoopAt.vC (f.member 0) ((cat T j).isLoop i)) =
      LoopAt.vC (f'.member 0) ((cat T j).isLoop i)
    have hU : (isoD iso).targetVertex (LoopAt.uP (f.member 0) ((cat T j).isLoop i)) =
        LoopAt.uP (f'.member 0) ((cat T j).isLoop i) := by
      have : (isoD iso).targetVertex (xBulb T (f.member 0) j i) = xBulb T (f'.member 0) j i := by
        rw [xBulb_eq, xBulb_eq]
        exact congrArg (fun X : (f'.member 0).data.SourceVertex ↦ X.1.1)
          (sourceVertexEquiv_vSource iso ((cat T j).vertex (Sum.inr i)))
      exact this
    have hT := targetEdge_tcol T iso (cat T j) (T.cubic hc) (Sum.inr (Sum.inr i))
    change (isoD iso).targetEdge (LoopAt.tl (f.member 0) ((cat T j).isLoop i)) =
      LoopAt.tl (f'.member 0) ((cat T j).isLoop i) at hT
    have hne := vC_ne_uP (f.member 0) ((cat T j).isLoop i)
    have hE := (isoD iso).ends (LoopAt.tl (f.member 0) ((cat T j).isLoop i))
    unfold DraismaVargas.Count.UnorderedEnds at hE
    rw [hT] at hE
    rcases LoopAt.tl_ends (f.member 0) ((cat T j).isLoop i) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb] at hE <;>
      rcases LoopAt.tl_ends (f'.member 0) ((cat T j).isLoop i) with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;>
      rcases hE with hE | hE <;> rw [hE] at ha' hb' <;> simp only at ha' hb' <;>
      first
        | exact hb'
        | exact ha'
        | exact absurd ((isoD iso).targetVertex.injective (ha'.trans hU.symm)) hne
        | exact absurd ((isoD iso).targetVertex.injective (hb'.trans hU.symm)) hne

include hc in
theorem targetVertex_mem_Keep (v : (f.member 0).target.V) :
    (isoD iso).targetVertex v ∈ Keep T (f'.member 0) ↔ v ∈ Keep T (f.member 0) := by
  rw [mem_Keep, mem_Keep]
  constructor
  · intro h q hq
    exact h q (by rw [← targetVertex_tailVertex T hc iso, hq])
  · intro h q hq
    apply h q
    apply (isoD iso).targetVertex.injective
    rw [targetVertex_tailVertex T hc iso, hq]

/-! ## 2.  The restricted isomorphism -/

/-- The isomorphism restricted to the kept target. -/
def rIso : GeometricDatumIso (rData T hc (f.member 0)) (rData T hc (f'.member 0)) :=
  restrictIso (Φ := isoD iso) (targetVertex_mem_Keep T hc iso)

theorem isNew_vertexPerm {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) (v : (rTarget T hc (f.member 0)).V)
    (i : Fin degree) :
    IsNew (split T hc (f'.member 0) m hm') ((rIso T hc iso).vertexPerm v i) ↔
      IsNew (split T hc (f.member 0) m hm) i := by
  rw [isNew_split_iff, isNew_split_iff]
  exact Sheets.isLone_vertexPerm_iff (rIso T hc iso) (rTarget_connected T hc (f.member 0)) v i

theorem isNew_edgePerm {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) (e : (rTarget T hc (f.member 0)).edges)
    (i : Fin degree) :
    IsNew (split T hc (f'.member 0) m hm') ((rIso T hc iso).edgePerm e i) ↔
      IsNew (split T hc (f.member 0) m hm) i := by
  rw [isNew_split_iff, isNew_split_iff]
  exact Sheets.isLone_edgePerm_iff (rIso T hc iso) (rTarget_connected T hc (f.member 0)) e i

/-- **The isomorphism of the restricted data.** -/
def datIso {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) :
    GeometricDatumIso (dat T hc (f.member 0) m hm) (dat T hc (f'.member 0) m hm') :=
  Sheets.restrictSheetsIso (rIso T hc iso) (isNew_vertexPerm T hc iso hm hm')
    (isNew_edgePerm T hc iso hm hm')

theorem cSV_datIso {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) (X : (dat T hc (f.member 0) m hm).SourceVertex) :
    cSV T hc (f'.member 0) m hm' ((datIso T hc iso hm hm').sourceVertexEquiv X) =
      (isoD iso).sourceVertexEquiv (cSV T hc (f.member 0) m hm X) := by
  unfold cSV datIso
  rw [Sheets.inclSV_restrictSheetsIso]
  rfl

theorem cSE_datIso {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) (E : (dat T hc (f.member 0) m hm).SourceEdge) :
    cSE T hc (f'.member 0) m hm' ((datIso T hc iso hm hm').sourceEdgeEquiv E) =
      (isoD iso).sourceEdgeEquiv (cSE T hc (f.member 0) m hm E) := by
  unfold cSE datIso
  rw [Sheets.inclSE_restrictSheetsIso]
  rfl

theorem datIso_markSrc {m : ℕ} (hm : m + nShed T hc (f.member 0) = degree)
    (hm' : m + nShed T hc (f'.member 0) = degree) (j : Fin k) :
    (datIso T hc iso hm hm').sourceVertexEquiv (markSrc T hc (f.member 0) m hm j) =
      markSrc T hc (f'.member 0) m hm' j := by
  apply cSV_injective T hc (f'.member 0) m hm'
  rw [cSV_datIso, cSV_markSrc, cSV_markSrc]
  exact sourceVertexEquiv_vSource iso _

/-! ## 3.  The isomorphism of typed frames -/

/-- **Restriction is functorial**: an isomorphism of frames over the identity of the tailed core
induces an isomorphism of the restricted typed frames over the identity of the marked core. -/
def typedIso (J : ∀ j, Fin ((c j + 1) / 2 + 1)) (hJ : ∀ j, (J j : ℕ) = lowerNat T hc f j)
    (hJ' : ∀ j, (J j : ℕ) = lowerNat T hc f' j) :
    TypedFrameIso (typedFrameAt T hc f J hJ) (typedFrameAt T hc f' J hJ') where
  datum := datIso T hc iso (mDegAt_add T hc f J hJ) (mDegAt_add T hc f' J hJ')
  mark j := datIso_markSrc T hc iso _ _ j
  overCore_vertex X hImage := by
    apply oldVertex_injective T
    refine (oldVertex_vertexEquiv T hc (f'.member 0) _ _ ⟨_, hImage⟩).trans
      (Eq.trans ?_ (oldVertex_vertexEquiv T hc (f.member 0) _ _ X).symm)
    have hB : branchOf T hc (f'.member 0) _ (mDegAt_add T hc f' J hJ') ⟨_, hImage⟩ =
        (isoD iso).branchVertexEquiv (f.member 0).fullDim.valid.1
          (branchOf T hc (f.member 0) _ (mDegAt_add T hc f J hJ) X) :=
      Subtype.ext (cSV_datIso T hc iso _ _ X.1)
    rw [hB]
    exact iso.overCore_vertex _
  overCore_row E := by
    apply T.coreSlot_injective
    refine (coreSlot_rowEquiv T hc (f'.member 0) _ (mDegAt_add T hc f' J hJ') _).trans
      (Eq.trans ?_ (coreSlot_rowEquiv T hc (f.member 0) _ (mDegAt_add T hc f J hJ) E).symm)
    have hN : ndInc T hc (f'.member 0) _ (mDegAt_add T hc f' J hJ')
        ((datIso T hc iso (mDegAt_add T hc f J hJ) (mDegAt_add T hc f' J hJ')).nonDanglingEdgeEquiv
          (dat_valid T hc (f.member 0) _ _).1 E) =
        (isoD iso).nonDanglingEdgeEquiv (f.member 0).fullDim.valid.1
          (ndInc T hc (f.member 0) _ (mDegAt_add T hc f J hJ) E) :=
      Subtype.ext (cSE_datIso T hc iso _ _ E.1)
    exact (congrArg (fun F : NonDanglingEdge (f'.member 0).data ↦
      (f'.member 0).ident.row F.stablePath) hN).trans (iso.overCore_row
        (NonDanglingEdge.stablePath (ndInc T hc (f.member 0) _ (mDegAt_add T hc f J hJ) E)))

include iso in
/-- **The slopes are invariant.** -/
theorem slopeSeqAt_map (J : ∀ j, Fin ((c j + 1) / 2 + 1)) (hJ : ∀ j, (J j : ℕ) = lowerNat T hc f j)
    (hJ' : ∀ j, (J j : ℕ) = lowerNat T hc f' j) :
    slopeSeqAt T hc f' J hJ' = slopeSeqAt T hc f J hJ :=
  funext fun j ↦ Subtype.ext (funext fun i ↦ sPath_map T hc iso j i)

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
