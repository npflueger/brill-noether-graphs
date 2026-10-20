module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailDatum

@[expose] public section

/-!
# Restriction over the tails: the marks, the marked rows and the marked vertices of `ψ`

For the restricted datum `ψ = dat` (module `RestrictTailDatum`):

* the marks `markSrc j` (the branch vertex `u_j` of the frame), of surviving valency two in `ψ`
  (`nonDanglingValency_markSrc`); every other vertex keeps its valency;
* the marked rows of `ψ` are the kept stable paths of the frame, i.e. its rows over core slots
  (`rowEquiv : MarkedStablePath ψ marks ≃ Fin p`, as the ramification-one
  `Lollipops.rowEquiv`);
* the marked vertices of `ψ` are the frame's branch vertices over core vertices
  (`vertexEquiv : MarkedBranchVertex ψ marks ≃ Fin n`), with the incidences
  (`markedIncidenceCount_eq`) and the path ends (`dat_pathEnds`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCountGeneral.Sheets (IsNew IsLone restrictSheets inclSV inclSE)
open GenusSixExistence.Tripod.Gluing (wCount nonDanglingValency_eq_wCount)
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree) (m : ℕ) (hm : m + nShed T hc M = degree)

/-! ## 1.  The marks -/

theorem exists_markSrc (j : Fin k) :
    ∃ X : (dat T hc M m hm).SourceVertex, cSV T hc M m hm X = uSource T M j :=
  exists_cSV T hc M m hm (xMark_mem_Keep T hc M j)
    (not_isLone_of_survivor T hc M (xMark_mem_Keep T hc M j)
      (by rw [nonDanglingValency_uSource]; omega))

/-- The mark `u_j` in `ψ`. -/
def markSrc (j : Fin k) : (dat T hc M m hm).SourceVertex := (exists_markSrc T hc M m hm j).choose

theorem cSV_markSrc (j : Fin k) : cSV T hc M m hm (markSrc T hc M m hm j) = uSource T M j :=
  (exists_markSrc T hc M m hm j).choose_spec

theorem markSrc_injective : Function.Injective (markSrc T hc M m hm) := by
  intro i j h
  have := congrArg (cSV T hc M m hm) h
  rw [cSV_markSrc, cSV_markSrc] at this
  exact uSource_injective T M hc this

/-- The marks of `ψ`. -/
abbrev marks : Finset (dat T hc M m hm).SourceVertex := markSet (markSrc T hc M m hm)

theorem mem_marks_iff (X : (dat T hc M m hm).SourceVertex) :
    X ∈ marks T hc M m hm ↔ ∃ j, cSV T hc M m hm X = uSource T M j := by
  simp only [marks, markSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, cSV_markSrc T hc M m hm j⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, cSV_injective T hc M m hm ((cSV_markSrc T hc M m hm j).trans hj.symm)⟩

include hc in
theorem wCount_lol_uSource (j : Fin k) : wCount M.data (Lol T M) (uSource T M j) = 1 := by
  classical
  rcases wCount_lol_kept T hc M (X := uSource T M j) (xMark_mem_Keep T hc M j) with h0 | ⟨h1, -⟩
  · exfalso
    have hE := uSource_incident_pathE T hc M j
    have hLol : Lol T M (TailAt.pathE (cat T j) M (T.cubic hc) 0).1 :=
      ⟨(TailAt.pathE (cat T j) M (T.cubic hc) 0).2, not_keptEdge_tEdge T hc M j (Sum.inl 0)⟩
    have hPos : 0 < wCount M.data (Lol T M) (uSource T M j) := by
      unfold wCount
      exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLol, hE⟩⟩
    omega
  · exact h1

include hc in
theorem wCount_lol_eq_zero {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M)
    (hne : ∀ j, X ≠ uSource T M j) : wCount M.data (Lol T M) X = 0 := by
  classical
  by_contra h
  obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  obtain ⟨j, -, rfl⟩ := eq_pathE_of_lol T hc M hX hE.1 hE.2
  exact hne j rfl

theorem nonDanglingValency_markSrc (j : Fin k) :
    nonDanglingValency (dat T hc M m hm) (markSrc T hc M m hm j) = 2 := by
  have h := nonDanglingValency_dat T hc M m hm (markSrc T hc M m hm j)
  rw [cSV_markSrc, wCount_lol_uSource T hc M j, nonDanglingValency_uSource] at h
  omega

theorem nonDanglingValency_dat_of_not_mark {X : (dat T hc M m hm).SourceVertex}
    (hX : X ∉ marks T hc M m hm) :
    nonDanglingValency (dat T hc M m hm) X = nonDanglingValency M.data (cSV T hc M m hm X) := by
  have h := nonDanglingValency_dat T hc M m hm X
  rw [wCount_lol_eq_zero T hc M (cSV_mem_Keep T hc M m hm X) fun j hj ↦
    hX ((mem_marks_iff T hc M m hm X).mpr ⟨j, hj⟩)] at h
  exact h

theorem nonDanglingValency_dat_le (X : (dat T hc M m hm).SourceVertex) :
    nonDanglingValency (dat T hc M m hm) X ≤ nonDanglingValency M.data (cSV T hc M m hm X) := by
  have h := nonDanglingValency_dat T hc M m hm X
  omega

theorem hMarks (X : (dat T hc M m hm).SourceVertex) :
    (nonDanglingValency (dat T hc M m hm) X = 2 ∧ X ∉ marks T hc M m hm) ↔
      nonDanglingValency M.data (cSV T hc M m hm X) = 2 := by
  by_cases hX : X ∈ marks T hc M m hm
  · obtain ⟨j, hj⟩ := (mem_marks_iff T hc M m hm X).mp hX
    rw [hj, nonDanglingValency_uSource]
    simp [hX]
  · rw [nonDanglingValency_dat_of_not_mark T hc M m hm hX]
    simp [hX]

theorem branch_iff (X : (dat T hc M m hm).SourceVertex) :
    (3 ≤ nonDanglingValency (dat T hc M m hm) X ∨ X ∈ marks T hc M m hm) ↔
      3 ≤ nonDanglingValency M.data (cSV T hc M m hm X) := by
  by_cases hX : X ∈ marks T hc M m hm
  · obtain ⟨j, hj⟩ := (mem_marks_iff T hc M m hm X).mp hX
    rw [hj, nonDanglingValency_uSource]
    simp [hX]
  · rw [nonDanglingValency_dat_of_not_mark T hc M m hm hX]
    simp [hX]

/-! ## 2.  The marked rows -/

/-- **Marked consecutiveness in `ψ` is consecutiveness in the frame.** -/
theorem markedConsecutive_iff (E F : NonDanglingEdge (dat T hc M m hm)) :
    MarkedConsecutive (dat T hc M m hm) (marks T hc M m hm) E F ↔
      Consecutive M.data (ndInc T hc M m hm E) (ndInc T hc M m hm F) := by
  constructor
  · rintro ⟨hne, X, hE, hF, h2, hX⟩
    exact ⟨fun h ↦ hne (ndInc_injective T hc M m hm h), cSV T hc M m hm X,
      (incident_cSE_iff T hc M m hm _ _).mpr hE, (incident_cSE_iff T hc M m hm _ _).mpr hF,
      (hMarks T hc M m hm X).mp ⟨h2, hX⟩⟩
  · rintro ⟨hne, X, hE, hF, h2⟩
    have hXK := target_mem_of_incident (cSE_kept T hc M m hm E.1) hE
    have hNL := not_isLone_of_survivor T hc M hXK (by omega)
    obtain ⟨X', rfl⟩ := exists_cSV T hc M m hm hXK hNL
    have h2' := (hMarks T hc M m hm X').mpr h2
    exact ⟨fun h ↦ hne (by rw [h]), X', (incident_cSE_iff T hc M m hm _ _).mp hE,
      (incident_cSE_iff T hc M m hm _ _).mp hF, h2'.1, h2'.2⟩

/-- **The marked rows of `ψ` are the kept stable paths of the frame.** -/
noncomputable def markedRowEquiv :
    MarkedStablePath (dat T hc M m hm) (marks T hc M m hm) ≃
      {r : StablePath M.data // KeptRow (deletionPattern T hc M) r} :=
  (Quot.congr (ndEquiv T hc M m hm) fun E F ↦ markedConsecutive_iff T hc M m hm E F).trans
    (quotSubtypeEquiv (Consecutive M.data) (fun F ↦ KeptEdge (Keep T M) F.1.1.1)
      (fun _ _ h ↦ keptEdge_iff_of_consecutive (deletionPattern T hc M) h))

theorem markedRowEquiv_markedRow (E : NonDanglingEdge (dat T hc M m hm)) :
    (markedRowEquiv T hc M m hm (markedRow (marks T hc M m hm) E)).1 =
      NonDanglingEdge.stablePath (ndInc T hc M m hm E) := rfl

/-- **The kept rows are the rows over core slots.** -/
theorem keptRow_iff (r : StablePath M.data) :
    KeptRow (deletionPattern T hc M) r ↔ M.ident.row r ∈ Set.range T.coreSlot := by
  constructor
  · intro hr
    rcases T.slot_cases (M.ident.row r) with ⟨i, hi⟩ | ⟨j, s, hjs⟩
    · exact ⟨i, hi⟩
    · exfalso
      obtain ⟨F, hF⟩ := Quot.exists_rep r
      have hF' : NonDanglingEdge.stablePath F = r := hF
      rw [← hF'] at hr hjs
      have hF : NonDanglingEdge.stablePath F = TailAt.row (cat T j) M s := by
        unfold TailAt.row
        rw [cat_slot, hjs, Equiv.symm_apply_apply]
      have hT := TailAt.over_tcol_of_onRow (cat T j) M (T.cubic hc) s hF
      exact not_keptEdge_tEdge T hc M j s (by rw [tEdge, ← hT]; exact hr)
  · rintro ⟨i, hi⟩
    obtain ⟨F, rfl⟩ := Quot.exists_rep r
    change KeptEdge (Keep T M) F.1.1.1
    by_contra hk
    obtain ⟨j, s, hjs⟩ := (not_keptEdge_iff T hc M _).mp hk
    have hR := tEdge_row T hc M j s F.2 hjs
    have : M.ident.row (NonDanglingEdge.stablePath F) = T.tailSlot j s := by
      change M.ident.row (NonDanglingEdge.stablePath ⟨F.1, F.2⟩) = _
      rw [hR, Equiv.apply_symm_apply]
    exact T.coreSlot_ne_tailSlot i j s (hi.trans this)

/-- Kept stable paths are core slots. -/
noncomputable def keptRowEquiv : {r : StablePath M.data // KeptRow (deletionPattern T hc M) r} ≃ Fin p :=
  (M.ident.row.subtypeEquiv fun r ↦ keptRow_iff T hc M r).trans
    (Equiv.ofInjective T.coreSlot T.coreSlot_injective).symm

theorem coreSlot_keptRowEquiv (r : {r : StablePath M.data // KeptRow (deletionPattern T hc M) r}) :
    T.coreSlot (keptRowEquiv T hc M r) = M.ident.row r.1 :=
  Equiv.apply_ofInjective_symm T.coreSlot_injective _

/-- **The marked rows of `ψ` are the core slots.** -/
noncomputable def rowEquiv : MarkedStablePath (dat T hc M m hm) (marks T hc M m hm) ≃ Fin p :=
  (markedRowEquiv T hc M m hm).trans (keptRowEquiv T hc M)

theorem coreSlot_rowEquiv (E : NonDanglingEdge (dat T hc M m hm)) :
    T.coreSlot (rowEquiv T hc M m hm (markedRow (marks T hc M m hm) E)) =
      M.ident.row (NonDanglingEdge.stablePath (ndInc T hc M m hm E)) :=
  coreSlot_keptRowEquiv T hc M _

theorem rowEquiv_markedRow_eq_iff (E : NonDanglingEdge (dat T hc M m hm)) (i : Fin p) :
    rowEquiv T hc M m hm (markedRow (marks T hc M m hm) E) = i ↔
      NonDanglingEdge.stablePath (ndInc T hc M m hm E) = M.ident.row.symm (T.coreSlot i) := by
  rw [Equiv.eq_symm_apply, ← coreSlot_rowEquiv]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ T.coreSlot_injective h⟩

/-! ## 3.  The marked vertices -/

include hc in
theorem keptVertex_iff (B : StableGraphIncidence.BranchVertex M.data) :
    B.1.1.1 ∈ Keep T M ↔ M.ident.vertex B ∈ Set.range T.oldVertex := by
  constructor
  · intro hB
    obtain ⟨w, hw⟩ := T.vertexEquiv.surjective (M.ident.vertex B)
    rcases w with v | ⟨j, x⟩
    · exact ⟨v, hw⟩
    · exfalso
      have hBx : B.1 = TailAt.vSource M ((cat T j).vertex x) :=
        TailAt.eq_vSource_of_ident M hw.symm
      rcases x with i | i
      · have : B.1.1.1 = xSpine T M j i := by rw [hBx]; rfl
        exact xSpine_notMem_Keep T M j i (this ▸ hB)
      · have : B.1.1.1 = xBulb T M j i := by rw [hBx, xBulb_eq]
        exact xBulb_notMem_Keep T M j i (this ▸ hB)
  · rintro ⟨v, hv⟩
    by_contra hB
    obtain ⟨⟨j, t⟩, ht⟩ := exists_tailVertex_of_notMem T M hB
    have hB3 := B.2
    rcases t with i | i | i
    · have hX := eq_spineV_of_over T hc M (X := B.1) ht.symm (by omega)
      have := congrArg M.ident.vertex (Subtype.ext hX :
        B = ⟨TailAt.spineV (cat T j) M i, TailAt.three_le_vSource M _⟩)
      rw [TailAt.ident_vSource, ← hv] at this
      exact vertexEquiv_inr_ne_old T j _ v this.symm
    · have hX := eq_bulbV_of_over T M (X := B.1) ht.symm (by omega)
      have := congrArg M.ident.vertex (Subtype.ext hX :
        B = ⟨TailAt.vSource M ((cat T j).vertex (Sum.inr i)), TailAt.three_le_vSource M _⟩)
      rw [TailAt.ident_vSource, ← hv] at this
      exact vertexEquiv_inr_ne_old T j _ v this.symm
    · have := LoopAt.nonDanglingValency_over_vC M ((cat T j).isLoop i) (X := B.1) ht.symm
      omega

theorem oldVertex_injective : Function.Injective T.oldVertex :=
  fun _ _ h ↦ Sum.inl_injective (T.vertexEquiv.injective h)

/-- The frame's branch vertex under a marked vertex of `ψ`. -/
def branchOf (X : MarkedBranchVertex (dat T hc M m hm) (marks T hc M m hm)) :
    StableGraphIncidence.BranchVertex M.data :=
  ⟨cSV T hc M m hm X.1, (branch_iff T hc M m hm X.1).mp X.2⟩

/-- **The marked vertices of `ψ` are the core vertices.** -/
noncomputable def vertexEquiv : MarkedBranchVertex (dat T hc M m hm) (marks T hc M m hm) ≃ Fin n :=
  (Equiv.ofBijective (fun X ↦ (⟨branchOf T hc M m hm X, cSV_mem_Keep T hc M m hm X.1⟩ :
      {B : StableGraphIncidence.BranchVertex M.data // B.1.1.1 ∈ Keep T M})) (by
    constructor
    · intro X Y h
      exact Subtype.ext (cSV_injective T hc M m hm (congrArg (fun B ↦ B.1.1) h))
    · intro B
      have hNL := not_isLone_of_survivor T hc M B.2 (by have := B.1.2; omega)
      obtain ⟨X', hX'⟩ := exists_cSV T hc M m hm B.2 hNL
      refine ⟨⟨X', (branch_iff T hc M m hm X').mpr (hX' ▸ B.1.2)⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hX'))).trans
    ((M.ident.vertex.subtypeEquiv fun B ↦ keptVertex_iff T hc M B).trans
      (Equiv.ofInjective T.oldVertex (oldVertex_injective T)).symm)

theorem oldVertex_vertexEquiv (X : MarkedBranchVertex (dat T hc M m hm) (marks T hc M m hm)) :
    T.oldVertex (vertexEquiv T hc M m hm X) = M.ident.vertex (branchOf T hc M m hm X) :=
  Equiv.apply_ofInjective_symm (oldVertex_injective T) _

theorem vertexEquiv_markSrc (j : Fin k)
    (h : 3 ≤ nonDanglingValency (dat T hc M m hm) (markSrc T hc M m hm j) ∨
      markSrc T hc M m hm j ∈ marks T hc M m hm) :
    vertexEquiv T hc M m hm ⟨markSrc T hc M m hm j, h⟩ = mark j := by
  apply oldVertex_injective T
  have hB : branchOf T hc M m hm ⟨markSrc T hc M m hm j, h⟩ =
      ⟨TailAt.vSource M (T.oldVertex (mark j)), TailAt.three_le_vSource M _⟩ :=
    Subtype.ext (cSV_markSrc T hc M m hm j)
  refine (oldVertex_vertexEquiv T hc M m hm ⟨markSrc T hc M m hm j, h⟩).trans ?_
  rw [hB, TailAt.ident_vSource]

/-! ## 4.  The incidences and the path ends -/

theorem coreIncidence_old_core (v : Fin n) (i : Fin p) :
    Count.coreIncidence T.H (T.oldVertex v) (T.coreSlot i) = Count.coreIncidence core v i := by
  unfold Count.coreIncidence
  rw [Tailed.coreSlot, T.tail_core, T.head_core]
  simp only [Tailed.oldVertex, Equiv.apply_eq_iff_eq, Sum.inl.injEq]

theorem markedIncidenceCount_eq (X : MarkedBranchVertex (dat T hc M m hm) (marks T hc M m hm))
    (i : Fin p) :
    markedIncidenceCount (dat T hc M m hm) (marks T hc M m hm) X.1 ((rowEquiv T hc M m hm).symm i) =
      Count.coreIncidence core (vertexEquiv T hc M m hm X) i := by
  classical
  rw [← coreIncidence_old_core T, oldVertex_vertexEquiv,
    ← M.ident.incidence (branchOf T hc M m hm X) (T.coreSlot i)]
  unfold markedIncidenceCount StablePathCount.incidenceCount
  refine Finset.card_bij (fun E _ ↦ ndInc T hc M m hm E) ?_ ?_ ?_
  · intro E hE
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hE ⊢
    refine ⟨(incident_cSE_iff T hc M m hm _ _).mpr hE.1, ?_⟩
    rw [← rowEquiv_markedRow_eq_iff, hE.2, Equiv.apply_symm_apply]
  · intro E _ F _ h
    exact ndInc_injective T hc M m hm h
  · intro F hF
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hF
    have hk : KeptEdge (Keep T M) F.1.1.1 := by
      have := (keptRow_iff T hc M (M.ident.row.symm (T.coreSlot i))).mpr
        ⟨i, by rw [Equiv.apply_symm_apply]⟩
      rw [← hF.2] at this
      exact this
    obtain ⟨E, hE⟩ := exists_cSE_of_survivor T hc M m hm F.2 hk
    have hES : ¬ IsDangling (dat T hc M m hm) E := not_isDangling_dat_of T hc M m hm (hE ▸ F.2)
    let E' : NonDanglingEdge (dat T hc M m hm) := ⟨E, hES⟩
    have hEF : ndInc T hc M m hm E' = F := Subtype.ext hE
    refine ⟨E', Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr
      ((incident_cSE_iff T hc M m hm _ _).mp (hE ▸ hF.1)), ?_⟩, hEF⟩
    rw [Equiv.eq_symm_apply, rowEquiv_markedRow_eq_iff, hEF]
    exact hF.2

include hc in
theorem keptEdge_of_stablePath_eq {F G : NonDanglingEdge M.data}
    (h : NonDanglingEdge.stablePath F = NonDanglingEdge.stablePath G)
    (hG : KeptEdge (Keep T M) G.1.1.1) : KeptEdge (Keep T M) F.1.1.1 := by
  have := (keptRow_mk (hP := deletionPattern T hc M) G).mpr hG
  rw [← h] at this
  exact (keptRow_mk (hP := deletionPattern T hc M) F).mp this

theorem dat_pathEnds : HasMarkedPathEnds (dat T hc M m hm) (marks T hc M m hm) := by
  intro E
  obtain ⟨F, X, hFE, hInc, hVal⟩ := M.fullDim.pathEnds (ndInc T hc M m hm E)
  have hk := keptEdge_of_stablePath_eq T hc M hFE (ndInc_kept T hc M m hm E)
  have hX := target_mem_of_incident hk hInc
  obtain ⟨F', hF'⟩ := exists_cSE_of_survivor T hc M m hm F.2 hk
  have hF'S : ¬ IsDangling (dat T hc M m hm) F' := not_isDangling_dat_of T hc M m hm (hF' ▸ F.2)
  have hNd : 0 < nonDanglingValency M.data X :=
    LollipopBridgeFibre.nonDanglingValency_pos_of_survivor F.2 hInc
  obtain ⟨X', rfl⟩ := exists_cSV T hc M m hm hX (not_isLone_of_survivor T hc M hX hNd)
  let F'' : NonDanglingEdge (dat T hc M m hm) := ⟨F', hF'S⟩
  refine ⟨F'', X', ?_, ?_⟩
  · apply (rowEquiv T hc M m hm).injective
    apply T.coreSlot_injective
    rw [coreSlot_rowEquiv, coreSlot_rowEquiv]
    have hFF : ndInc T hc M m hm F'' = F := Subtype.ext hF'
    rw [hFF]
    exact congrArg M.ident.row hFE
  · refine ⟨(incident_cSE_iff T hc M m hm _ _).mp (hF' ▸ hInc), ?_⟩
    by_cases hmk : X' ∈ marks T hc M m hm
    · exact Or.inr hmk
    · left
      rw [nonDanglingValency_dat_of_not_mark T hc M m hm hmk]
      exact hVal

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
