module

public import DraismaVargasMarkedCount.MarkedCount.RestrictBranch

@[expose] public section

/-!
# The restricted datum of a member over the lollipop core

For a member `M` over `attachLollipops core mark`, `rData M` is the restriction of
`M.data` to the kept target vertices (module `RestrictDatum`), and this file proves every
ingredient of the marked frame it carries, except the structures
themselves, which `Restriction.lean` assembles:

* validity, the target hypotheses and the dimension count;
* the marks `markSource M j` (`u_j`, kept), of surviving valency two;
* the marked rows (`rowEquiv`) and marked vertices (`vertexEquiv`), with the incidences;
* the marked labelling (`labelling`) and the block decomposition of the matrix
  (`submatrix_eq_fromBlocks`), whence `|det|`, the coordinates and the denominators;
* the local ramification at the marks, `r' = r + 1`.
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction
open scoped Matrix

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  {y : Fin (p + (k + k)) → ℚ} (M : FibreMember (attachLollipops core mark) y degree)

/-! ## 1.  The restricted datum -/

/-- The restricted target `T'`. -/
abbrev rTarget : CFGraph.{0} := restrictTarget (Keep M) (Keep_nonempty M)

/-- **The restricted datum** `φ' = φ|_{φ⁻¹(T')}`. -/
abbrev rData : GluingDatum (rTarget M) degree :=
  restrictDatum M.data (Keep M) (Keep_nonempty M)

theorem rData_connected : (rData M).Connected :=
  connected_restrictDatum M.fullDim.connected (retract M) (fun _ h ↦ retract_of_mem M h)
    (retract_edge M) (retract_refines M)

theorem rData_valid : (rData M).Valid :=
  ⟨rData_connected M, riemannHurwitz_restrictDatum M.fullDim.valid.2⟩

theorem rTarget_connected : graph_connected (rTarget M) :=
  graph_connected_restrictTarget M.fullDim.targetConnected (retract M)
    (fun _ h ↦ retract_of_mem M h) (retract_edge M)

theorem card_edges_target : Multiset.card M.target.edges = p + (k + k) := by
  rw [← Multiset.card_coe M.target.edges, ← Fintype.card_congr M.fullDim.labelling.targetEdge,
    Fintype.card_fin]

theorem card_rTarget_edges : Multiset.card (rTarget M).edges = p := by
  rw [card_edges_restrictTarget]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset M.target.edges))
    (fun e ↦ KeptEdge (Keep M) e)
  rw [card_notKept, Finset.card_univ, Multiset.card_coe, card_edges_target] at h
  omega

theorem rTarget_genus : genus (rTarget M) = 0 := by
  classical
  have hT := M.fullDim.targetGenus
  unfold genus at hT ⊢
  rw [card_rTarget_edges, card_restrictTarget_V]
  rw [card_edges_target] at hT
  have hV := Finset.card_add_card_compl (Keep M)
  rw [card_Del] at hV
  push_cast at hT ⊢
  omega

/-! ## 2.  The marks and the surviving valencies -/

/-- `u_j` in the restriction. -/
def markSource (j : Fin k) : (rData M).SourceVertex := svRestrict (markV M j) (xV_mem_Keep M j)

@[simp] theorem svIncl_markSource (j : Fin k) : svIncl (markSource M j) = markV M j := rfl

/-- The marks, as a finset (`MarkedFrame.markSet`). -/
def marks : Finset (rData M).SourceVertex := Finset.univ.image (markSource M)

theorem mem_marks_iff (X : (rData M).SourceVertex) :
    X ∈ marks M ↔ ∃ j, markV M j = svIncl X := by
  simp only [marks, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, hj⟩; exact ⟨j, svIncl_injective hj⟩

theorem nonDanglingValency_rData (hc : IsMarkedCubic core mark) (X : (rData M).SourceVertex) :
    nonDanglingValency (rData M) X + GenusSixExistence.Tripod.Gluing.wCount M.data (Lol M) (svIncl X) =
      nonDanglingValency M.data (svIncl X) :=
  nonDanglingValency_restrict M.fullDim.connected (rData_connected M) (deletionPattern M hc) X

theorem nonDanglingValency_rData_of_not_mark (hc : IsMarkedCubic core mark)
    {X : (rData M).SourceVertex} (hX : X ∉ marks M) :
    nonDanglingValency (rData M) X = nonDanglingValency M.data (svIncl X) := by
  have h := nonDanglingValency_rData M hc X
  rw [wCount_lol_eq_zero M (svIncl_target_mem X) fun j hj ↦ hX ((mem_marks_iff M X).mpr ⟨j, hj⟩)]
    at h
  exact h

theorem nonDanglingValency_markSource (hc : IsMarkedCubic core mark) (j : Fin k) :
    nonDanglingValency (rData M) (markSource M j) = 2 := by
  have h := nonDanglingValency_rData M hc (markSource M j)
  rw [svIncl_markSource, wCount_lol_markV M hc, nonDanglingValency_markV] at h
  omega

theorem nonDanglingValency_rData_le (hc : IsMarkedCubic core mark) (X : (rData M).SourceVertex) :
    nonDanglingValency (rData M) X ≤ nonDanglingValency M.data (svIncl X) := by
  have h := nonDanglingValency_rData M hc X
  omega

theorem hMarks (hc : IsMarkedCubic core mark) (X : (rData M).SourceVertex) :
    (nonDanglingValency (rData M) X = 2 ∧ X ∉ marks M) ↔
      nonDanglingValency M.data (svIncl X) = 2 := by
  by_cases hX : X ∈ marks M
  · obtain ⟨j, hj⟩ := (mem_marks_iff M X).mp hX
    rw [← hj, nonDanglingValency_markV]
    simp [hX]
  · rw [nonDanglingValency_rData_of_not_mark M hc hX]
    simp [hX]

theorem branch_iff (hc : IsMarkedCubic core mark) (X : (rData M).SourceVertex) :
    (3 ≤ nonDanglingValency (rData M) X ∨ X ∈ marks M) ↔
      3 ≤ nonDanglingValency M.data (svIncl X) := by
  by_cases hX : X ∈ marks M
  · obtain ⟨j, hj⟩ := (mem_marks_iff M X).mp hX
    rw [← hj, nonDanglingValency_markV]
    simp [hX]
  · rw [nonDanglingValency_rData_of_not_mark M hc hX]
    simp [hX]

/-! ## 3.  The local ramification at the marks -/

theorem localRamification_markSource (hc : IsMarkedCubic core mark) (j : Fin k) :
    (rData M).localRamification (markSource M j).1.1
        ⟨(markSource M j).1.2, (markSource M j).2⟩ =
      M.data.localRamification (markV M j).1.1 ⟨(markV M j).1.2, (markV M j).2⟩ + 1 := by
  rw [localRamification_restrict_index]
  exact congrArg _ (sum_deleted_index_markV M hc j)

/-! ## 4.  The dimension count -/

theorem genus_rData :
    genus (rData M).sourceGraph = genus M.data.sourceGraph - k := by
  rw [genus_sourceGraph, genus_sourceGraph]
  have hV : Fintype.card (rData M).SourceVertex +
      ∑ v ∈ (Keep M)ᶜ, Fintype.card (M.data.vertexPartition v).Blocks =
      Fintype.card M.data.SourceVertex :=
    card_sourceVertex_restrict_add M.data (Keep M) (Keep_nonempty M)
  have hE : Fintype.card (rData M).SourceEdge +
      ∑ e ∈ Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep M) e),
        Fintype.card (M.data.edgePartition e).Blocks = Fintype.card M.data.SourceEdge :=
    card_sourceEdge_restrict_add M.data (Keep M) (Keep_nonempty M)
  have hV' := sum_blocks_Del M
  have hE' := sum_blocks_notKept M
  omega

theorem rData_saturated :
    ((rTarget M).edges.card : ℤ) = 2 * genus (rData M).sourceGraph + 2 * degree - 5 := by
  have h := M.fullDim.saturated
  rw [card_edges_target] at h
  rw [card_rTarget_edges, genus_rData]
  push_cast at h ⊢
  linarith

/-! ## 5.  The marked rows -/

theorem keptRow_iff (hc : IsMarkedCubic core mark) (r : StablePath M.data) :
    KeptRow (deletionPattern M hc) r ↔ M.ident.row r ∈ Set.range (coreSlot (p := p) k) := by
  constructor
  · intro hr
    rcases slot_cases (M.ident.row r) with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨i, hi.symm⟩
    · exfalso
      have hrb : r = bridgePath M j := by rw [bridgePath_eq, ← hj, Equiv.symm_apply_apply]
      subst hrb
      exact ((not_keptEdge_iff M (tb M j)).mpr (Or.inl ⟨j, rfl⟩)) hr
    · exfalso
      have hrl : r = loopRow M j := by
        unfold loopRow; rw [← hj, Equiv.symm_apply_apply]
      obtain ⟨E, hT, hS⟩ := M.fullDim.noDanglingTargetFibres (tl M j)
      have hE := onRow_of_over_tl M hS hT
      rw [hrl, ← hE] at hr
      exact ((not_keptEdge_iff M E.1.1).mpr (Or.inr ⟨j, hT⟩)) hr
  · rintro ⟨i, hi⟩
    obtain ⟨F, rfl⟩ := Quot.exists_rep r
    change KeptEdge (Keep M) F.1.1.1
    by_contra hk
    rcases (not_keptEdge_iff M F.1.1.1).mp hk with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hF : F.1 = bridgeE M j := eq_bridgeE M F.2 hj
      have hP : Quot.mk (Consecutive M.data) F = bridgePath M j := by
        unfold bridgePath; congr 1; exact Subtype.ext hF
      rw [hP, ident_row_bridgePath] at hi
      exact coreSlot_ne_bridgeSlot i j hi
    · have hP : Quot.mk (Consecutive M.data) F = loopRow M j := onRow_of_over_tl M F.2 hj
      rw [hP] at hi
      unfold loopRow at hi
      rw [Equiv.apply_symm_apply] at hi
      exact coreSlot_ne_loopSlot i j hi

/-- Kept stable paths are core slots. -/
def keptRowEquiv (hc : IsMarkedCubic core mark) :
    {r : StablePath M.data // KeptRow (deletionPattern M hc) r} ≃ Fin p :=
  (M.ident.row.subtypeEquiv fun r ↦ keptRow_iff M hc r).trans
    (Equiv.ofInjective (coreSlot (p := p) k) coreSlot_injective).symm

theorem coreSlot_keptRowEquiv (hc : IsMarkedCubic core mark)
    (r : {r : StablePath M.data // KeptRow (deletionPattern M hc) r}) :
    coreSlot k (keptRowEquiv M hc r) = M.ident.row r.1 :=
  Equiv.apply_ofInjective_symm coreSlot_injective _

/-- **The marked rows of the restriction are the core slots** (`ident.row`). -/
def rowEquiv (hc : IsMarkedCubic core mark) : MarkedStablePath (rData M) (marks M) ≃ Fin p :=
  (markedRowEquiv M.fullDim.connected (rData_connected M) (deletionPattern M hc) (marks M)
    (hMarks M hc)).trans (keptRowEquiv M hc)

/-- The survivor of `D` underlying a survivor of the restriction. -/
abbrev ndIncl' (hc : IsMarkedCubic core mark) (E : NonDanglingEdge (rData M)) :
    NonDanglingEdge M.data :=
  ndIncl M.fullDim.connected (rData_connected M) (deletionPattern M hc) E

theorem coreSlot_rowEquiv (hc : IsMarkedCubic core mark) (E : NonDanglingEdge (rData M)) :
    coreSlot k (rowEquiv M hc (markedRow (marks M) E)) =
      M.ident.row (NonDanglingEdge.stablePath (ndIncl' M hc E)) :=
  coreSlot_keptRowEquiv M hc _

theorem rowEquiv_markedRow_eq_iff (hc : IsMarkedCubic core mark) (E : NonDanglingEdge (rData M))
    (i : Fin p) :
    rowEquiv M hc (markedRow (marks M) E) = i ↔
      NonDanglingEdge.stablePath (ndIncl' M hc E) = M.ident.row.symm (coreSlot k i) := by
  rw [Equiv.eq_symm_apply, ← coreSlot_rowEquiv]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ coreSlot_injective h⟩

/-! ## 6.  The marked vertices -/

theorem keptVertex_iff (B : StableGraphIncidence.BranchVertex M.data) :
    B.1.1.1 ∈ Keep M ↔ M.ident.vertex B ∈ Set.range (oldVertex (n := n) k) := by
  constructor
  · intro hB
    rcases Fin.addCases (motive := fun c ↦ (∃ v, c = Fin.castAdd k v) ∨ ∃ j, c = Fin.natAdd n j)
      (fun v ↦ Or.inl ⟨v, rfl⟩) (fun j ↦ Or.inr ⟨j, rfl⟩) (M.ident.vertex B) with
      ⟨v, hv⟩ | ⟨j, hj⟩
    · exact ⟨v, hv.symm⟩
    · exfalso
      have : B = ⟨loopV M j, three_le_loopV M j⟩ := by
        apply M.ident.vertex.injective
        rw [hj, ident_loopV]; rfl
      rw [this] at hB
      exact uP_notMem_Keep M j hB
  · rintro ⟨v, hv⟩
    by_contra hB
    obtain ⟨j, hj | hj⟩ := exists_branch_of_notMem_Keep M hB
    · have hX : B.1 = loopV M j := by
        by_contra hne
        have := nonDanglingValency_over_uP M hj.symm hne
        have := B.2
        omega
      have : B = ⟨loopV M j, three_le_loopV M j⟩ := Subtype.ext hX
      rw [this, ident_loopV] at hv
      exact lollipopVertex_ne_oldVertex j v hv.symm
    · have := nonDanglingValency_over_vC M (X := B.1) hj.symm
      have := B.2
      omega

/-- **The marked vertices of the restriction are the old core vertices.** -/
def vertexEquiv (hc : IsMarkedCubic core mark) :
    MarkedBranchVertex (rData M) (marks M) ≃ Fin n :=
  ({ toFun := fun X ↦ ⟨⟨svIncl X.1, (branch_iff M hc X.1).mp X.2⟩, svIncl_target_mem X.1⟩
     invFun := fun B ↦ ⟨svRestrict B.1.1 B.2, (branch_iff M hc _).mpr B.1.2⟩
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
      MarkedBranchVertex (rData M) (marks M) ≃
        {B : StableGraphIncidence.BranchVertex M.data // B.1.1.1 ∈ Keep M}).trans
    ((M.ident.vertex.subtypeEquiv fun B ↦ keptVertex_iff M B).trans
      (Equiv.ofInjective (oldVertex (n := n) k) (Fin.castAdd_injective n k)).symm)

theorem oldVertex_vertexEquiv (hc : IsMarkedCubic core mark)
    (X : MarkedBranchVertex (rData M) (marks M)) :
    oldVertex k (vertexEquiv M hc X) =
      M.ident.vertex ⟨svIncl X.1, (branch_iff M hc X.1).mp X.2⟩ :=
  Equiv.apply_ofInjective_symm (Fin.castAdd_injective n k) _

theorem vertexEquiv_markSource (hc : IsMarkedCubic core mark) (j : Fin k)
    (h : 3 ≤ nonDanglingValency (rData M) (markSource M j) ∨ markSource M j ∈ marks M) :
    vertexEquiv M hc ⟨markSource M j, h⟩ = mark j := by
  apply Fin.castAdd_injective n k
  exact (oldVertex_vertexEquiv M hc ⟨markSource M j, h⟩).trans (ident_markV M j)

/-! ## 7.  The incidences -/

theorem coreIncidence_old_core (v : Fin n) (i : Fin p) :
    Count.coreIncidence (attachLollipops core mark) (oldVertex k v) (coreSlot k i) =
      Count.coreIncidence core v i := by
  simp [Count.coreIncidence]

theorem markedIncidenceCount_eq (hc : IsMarkedCubic core mark)
    (X : MarkedBranchVertex (rData M) (marks M)) (i : Fin p) :
    markedIncidenceCount (rData M) (marks M) X.1 ((rowEquiv M hc).symm i) =
      Count.coreIncidence core (vertexEquiv M hc X) i := by
  classical
  rw [← coreIncidence_old_core (mark := mark), oldVertex_vertexEquiv,
    ← M.ident.incidence ⟨svIncl X.1, (branch_iff M hc X.1).mp X.2⟩ (coreSlot k i)]
  unfold markedIncidenceCount StablePathCount.incidenceCount
  refine Finset.card_bij (fun E _ ↦ ndIncl' M hc E) ?_ ?_ ?_
  · intro E hE
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hE ⊢
    refine ⟨(incident_seIncl_iff _ _).mpr hE.1, ?_⟩
    rw [← rowEquiv_markedRow_eq_iff, hE.2, Equiv.apply_symm_apply]
  · intro E _ F _ h
    exact ndIncl_injective _ _ _ h
  · intro F hF
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hF
    have hk : KeptEdge (Keep M) F.1.1.1 := by
      have := (keptRow_iff M hc (M.ident.row.symm (coreSlot k i))).mpr
        ⟨i, by rw [Equiv.apply_symm_apply]⟩
      rw [← hF.2] at this
      exact this
    refine ⟨ndRestrict M.fullDim.connected (deletionPattern M hc) F hk, ?_, rfl⟩
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges]
    refine ⟨(incident_iff_seRestrict hk X.1).mp hF.1, ?_⟩
    rw [Equiv.eq_symm_apply, rowEquiv_markedRow_eq_iff]
    exact hF.2

/-! ## 8.  Path ends -/

theorem keptEdge_of_stablePath_eq (hc : IsMarkedCubic core mark) {F G : NonDanglingEdge M.data}
    (h : NonDanglingEdge.stablePath F = NonDanglingEdge.stablePath G)
    (hG : KeptEdge (Keep M) G.1.1.1) : KeptEdge (Keep M) F.1.1.1 := by
  have := (keptRow_mk (hP := deletionPattern M hc) G).mpr hG
  rw [← h] at this
  exact (keptRow_mk (hP := deletionPattern M hc) F).mp this

theorem rData_pathEnds (hc : IsMarkedCubic core mark) : HasMarkedPathEnds (rData M) (marks M) := by
  intro E
  obtain ⟨F, X, hFE, hInc, hVal⟩ := M.fullDim.pathEnds (ndIncl' M hc E)
  have hk := keptEdge_of_stablePath_eq M hc hFE (seIncl_kept E.1)
  have hX := target_mem_of_incident hk hInc
  refine ⟨ndRestrict M.fullDim.connected (deletionPattern M hc) F hk, svRestrict X hX, ?_, ?_⟩
  · apply (rowEquiv M hc).injective
    apply coreSlot_injective
    rw [coreSlot_rowEquiv, coreSlot_rowEquiv]
    exact congrArg M.ident.row hFE
  · refine ⟨(incident_iff_seRestrict hk _).mp hInc, ?_⟩
    by_cases hm : svRestrict X hX ∈ marks M
    · exact Or.inr hm
    · left
      rw [nonDanglingValency_rData_of_not_mark M hc hm]
      exact hVal

/-! ## 9.  The marked labelling -/

theorem card_rTarget_edges' : Fintype.card (rTarget M).edges = p := by
  rw [Multiset.card_coe, card_rTarget_edges]

/-- The target edges of the restriction, numbered. -/
def targetEdge' : Fin p ≃ (rTarget M).edges :=
  (Fintype.equivFinOfCardEq (card_rTarget_edges' M)).symm

theorem keptEdge_incl_targetEdge (c : Fin p) : KeptEdge (Keep M) (edgeIncl (targetEdge' M c)) :=
  keptEdge_edgeIncl _

/-- **The marked labelling of the restriction**: rows by core slots (as `ident.row`). -/
def labelling (hc : IsMarkedCubic core mark) : MarkedLabelling (rData M) (marks M) (Fin p) :=
  ⟨targetEdge' M, rowEquiv M hc⟩

/-- The column of `A_φ` of a kept target edge. -/
def colIncl (c : Fin p) : Fin (p + (k + k)) :=
  M.fullDim.labelling.targetEdge.symm (edgeIncl (targetEdge' M c))

/-- The row of `A_φ` of a core slot. -/
def rowIncl (i : Fin p) : Fin (p + (k + k)) :=
  M.fullDim.labelling.row (M.ident.row.symm (coreSlot k i))

/-- **The marked matrix of the restriction is a submatrix of `A_φ`.** -/
theorem matrix_labelling (hc : IsMarkedCubic core mark) (i c : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation i c =
      GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
        (rowIncl M i) (colIncl M c) := by
  classical
  have hc' : c = (labelling M hc).targetEdge.symm ((labelling M hc).targetEdge c) :=
    (Equiv.symm_apply_apply _ _).symm
  conv_lhs => rw [hc']
  rw [markedMatrix_eq_sum, colIncl, LeafFibre.matrix_eq_sum_fibre]
  refine Finset.sum_bij' (fun E _ ↦ seIncl E) (fun E hE ↦ seRestrict E (by
      have hT := ((LeafFibre.mem_rowFibre _ _ _ _).mp hE).2
      rw [hT]; exact keptEdge_incl_targetEdge M c)) ?_ ?_ ?_ ?_ ?_
  · intro E hE
    obtain ⟨⟨hS, hR⟩, hT⟩ := (mem_markedRowFibre _ _ _ _).mp hE
    refine (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨(ndIncl' M hc ⟨E, hS⟩).2, ?_⟩, ?_⟩
    · have := (rowEquiv_markedRow_eq_iff M hc ⟨E, hS⟩ i).mp hR
      exact congrArg M.fullDim.labelling.row this
    · change edgeIncl E.1.1 = _
      rw [hT]; rfl
  · intro E hE
    obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hE
    have hk : KeptEdge (Keep M) E.1.1 := by rw [hT]; exact keptEdge_incl_targetEdge M c
    have hS' := not_isDangling_restrict_of (hKeep := Keep_nonempty M) M.fullDim.connected
      (deletionPattern M hc) (E := seRestrict E hk) hS
    refine (mem_markedRowFibre _ _ _ _).mpr ⟨⟨hS', ?_⟩, ?_⟩
    · exact (rowEquiv_markedRow_eq_iff M hc ⟨seRestrict E hk, hS'⟩ i).mpr
        (M.fullDim.labelling.row.injective hR)
    · apply edgeIncl_injective
      change E.1.1 = _
      rw [hT]; rfl
  · intro E _; rfl
  · intro E _; rfl
  · intro E _; rfl

/-! ## 10.  The block decomposition of `A_φ` -/

/-- The slots of the lollipop core, in three blocks. -/
def slotEquiv : Fin p ⊕ (Fin k ⊕ Fin k) ≃ Fin (p + (k + k)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

@[simp] theorem slotEquiv_inl (i : Fin p) : slotEquiv (k := k) (Sum.inl i) = coreSlot k i := by
  simp [slotEquiv, coreSlot]

@[simp] theorem slotEquiv_inr_inl (j : Fin k) :
    slotEquiv (p := p) (Sum.inr (Sum.inl j)) = bridgeSlot p j := by
  simp [slotEquiv, bridgeSlot]

@[simp] theorem slotEquiv_inr_inr (j : Fin k) :
    slotEquiv (p := p) (Sum.inr (Sum.inr j)) = loopSlot p j := by
  simp [slotEquiv, loopSlot]

/-- The rows of `A_φ`: core slots, bridge rows, loop rows. -/
def rowBlocks : Fin p ⊕ (Fin k ⊕ Fin k) ≃ Fin (p + (k + k)) :=
  slotEquiv.trans (M.ident.row.symm.trans M.fullDim.labelling.row)

theorem rowBlocks_inl (i : Fin p) : rowBlocks M (Sum.inl i) = rowIncl M i := by
  simp [rowBlocks, rowIncl]

theorem rowBlocks_inr_inl (j : Fin k) :
    rowBlocks M (Sum.inr (Sum.inl j)) = M.fullDim.labelling.row (bridgePath M j) := by
  simp [rowBlocks, bridgePath_eq]

theorem rowBlocks_inr_inr (j : Fin k) :
    rowBlocks M (Sum.inr (Sum.inr j)) = M.fullDim.labelling.row (loopRow M j) := by
  simp [rowBlocks, loopRow]

/-- The column function: kept target edges, bridge images, leaf edges. -/
def colFun : Fin p ⊕ (Fin k ⊕ Fin k) → Fin (p + (k + k)) :=
  Sum.elim (colIncl M) (Sum.elim (fun j ↦ M.fullDim.labelling.targetEdge.symm (tb M j))
    (fun j ↦ M.fullDim.labelling.targetEdge.symm (tl M j)))

theorem colFun_injective : Function.Injective (colFun M) := by
  have hK : ∀ c j, edgeIncl (targetEdge' M c) ≠ tb M j := fun c j h ↦
    (not_keptEdge_iff M (tb M j)).mpr (Or.inl ⟨j, rfl⟩) (h ▸ keptEdge_incl_targetEdge M c)
  have hL : ∀ c j, edgeIncl (targetEdge' M c) ≠ tl M j := fun c j h ↦
    (not_keptEdge_iff M (tl M j)).mpr (Or.inr ⟨j, rfl⟩) (h ▸ keptEdge_incl_targetEdge M c)
  have hinj : Function.Injective (fun s ↦ M.fullDim.labelling.targetEdge (colFun M s)) := by
    rintro (a | (a | a)) (b | (b | b)) h <;>
      simp only [colFun, colIncl, Sum.elim_inl, Sum.elim_inr, Equiv.apply_symm_apply] at h
    · exact congrArg Sum.inl ((targetEdge' M).injective (edgeIncl_injective h))
    · exact absurd h (hK a b)
    · exact absurd h (hL a b)
    · exact absurd h.symm (hK b a)
    · exact congrArg (Sum.inr ∘ Sum.inl) (tb_injective M h)
    · exact absurd h (tb_ne_tl' M a b)
    · exact absurd h.symm (hL b a)
    · exact absurd h.symm (tb_ne_tl' M b a)
    · exact congrArg (Sum.inr ∘ Sum.inr) (tl_injective M h)
  exact fun a b h ↦ hinj (congrArg _ h)

/-- The columns of `A_φ`, in three blocks. -/
def colBlocks : Fin p ⊕ (Fin k ⊕ Fin k) ≃ Fin (p + (k + k)) :=
  Equiv.ofBijective (colFun M) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨colFun_injective M, by simp [Fintype.card_sum]⟩)

theorem matrix_eq_zero_of_keptRow (hc : IsMarkedCubic core mark) (r : StablePath M.data)
    (e : M.target.edges) (h : KeptRow (deletionPattern M hc) r ↔ ¬ KeptEdge (Keep M) e) :
    GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
      (M.fullDim.labelling.row r) (M.fullDim.labelling.targetEdge.symm e) = 0 := by
  rw [LeafFibre.matrix_eq_sum_fibre]
  refine Finset.sum_eq_zero fun E hE ↦ ?_
  obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hE
  have hr := M.fullDim.labelling.row.injective hR
  have := (keptRow_mk (hP := deletionPattern M hc) ⟨E, hS⟩)
  rw [hr, h, hT] at this
  exact (iff_not_self this.symm).elim

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem keptRow_coreSlot (hc : IsMarkedCubic core mark) (i : Fin p) :
    KeptRow (deletionPattern M hc) (M.ident.row.symm (coreSlot k i)) :=
  (keptRow_iff M hc _).mpr ⟨i, by rw [Equiv.apply_symm_apply]⟩

theorem not_keptRow_bridgePath (hc : IsMarkedCubic core mark) (j : Fin k) :
    ¬ KeptRow (deletionPattern M hc) (bridgePath M j) := by
  rw [keptRow_iff M hc, ident_row_bridgePath]
  rintro ⟨i, hi⟩
  exact coreSlot_ne_bridgeSlot i j hi

theorem not_keptRow_loopRow (hc : IsMarkedCubic core mark) (j : Fin k) :
    ¬ KeptRow (deletionPattern M hc) (loopRow M j) := by
  rw [keptRow_iff M hc, loopRow, Equiv.apply_symm_apply]
  rintro ⟨i, hi⟩
  exact coreSlot_ne_loopSlot i j hi

theorem bridgePath_inj {i j : Fin k} (h : bridgePath M i = bridgePath M j) : i = j := by
  have := congrArg M.ident.row h
  rw [ident_row_bridgePath, ident_row_bridgePath] at this
  exact bridgeSlot_injective this

theorem loopRow_inj {i j : Fin k} (h : loopRow M i = loopRow M j) : i = j :=
  loopSlot_injective (M.ident.row.symm.injective h)

theorem bridgePath_ne_loopRow (i j : Fin k) : bridgePath M i ≠ loopRow M j := by
  intro h
  have := congrArg M.ident.row h
  rw [ident_row_bridgePath, loopRow, Equiv.apply_symm_apply] at this
  exact bridgeSlot_ne_loopSlot i j this

theorem leafRow_vC (j : Fin k) :
    LeafFibre.leafRow M.fullDim (vC_isLeaf M j) = M.fullDim.labelling.row (loopRow M j) :=
  LollipopLeafRow.leafRow_loopLeaf M (hLoop j)

/-- The block of the lollipops: `diag(½, 2)` per lollipop. -/
def lollipopBlock : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℚ :=
  Matrix.diagonal (Sum.elim (fun _ ↦ (1 / 2 : ℚ)) (fun _ ↦ 2))

theorem det_lollipopBlock : (lollipopBlock (k := k)).det = 1 := by
  rw [lollipopBlock, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow]
  norm_num

/-- **The block decomposition** `A_φ ≅ A_{φ'} ⊕ diag(½, 2)^k`, after reordering rows and
columns. -/
theorem submatrix_eq_fromBlocks (hc : IsMarkedCubic core mark) :
    (GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation).submatrix
        (rowBlocks M) (colBlocks M) =
      Matrix.fromBlocks
        (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation) 0 0
        lollipopBlock := by
  have hU : ∀ j F, ¬ IsDangling M.data F → F.1.1 = (bridgeE M j).1.1 → F = bridgeE M j :=
    fun j F hF hT ↦ eq_bridgeE M hF hT
  ext (i | (j | j)) (c | (j' | j'))
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, rowBlocks_inl]
    exact (matrix_labelling M hc i c).symm
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, rowBlocks_inl]
    exact matrix_eq_zero_of_keptRow M hc _ (tb M j')
      (iff_of_true (keptRow_coreSlot M hc i) ((not_keptEdge_iff M _).mpr (Or.inl ⟨j', rfl⟩)))
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, rowBlocks_inl]
    exact matrix_eq_zero_of_keptRow M hc _ (tl M j')
      (iff_of_true (keptRow_coreSlot M hc i) ((not_keptEdge_iff M _).mpr (Or.inr ⟨j', rfl⟩)))
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, rowBlocks_inr_inl]
    exact matrix_eq_zero_of_keptRow M hc _ _
      (iff_of_false (not_keptRow_bridgePath M hc j) (not_not.mpr (keptEdge_incl_targetEdge M c)))
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, rowBlocks_inr_inl]
    change GluingDatum.LengthMatrixPresentation.matrix _ _
      (M.fullDim.labelling.targetEdge.symm (bridgeE M j').1.1) = _
    rw [matrix_column_of_unique M.fullDim (bridgeE_survives M j') (hU j'), lollipopBlock,
      Matrix.diagonal_apply]
    change (if M.fullDim.labelling.row (bridgePath M j) = M.fullDim.labelling.row (bridgePath M j')
      then _ else _) = _
    by_cases h : j = j'
    · subst h; simp [bridgeE_index]
    · rw [ite_neg' (fun h' ↦ h (bridgePath_inj M (M.fullDim.labelling.row.injective h'))),
        ite_neg' (fun h' ↦ h (Sum.inl_injective h'))]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, rowBlocks_inr_inl]
    change GluingDatum.LengthMatrixPresentation.matrix _ _
      (M.fullDim.labelling.targetEdge.symm (Count.leafEdge (vC_isLeaf M j'))) = _
    rw [LeafFibre.matrix_leafEdge_column M.fullDim (vC_isLeaf M j'), leafRow_vC, lollipopBlock,
      Matrix.diagonal_apply, ite_neg' Sum.inl_ne_inr,
      ite_neg' (fun h' ↦ bridgePath_ne_loopRow M j j' (M.fullDim.labelling.row.injective h'))]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, rowBlocks_inr_inr]
    exact matrix_eq_zero_of_keptRow M hc _ _
      (iff_of_false (not_keptRow_loopRow M hc j) (not_not.mpr (keptEdge_incl_targetEdge M c)))
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, rowBlocks_inr_inr]
    change GluingDatum.LengthMatrixPresentation.matrix _ _
      (M.fullDim.labelling.targetEdge.symm (bridgeE M j').1.1) = _
    rw [matrix_column_of_unique M.fullDim (bridgeE_survives M j') (hU j'), lollipopBlock,
      Matrix.diagonal_apply, ite_neg' Sum.inr_ne_inl]
    change (if M.fullDim.labelling.row (loopRow M j) = M.fullDim.labelling.row (bridgePath M j')
      then _ else _) = _
    rw [ite_neg' (fun h' ↦ bridgePath_ne_loopRow M j' j (M.fullDim.labelling.row.injective h').symm)]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, rowBlocks_inr_inr]
    change GluingDatum.LengthMatrixPresentation.matrix _ _
      (M.fullDim.labelling.targetEdge.symm (Count.leafEdge (vC_isLeaf M j'))) = _
    rw [LeafFibre.matrix_leafEdge_column M.fullDim (vC_isLeaf M j'), leafRow_vC, lollipopBlock,
      Matrix.diagonal_apply]
    by_cases h : j = j'
    · subst h; simp
    · rw [ite_neg' (fun h' ↦ h (loopRow_inj M (M.fullDim.labelling.row.injective h'))),
        ite_neg' (fun h' ↦ h (Sum.inr_injective h'))]

/-- **`|det A_{φ'}| = |det A_φ|`.** -/
theorem abs_det_labelling (hc : IsMarkedCubic core mark) :
    |(GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation).det| =
      |(GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation).det| := by
  set A := GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
  have h := congrArg Matrix.det (submatrix_eq_fromBlocks M hc)
  rw [Matrix.det_fromBlocks_zero₂₁, det_lollipopBlock, mul_one] at h
  have hσ : A.submatrix (rowBlocks M) (colBlocks M) =
      (A.submatrix id ((rowBlocks M).symm.trans (colBlocks M))).submatrix (rowBlocks M)
        (rowBlocks M) := by
    ext a b
    simp
  rw [hσ, Matrix.det_submatrix_equiv_self, Matrix.det_permute'] at h
  rw [← h, abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ((rowBlocks M).symm.trans (colBlocks M))) with
    hs | hs <;> simp [hs]

theorem det_labelling_ne_zero (hc : IsMarkedCubic core mark) :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation).det ≠ 0 := by
  intro h
  have := abs_det_labelling M hc
  rw [h, abs_zero] at this
  exact M.fullDim.det_ne_zero (abs_eq_zero.mp this.symm)


/-! ## 11.  Coordinates -/

theorem slot_rowBlocks (s : Fin p ⊕ (Fin k ⊕ Fin k)) :
    M.ident.row (M.fullDim.labelling.row.symm (rowBlocks M s)) = slotEquiv s := by
  simp [rowBlocks]

/-- **The coordinates split** as `z = (A_{φ'}⁻¹ y, 2β, λ/2)`, stated for any solution of the
realization equation. -/
theorem coords_blocks (hc : IsMarkedCubic core mark) (Y : Fin (p + (k + k)) → ℚ)
    (z : Fin (p + (k + k)) → ℚ)
    (hz : GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation *ᵥ z =
      fun row ↦ Y (M.ident.row (M.fullDim.labelling.row.symm row))) :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation *ᵥ
        (fun i ↦ z (colIncl M i)) = fun i ↦ Y (coreSlot k i)) ∧
      (∀ j, z (M.fullDim.labelling.targetEdge.symm (tb M j)) = 2 * Y (bridgeSlot p j)) ∧
      (∀ j, z (M.fullDim.labelling.targetEdge.symm (tl M j)) = Y (loopSlot p j) / 2) := by
  set A := GluingDatum.LengthMatrixPresentation.matrix M.fullDim.labelling.presentation
  have hBlocks := submatrix_eq_fromBlocks M hc
  have hEq : A.submatrix (rowBlocks M) (colBlocks M) *ᵥ (z ∘ colBlocks M) =
      fun s ↦ Y (slotEquiv s) := by
    rw [Matrix.submatrix_mulVec_equiv]
    funext s
    simp only [Function.comp_apply]
    have : (z ∘ ⇑(colBlocks M)) ∘ ⇑(colBlocks M).symm = z := by
      funext c; simp
    rw [this, hz]
    exact congrArg Y (slot_rowBlocks M s)
  rw [hBlocks, Matrix.fromBlocks_mulVec] at hEq
  simp only [Matrix.zero_mulVec, add_zero, zero_add] at hEq
  refine ⟨?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · funext i
    have := congrFun hEq (Sum.inl i)
    simp only [Sum.elim_inl, slotEquiv_inl] at this
    exact this
  · have := congrFun hEq (Sum.inr (Sum.inl j))
    simp only [Sum.elim_inr, lollipopBlock, Matrix.mulVec_diagonal, Sum.elim_inl,
      Function.comp_apply, slotEquiv_inr_inl] at this
    change (1 / 2 : ℚ) * z (colFun M (Sum.inr (Sum.inl j))) = _ at this
    simp only [colFun, Sum.elim_inr, Sum.elim_inl] at this
    linarith
  · have := congrFun hEq (Sum.inr (Sum.inr j))
    simp only [Sum.elim_inr, lollipopBlock, Matrix.mulVec_diagonal,
      Function.comp_apply, slotEquiv_inr_inr] at this
    change (2 : ℚ) * z (colFun M (Sum.inr (Sum.inr j))) = _ at this
    simp only [colFun, Sum.elim_inr] at this
    linarith

theorem colBlocks_apply (s : Fin p ⊕ (Fin k ⊕ Fin k)) : colBlocks M s = colFun M s := rfl


/-! ## 12.  Row denominators -/

section Denominators

open DraismaVargas.Count.TrivalentWeight (commonDenominator_equiv)

theorem commonDenominator_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ] (g : ι → ℚ)
    (h : κ → ℚ) :
    commonDenominator Finset.univ (Sum.elim g h) =
      Nat.lcm (commonDenominator Finset.univ g) (commonDenominator Finset.univ h) := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun s _ ↦ ?_
    rcases s with a | b
    · exact dvd_trans (den_dvd_commonDenominator _ g (Finset.mem_univ a)) (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (den_dvd_commonDenominator _ h (Finset.mem_univ b)) (Nat.dvd_lcm_right _ _)
  · refine Nat.lcm_dvd ((commonDenominator_dvd_iff _ _ _).mpr fun a _ ↦ ?_)
      ((commonDenominator_dvd_iff _ _ _).mpr fun b _ ↦ ?_)
    · exact den_dvd_commonDenominator _ (Sum.elim g h) (Finset.mem_univ (Sum.inl a))
    · exact den_dvd_commonDenominator _ (Sum.elim g h) (Finset.mem_univ (Sum.inr b))

theorem commonDenominator_zero {ι : Type*} [Fintype ι] :
    commonDenominator Finset.univ (fun _ : ι ↦ (0 : ℚ)) = 1 :=
  Nat.dvd_one.mp ((commonDenominator_dvd_iff _ _ _).mpr fun _ _ ↦ by simp)

theorem commonDenominator_single {ι : Type*} [Fintype ι] [DecidableEq ι] (s₀ : ι) (c : ℚ) :
    commonDenominator Finset.univ (fun s ↦ if s = s₀ then c else 0) = c.den := by
  refine Nat.dvd_antisymm ((commonDenominator_dvd_iff _ _ _).mpr fun s _ ↦ ?_) ?_
  · split_ifs <;> simp
  · simpa using den_dvd_commonDenominator Finset.univ (fun s ↦ if s = s₀ then c else 0)
      (Finset.mem_univ s₀)

theorem rowDenominator_rowBlocks (hc : IsMarkedCubic core mark) (t : Fin p ⊕ (Fin k ⊕ Fin k)) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks M t) =
      commonDenominator Finset.univ (fun s ↦ Matrix.fromBlocks
        (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation) 0 0
        lollipopBlock t s) := by
  rw [← submatrix_eq_fromBlocks M hc, Count.rowDenominator,
    ← commonDenominator_equiv (colBlocks M)]
  rfl

theorem rowDenominator_inl (hc : IsMarkedCubic core mark) (i : Fin p) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks M (Sum.inl i)) =
      Count.rowDenominator (labelling M hc).presentation i := by
  rw [rowDenominator_rowBlocks M hc]
  have : (fun s ↦ Matrix.fromBlocks
      (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation) 0 0
      (lollipopBlock (k := k)) (Sum.inl i) s) =
      Sum.elim (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation i)
        (fun _ ↦ 0) := by
    funext s; rcases s with a | b <;> simp
  rw [this, commonDenominator_sumElim, commonDenominator_zero, Nat.lcm_one_right]
  rfl

theorem rowDenominator_inr_inl (hc : IsMarkedCubic core mark) (j : Fin k) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks M (Sum.inr (Sum.inl j))) =
      2 := by
  classical
  rw [rowDenominator_rowBlocks M hc]
  have : (fun s ↦ Matrix.fromBlocks
      (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation) 0 0
      (lollipopBlock (k := k)) (Sum.inr (Sum.inl j)) s) =
      fun s ↦ if s = Sum.inr (Sum.inl j) then (1 / 2 : ℚ) else 0 := by
    funext s
    rcases s with a | b
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, lollipopBlock, Matrix.diagonal_apply]
      by_cases h : Sum.inl j = b
      · subst h; simp
      · rw [ite_neg' h, ite_neg' (fun h' ↦ h (Sum.inr_injective h').symm)]
  rw [this, commonDenominator_single]
  norm_num

theorem rowDenominator_inr_inr (hc : IsMarkedCubic core mark) (j : Fin k) :
    Count.rowDenominator M.fullDim.labelling.presentation (rowBlocks M (Sum.inr (Sum.inr j))) =
      1 := by
  classical
  rw [rowDenominator_rowBlocks M hc]
  have : (fun s ↦ Matrix.fromBlocks
      (GluingDatum.LengthMatrixPresentation.matrix (labelling M hc).presentation) 0 0
      (lollipopBlock (k := k)) (Sum.inr (Sum.inr j)) s) =
      fun s ↦ if s = Sum.inr (Sum.inr j) then (2 : ℚ) else 0 := by
    funext s
    rcases s with a | b
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, lollipopBlock, Matrix.diagonal_apply]
      by_cases h : Sum.inr j = b
      · subst h; simp
      · rw [ite_neg' h, ite_neg' (fun h' ↦ h (Sum.inr_injective h').symm)]
  rw [this, commonDenominator_single]
  norm_num

/-- **`D_φ = 2^k D_{φ'}`.** -/
theorem denominatorProduct_labelling (hc : IsMarkedCubic core mark) :
    Count.denominatorProduct M.fullDim.labelling.presentation =
      2 ^ k * Count.denominatorProduct (labelling M hc).presentation := by
  rw [Count.denominatorProduct, ← Fintype.prod_equiv (rowBlocks M) _ _ (fun _ ↦ rfl),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [rowDenominator_inl M hc, rowDenominator_inr_inl M hc, rowDenominator_inr_inr M hc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one]
  rw [Count.denominatorProduct, mul_comm]

end Denominators


/-! ## 13.  The leaf count -/

section Leaves

/-- At a kept vertex, the deleted target edges are the bridge images of the marks over it. -/
theorem card_notKept_at {v : M.target.V} (hv : v ∈ Keep M) :
    ((GluingDatum.incidentEdges v).filter (fun e ↦ ¬ KeptEdge (Keep M) e)).card =
      (Finset.univ.filter (fun j ↦ xV M j = v)).card := by
  classical
  symm
  refine Finset.card_bij (fun j _ ↦ tb M j) ?_ (fun _ _ _ _ h ↦ tb_injective M h) ?_
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨hj' ▸ tb_mem_xV M j, ?_⟩
    rw [not_keptEdge_iff]; exact Or.inl ⟨j, rfl⟩
  · intro e he
    obtain ⟨heI, hk⟩ := Finset.mem_filter.mp he
    obtain ⟨j, rfl, hj⟩ := eq_tb_of_mem_incidentEdges M hv heI hk
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

theorem card_marks_at (hc : IsMarkedCubic core mark) (v : M.target.V) :
    (Finset.univ.filter (fun j ↦ xV M j = v)).card = if v ∈ Set.range (xV M) then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h ↦ xV_injective M hc h, fun h ↦ h ▸ rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun j _ hj ↦ h ⟨j, hj⟩

theorem card_kept_at (hc : IsMarkedCubic core mark) {v : M.target.V} (hv : v ∈ Keep M) :
    ((GluingDatum.incidentEdges v).filter (KeptEdge (Keep M))).card +
        (if v ∈ Set.range (xV M) then 1 else 0) = (GluingDatum.incidentEdges v).card := by
  rw [← card_marks_at M hc, ← card_notKept_at M hv]
  exact Finset.card_filter_add_card_filter_not _

theorem leafCount_rTarget_eq (hc : IsMarkedCubic core mark) :
    Count.leafCount (rTarget M) =
      (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
        (GluingDatum.incidentEdges v).card = 1)).card +
      (Finset.univ.filter (fun j ↦ (GluingDatum.incidentEdges (xV M j)).card = 2)).card := by
  classical
  have hImage : (Count.leafVertices (rTarget M)).map ⟨vIncl, vIncl_injective⟩ =
      (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
        (GluingDatum.incidentEdges v).card = 1)) ∪
      (Finset.univ.filter (fun j ↦ (GluingDatum.incidentEdges (xV M j)).card = 2)).image
        (xV M) := by
    ext v
    simp only [Finset.mem_map, Count.mem_leafVertices, Function.Embedding.coeFn_mk,
      Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨v', hLeaf, rfl⟩
      have hK := card_kept_at M hc (vIncl_mem v')
      have hL : ((GluingDatum.incidentEdges (vIncl v')).filter
          (KeptEdge (Keep M))).card = 1 := by
        rw [← card_incidentEdges_restrict]; exact hLeaf
      rw [hL] at hK
      split_ifs at hK with hx
      · obtain ⟨j, hj⟩ := hx
        right
        exact ⟨j, by rw [hj]; omega, hj⟩
      · left
        exact ⟨vIncl_mem v', hx, by omega⟩
    · rintro (⟨hv, hx, h1⟩ | ⟨j, h2, rfl⟩)
      · refine ⟨vRestrict v hv, ?_, rfl⟩
        change (GluingDatum.incidentEdges (vRestrict v hv)).card = 1
        have hK := card_kept_at M hc hv
        rw [ite_neg' hx] at hK
        rw [card_incidentEdges_restrict]
        exact (show ((GluingDatum.incidentEdges v).filter (KeptEdge (Keep M))).card = 1 by omega)
      · refine ⟨vRestrict (xV M j) (xV_mem_Keep M j), ?_, rfl⟩
        change (GluingDatum.incidentEdges (vRestrict (xV M j) (xV_mem_Keep M j))).card = 1
        have hK := card_kept_at M hc (xV_mem_Keep M j)
        rw [show (if xV M j ∈ Set.range (xV M) then 1 else 0) = 1 by simp] at hK
        rw [card_incidentEdges_restrict]
        exact (show ((GluingDatum.incidentEdges (xV M j)).filter (KeptEdge (Keep M))).card = 1 by
          omega)
  have hDisj : Disjoint (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
        (GluingDatum.incidentEdges v).card = 1))
      ((Finset.univ.filter (fun j ↦ (GluingDatum.incidentEdges (xV M j)).card = 2)).image
        (xV M)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv'
    exact (Finset.mem_filter.mp hv).2.2.1 ⟨j, rfl⟩
  rw [Count.leafCount, ← Finset.card_map ⟨vIncl, vIncl_injective⟩, hImage,
    Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _ (xV_injective M hc)]

theorem leafCount_target_eq :
    Count.leafCount M.target =
      (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
        (GluingDatum.incidentEdges v).card = 1)).card + k := by
  classical
  have hEq : Count.leafVertices M.target =
      (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
        (GluingDatum.incidentEdges v).card = 1)) ∪ Finset.univ.image (vC M) := by
    ext v
    simp only [Count.mem_leafVertices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image]
    constructor
    · intro hLeaf
      by_cases hv : v ∈ Keep M
      · left
        refine ⟨hv, ?_, hLeaf⟩
        rintro ⟨j, rfl⟩
        have := valency_xV M j
        have h1 : (GluingDatum.incidentEdges (xV M j)).card = 1 := hLeaf
        omega
      · right
        obtain ⟨j, hj | hj⟩ := exists_branch_of_notMem_Keep M hv
        · subst hj
          have := uP_divalent M j
          have h1 : (GluingDatum.incidentEdges (uP M j)).card = 1 := hLeaf
          omega
        · exact ⟨j, hj⟩
    · rintro (⟨-, -, h1⟩ | ⟨j, rfl⟩)
      · exact h1
      · exact vC_isLeaf M j
  have hDisj : Disjoint (Finset.univ.filter (fun v ↦ v ∈ Keep M ∧ v ∉ Set.range (xV M) ∧
      (GluingDatum.incidentEdges v).card = 1)) (Finset.univ.image (vC M)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv'
    exact vC_notMem_Keep M j (Finset.mem_filter.mp hv).2.1
  rw [Count.leafCount, hEq, Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _ (vC_injective M), Finset.card_univ, Fintype.card_fin]

/-- **The leaf count**: `l(T) + #{folds} = l(T') + k`. -/
theorem leafCount_restrict (hc : IsMarkedCubic core mark) :
    Count.leafCount M.target +
        (Finset.univ.filter fun j ↦ (rData M).localRamification (markSource M j).1.1
          ⟨(markSource M j).1.2, (markSource M j).2⟩ = 2).card =
      Count.leafCount (rTarget M) + k := by
  have hFold : (Finset.univ.filter fun j ↦ (rData M).localRamification (markSource M j).1.1
      ⟨(markSource M j).1.2, (markSource M j).2⟩ = 2) =
      Finset.univ.filter (fun j ↦ (GluingDatum.incidentEdges (xV M j)).card = 2) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← markRamification_eq_one_iff M j]
    have h : (rData M).localRamification (markSource M j).1.1
        ⟨(markSource M j).1.2, (markSource M j).2⟩ =
        M.data.localRamification (xV M j) ⟨(markV M j).1.2, (markV M j).2⟩ + 1 :=
      localRamification_markSource M hc j
    rw [h]
    constructor <;> intro h' <;> omega
  rw [hFold, leafCount_rTarget_eq M hc, leafCount_target_eq M]
  ring

end Leaves

end

end DraismaVargas.Count.MarkedCount.Lollipops
