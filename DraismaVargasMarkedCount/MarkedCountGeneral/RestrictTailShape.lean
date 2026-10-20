module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RigidTail
public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargasMarkedCount.MarkedCount.RestrictDatum

@[expose] public section

/-!
# Restriction over the tails: the shape of the tails in the target

For a member `M` over the tailed core `T.H` (a caterpillar `T.caterpillarAt j` at every mark),
the image of the tail at mark `j` in the target is the subtree `T_tail,j` of the rigidity lemma
(module `Rigidity`), attached to the rest of the target at `φ(u_j)` only:

* `xMark j = φ(u_j)`, kept;
* `xSpine j i = φ(B_{i+1})` (trivalent), `xBulb j i = φ(A_{i+1})` (divalent), `xLeaf j i` (the loop
  leaf), deleted;
* the tail edges `tEdge j s` (`TailAt.tcol`), with the incidences `incidentEdges_xSpine`,
  `incidentEdges_xBulb`, `incidentEdges_xLeaf` and the first path edge at `xMark j`.

All tails at once: the deleted vertices are distinct (`xSpine_inj`, `xBulb_inj`, `xLeaf_inj` and
the cross inequalities), and never the image of a mark. The kept vertices `Keep` are the rest; a
target edge is deleted iff it is a tail edge (`not_keptEdge_iff`), and the only deleted edge at a
kept vertex is the first path edge at the image of a mark (`eq_tEdge_zero_of_kept`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

/-! ## 1.  The source vertices and the target vertices of the tails -/

/-- The caterpillar at mark `j`. -/
abbrev cat (j : Fin k) : CaterpillarAt T.H (T.oldVertex (mark j)) (c j) := T.caterpillarAt j

/-- `u_j`, the branch vertex of the mark. -/
def uSource (j : Fin k) : M.data.SourceVertex := TailAt.vSource M (T.oldVertex (mark j))

/-- `φ(u_j)`. -/
def xMark (j : Fin k) : M.target.V := (uSource T M j).1.1

/-- `φ(B_{i+1})`, the image of a spine vertex. -/
def xSpine (j : Fin k) (i : Fin (c j)) : M.target.V := (TailAt.spineV (cat T j) M i).1.1

/-- `φ(A_{i+1})`, the image of a bulb (the lollipop's `uP`). -/
def xBulb (j : Fin k) (i : Fin (c j + 1)) : M.target.V := LoopAt.uP M ((cat T j).isLoop i)

/-- The loop leaf of the bulb `A_{i+1}`. -/
def xLeaf (j : Fin k) (i : Fin (c j + 1)) : M.target.V := LoopAt.vC M ((cat T j).isLoop i)

/-- The tail edges. -/
def tEdge (j : Fin k) (s : CatSlot (c j)) : M.target.edges :=
  TailAt.tcol (cat T j) M (T.cubic hc) s

theorem nonDanglingValency_uSource (j : Fin k) : nonDanglingValency M.data (uSource T M j) = 3 :=
  TailAt.nonDanglingValency_vSource M _

theorem xBulb_eq (j : Fin k) (i : Fin (c j + 1)) :
    xBulb T M j i = (TailAt.vSource M ((cat T j).vertex (Sum.inr i))).1.1 := by
  unfold xBulb LoopAt.uP
  rw [TailAt.loopV_eq]

/-- The vertex of the tail at `j` named `x`. -/
theorem cat_vertex (j : Fin k) (x : CatVertex (c j)) :
    (cat T j).vertex x = T.vertexEquiv (Sum.inr ⟨j, x⟩) := rfl

theorem cat_slot (j : Fin k) (s : CatSlot (c j)) : (cat T j).slot s = T.tailSlot j s := rfl

/-! ### Incidences at the deleted vertices -/

theorem incidentEdges_xSpine (j : Fin k) (i : Fin (c j)) :
    GluingDatum.incidentEdges (xSpine T M j i) =
      {tEdge T hc M j (Sum.inr (Sum.inl i)), tEdge T hc M j (Sum.inl i.succ),
        tEdge T hc M j (Sum.inl i.castSucc)} := by
  have h := SpineStep.spineStep_incidentEdges M.fullDim (TailAt.spineHyp (cat T j) M (T.cubic hc) i)
  rw [TailAt.third_spineHyp] at h
  exact h

theorem incidentEdges_xBulb (j : Fin k) (i : Fin (c j + 1)) :
    GluingDatum.incidentEdges (xBulb T M j i) =
      {tEdge T hc M j (bulbBridge i), tEdge T hc M j (Sum.inr (Sum.inr i))} := by
  unfold xBulb tEdge
  rw [LoopAt.incidentEdges_uP]
  congr 2
  revert i
  intro i
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [bulbBridge_last]
    change _ = (TailAt.pathE (cat T j) M (T.cubic hc) (Fin.last (c j))).1.1.1
    rw [TailAt.pathE_last]; rfl
  · rw [bulbBridge_castSucc]; rfl

theorem incidentEdges_xLeaf (j : Fin k) (i : Fin (c j + 1)) :
    GluingDatum.incidentEdges (xLeaf T M j i) = {tEdge T hc M j (Sum.inr (Sum.inr i))} :=
  LoopAt.incidentEdges_vC M ((cat T j).isLoop i)

include hc in
theorem xSpine_trivalent (j : Fin k) (i : Fin (c j)) :
    (GluingDatum.incidentEdges (xSpine T M j i)).card = 3 :=
  SpineStep.spineStep_trivalent M.fullDim (TailAt.spineHyp (cat T j) M (T.cubic hc) i)

theorem xBulb_divalent (j : Fin k) (i : Fin (c j + 1)) :
    (GluingDatum.incidentEdges (xBulb T M j i)).card = 2 :=
  LoopAt.uP_divalent M ((cat T j).isLoop i)

theorem xLeaf_isLeaf (j : Fin k) (i : Fin (c j + 1)) :
    (GluingDatum.incidentEdges (xLeaf T M j i)).card = 1 :=
  LoopAt.vC_isLeaf M ((cat T j).isLoop i)

include hc in
/-- The only non-dangling vertex over `xSpine` is the spine vertex. -/
theorem eq_spineV_of_over {j : Fin k} {i : Fin (c j)} {X : M.data.SourceVertex}
    (hX : X.1.1 = xSpine T M j i) (hNd : nonDanglingValency M.data X ≠ 0) :
    X = TailAt.spineV (cat T j) M i :=
  SpineStep.spineStep_unique_vertex M.fullDim (TailAt.spineHyp (cat T j) M (T.cubic hc) i) hX hNd

/-- The only non-dangling vertex over `xBulb` is the bulb vertex. -/
theorem eq_bulbV_of_over {j : Fin k} {i : Fin (c j + 1)} {X : M.data.SourceVertex}
    (hX : X.1.1 = xBulb T M j i) (hNd : nonDanglingValency M.data X ≠ 0) :
    X = TailAt.vSource M ((cat T j).vertex (Sum.inr i)) := by
  rw [← TailAt.loopV_eq]
  by_contra hne
  exact hNd (LoopAt.nonDanglingValency_over_uP M ((cat T j).isLoop i) hX hne)

/-! ### The first path edge at the image of the mark -/

theorem tEdge_zero_mem_xMark (j : Fin k) :
    tEdge T hc M j (Sum.inl 0) ∈ GluingDatum.incidentEdges (xMark T M j) := by
  have h := TailAt.pathE_incident_tail (cat T j) M (T.cubic hc) 0
  rw [(cat T j).tail_path_zero] at h
  exact SpineStep.target_mem_of_incident h

/-! ## 2.  Distinctness -/

theorem vertexEquiv_inr_ne_old (j : Fin k) (x : CatVertex (c j)) (v : Fin n) :
    T.vertexEquiv (Sum.inr ⟨j, x⟩) ≠ T.oldVertex v := by
  intro h
  have := T.vertexEquiv.injective h
  simp at this

theorem vertexEquiv_inr_inj {j j' : Fin k} {x : CatVertex (c j)} {x' : CatVertex (c j')}
    (h : T.vertexEquiv (Sum.inr ⟨j, x⟩) = T.vertexEquiv (Sum.inr ⟨j', x'⟩)) :
    (⟨j, x⟩ : Σ j, CatVertex (c j)) = ⟨j', x'⟩ :=
  Sum.inr_injective (T.vertexEquiv.injective h)

include hc in
theorem xMark_ne_xSpine (j j' : Fin k) (i : Fin (c j')) : xMark T M j ≠ xSpine T M j' i := by
  intro h
  have this := eq_spineV_of_over T hc M (X := uSource T M j) h
    (by rw [nonDanglingValency_uSource]; omega)
  have h2 := TailAt.vSource_injective M this
  exact vertexEquiv_inr_ne_old T j' _ _ h2.symm

theorem xMark_ne_xBulb (j j' : Fin k) (i : Fin (c j' + 1)) : xMark T M j ≠ xBulb T M j' i := by
  intro h
  have h1 := eq_bulbV_of_over T M (X := uSource T M j) h
    (by rw [nonDanglingValency_uSource]; omega)
  have h2 := TailAt.vSource_injective M h1
  exact vertexEquiv_inr_ne_old T j' _ _ h2.symm

theorem xMark_ne_xLeaf (j j' : Fin k) (i : Fin (c j' + 1)) : xMark T M j ≠ xLeaf T M j' i := by
  intro h
  have := LoopAt.nonDanglingValency_over_vC M ((cat T j').isLoop i) (X := uSource T M j) h
  rw [nonDanglingValency_uSource] at this
  omega

include hc in
theorem xSpine_ne_xBulb (j : Fin k) (i : Fin (c j)) (j' : Fin k) (i' : Fin (c j' + 1)) :
    xSpine T M j i ≠ xBulb T M j' i' := by
  intro h
  have h1 := xSpine_trivalent T hc M j i
  rw [h, xBulb_divalent] at h1
  omega

include hc in
theorem xSpine_ne_xLeaf (j : Fin k) (i : Fin (c j)) (j' : Fin k) (i' : Fin (c j' + 1)) :
    xSpine T M j i ≠ xLeaf T M j' i' := by
  intro h
  have h1 := xSpine_trivalent T hc M j i
  rw [h, xLeaf_isLeaf] at h1
  omega

theorem xBulb_ne_xLeaf (j : Fin k) (i : Fin (c j + 1)) (j' : Fin k) (i' : Fin (c j' + 1)) :
    xBulb T M j i ≠ xLeaf T M j' i' := by
  intro h
  have h1 := xBulb_divalent T M j i
  rw [h, xLeaf_isLeaf] at h1
  omega

include hc in
theorem xSpine_inj {j j' : Fin k} {i : Fin (c j)} {i' : Fin (c j')}
    (h : xSpine T M j i = xSpine T M j' i') :
    (⟨j, Sum.inl i⟩ : Σ j, CatVertex (c j)) = ⟨j', Sum.inl i'⟩ := by
  have h1 := eq_spineV_of_over T hc M (X := TailAt.spineV (cat T j') M i') h.symm
    (by rw [TailAt.nonDanglingValency_vSource]; omega)
  exact (vertexEquiv_inr_inj T (TailAt.vSource_injective M h1)).symm

theorem xBulb_inj {j j' : Fin k} {i : Fin (c j + 1)} {i' : Fin (c j' + 1)}
    (h : xBulb T M j i = xBulb T M j' i') :
    (⟨j, Sum.inr i⟩ : Σ j, CatVertex (c j)) = ⟨j', Sum.inr i'⟩ := by
  have h1 := eq_bulbV_of_over T M (X := TailAt.vSource M ((cat T j').vertex (Sum.inr i')))
    ((xBulb_eq T M j' i').symm.trans h.symm)
    (by rw [TailAt.nonDanglingValency_vSource]; omega)
  exact (vertexEquiv_inr_inj T (TailAt.vSource_injective M h1)).symm

theorem xLeaf_inj {j j' : Fin k} {i : Fin (c j + 1)} {i' : Fin (c j' + 1)}
    (h : xLeaf T M j i = xLeaf T M j' i') :
    (⟨j, Sum.inr (Sum.inr i)⟩ : Σ j, CatSlot (c j)) = ⟨j', Sum.inr (Sum.inr i')⟩ := by
  have h1 := LollipopLeafRow.loopLeaf_inj M ((cat T j).isLoop i) ((cat T j').isLoop i') h
  exact Sum.inr_injective (T.slotEquiv.injective h1)

/-! ## 3.  All the tail vertices and edges at once -/

/-- The kinds of deleted target vertices of a tail: spine images, bulb images, leaves. -/
abbrev TailV (c : ℕ) : Type := Fin c ⊕ (Fin (c + 1) ⊕ Fin (c + 1))

/-- **The deleted target vertices**, all tails at once. -/
def tailVertex : (Σ j, TailV (c j)) → M.target.V
  | ⟨j, Sum.inl i⟩ => xSpine T M j i
  | ⟨j, Sum.inr (Sum.inl i)⟩ => xBulb T M j i
  | ⟨j, Sum.inr (Sum.inr i)⟩ => xLeaf T M j i

include hc in
theorem tailVertex_injective : Function.Injective (tailVertex T M) := by
  rintro ⟨j, i | i | i⟩ ⟨j', i' | i' | i'⟩ h <;> simp only [tailVertex] at h
  · have := xSpine_inj T hc M h
    simp only [Sigma.mk.inj_iff] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq, Sum.inl.injEq] at h2
    rw [h2]
  · exact absurd h (xSpine_ne_xBulb T hc M _ _ _ _)
  · exact absurd h (xSpine_ne_xLeaf T hc M _ _ _ _)
  · exact absurd h.symm (xSpine_ne_xBulb T hc M _ _ _ _)
  · have := xBulb_inj T M h
    simp only [Sigma.mk.inj_iff] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq, Sum.inr.injEq] at h2
    rw [h2]
  · exact absurd h (xBulb_ne_xLeaf T M _ _ _ _)
  · exact absurd h.symm (xSpine_ne_xLeaf T hc M _ _ _ _)
  · exact absurd h.symm (xBulb_ne_xLeaf T M _ _ _ _)
  · have := xLeaf_inj T M h
    simp only [Sigma.mk.inj_iff] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq, Sum.inr.injEq] at h2
    rw [h2]

include hc in
theorem xMark_ne_tailVertex (j : Fin k) (q : Σ j, TailV (c j)) :
    xMark T M j ≠ tailVertex T M q := by
  rcases q with ⟨j', i | i | i⟩
  · exact xMark_ne_xSpine T hc M j j' i
  · exact xMark_ne_xBulb T M j j' i
  · exact xMark_ne_xLeaf T M j j' i

/-- **The kept target vertices** (the vertices of `T'`). -/
def Keep : Finset M.target.V := (Finset.univ.image (tailVertex T M))ᶜ

theorem mem_Keep {v : M.target.V} : v ∈ Keep T M ↔ ∀ q, tailVertex T M q ≠ v := by
  simp only [Keep, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists]

theorem tailVertex_notMem_Keep (q : Σ j, TailV (c j)) : tailVertex T M q ∉ Keep T M := by
  rw [mem_Keep]; push Not; exact ⟨q, rfl⟩

theorem xSpine_notMem_Keep (j : Fin k) (i : Fin (c j)) : xSpine T M j i ∉ Keep T M :=
  tailVertex_notMem_Keep T M ⟨j, Sum.inl i⟩

theorem xBulb_notMem_Keep (j : Fin k) (i : Fin (c j + 1)) : xBulb T M j i ∉ Keep T M :=
  tailVertex_notMem_Keep T M ⟨j, Sum.inr (Sum.inl i)⟩

theorem xLeaf_notMem_Keep (j : Fin k) (i : Fin (c j + 1)) : xLeaf T M j i ∉ Keep T M :=
  tailVertex_notMem_Keep T M ⟨j, Sum.inr (Sum.inr i)⟩

include hc in
theorem xMark_mem_Keep (j : Fin k) : xMark T M j ∈ Keep T M := by
  rw [mem_Keep]
  intro q hq
  exact xMark_ne_tailVertex T hc M j q hq.symm

include hc in
theorem Keep_nonempty : (Keep T M).Nonempty := by
  rcases isEmpty_or_nonempty (Fin k) with hk | ⟨⟨j⟩⟩
  · obtain ⟨v⟩ := M.target.instNonempty
    refine ⟨v, (mem_Keep T M).mpr fun q ↦ ?_⟩
    exact (hk.false q.1).elim
  · exact ⟨_, xMark_mem_Keep T hc M j⟩

/-! ### The tail edges -/

/-- **The tail edges**, all tails at once. -/
def tailEdge : (Σ j, CatSlot (c j)) → M.target.edges := fun q ↦ tEdge T hc M q.1 q.2

theorem tEdge_row (j : Fin k) (s : CatSlot (c j)) {F : M.data.SourceEdge}
    (hF : ¬ IsDangling M.data F) (hT : F.1.1 = tEdge T hc M j s) :
    NonDanglingEdge.stablePath (⟨F, hF⟩ : NonDanglingEdge M.data) =
      M.ident.row.symm (T.tailSlot j s) :=
  TailAt.onRow_of_over_tcol (cat T j) M (T.cubic hc) s hF hT

theorem tailEdge_injective : Function.Injective (tailEdge T hc M) := by
  rintro ⟨j, s⟩ ⟨j', s'⟩ h
  obtain ⟨F, hT, hS⟩ := M.fullDim.noDanglingTargetFibres (tEdge T hc M j s)
  have h1 := tEdge_row T hc M j s hS hT
  have h2 := tEdge_row T hc M j' s' hS (hT.trans h)
  have := T.slotEquiv.injective (M.ident.row.symm.injective (h1.symm.trans h2))
  exact Sum.inr_injective this

/-- An edge at two distinct vertices has them as its ends. -/
theorem eq_of_mem_incidentEdges {e : M.target.edges} {a b v : M.target.V}
    (ha : e ∈ GluingDatum.incidentEdges a) (hb : e ∈ GluingDatum.incidentEdges b) (hab : a ≠ b)
    (hv : e ∈ GluingDatum.incidentEdges v) : v = a ∨ v = b := by
  have ha' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges ha
  have hb' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges hb
  have hv' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges hv
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rcases hv' with hv' | hv'
  · exact Or.inl (hv'.symm.trans ha')
  · exact absurd (ha'.symm.trans hb') hab
  · exact Or.inl (hv'.symm.trans ha')
  · exact Or.inr (hv'.symm.trans hb')
  · exact Or.inr (hv'.symm.trans hb')
  · exact Or.inl (hv'.symm.trans ha')
  · exact absurd (ha'.symm.trans hb') hab
  · exact Or.inl (hv'.symm.trans ha')

theorem mem_incidentEdges_iff_end {e : M.target.edges} {v : M.target.V} :
    e ∈ GluingDatum.incidentEdges v ↔
      (e : M.target.V × M.target.V).1 = v ∨ (e : M.target.V × M.target.V).2 = v := by
  simp [GluingDatum.incidentEdges]

/-- The lower end of the path edge `h_{i+1}`: `x_j` or the spine image below. -/
def lowerX (j : Fin k) (i : Fin (c j + 1)) : M.target.V :=
  (TailAt.vSource M (T.H.tail ((cat T j).slot (Sum.inl i)))).1.1

/-- The upper end of the path edge `h_{i+1}`: the spine image above, or the last bulb. -/
def upperX (j : Fin k) (i : Fin (c j + 1)) : M.target.V :=
  (TailAt.vSource M (T.H.head ((cat T j).slot (Sum.inl i)))).1.1

theorem path_mem_lowerX (j : Fin k) (i : Fin (c j + 1)) :
    tEdge T hc M j (Sum.inl i) ∈ GluingDatum.incidentEdges (lowerX T M j i) :=
  SpineStep.target_mem_of_incident (TailAt.pathE_incident_tail (cat T j) M (T.cubic hc) i)

theorem path_mem_upperX (j : Fin k) (i : Fin (c j + 1)) :
    tEdge T hc M j (Sum.inl i) ∈ GluingDatum.incidentEdges (upperX T M j i) :=
  SpineStep.target_mem_of_incident (TailAt.pathE_incident_head (cat T j) M (T.cubic hc) i)

theorem lowerX_zero (j : Fin k) : lowerX T M j 0 = xMark T M j := by
  unfold lowerX xMark uSource; rw [(cat T j).tail_path_zero]

theorem lowerX_succ (j : Fin k) (i : Fin (c j)) : lowerX T M j i.succ = xSpine T M j i := by
  unfold lowerX xSpine; rw [(cat T j).tail_path_succ]

theorem upperX_castSucc (j : Fin k) (i : Fin (c j)) : upperX T M j i.castSucc = xSpine T M j i := by
  unfold upperX xSpine; rw [(cat T j).head_path_castSucc]

theorem upperX_last (j : Fin k) : upperX T M j (Fin.last (c j)) = xBulb T M j (Fin.last (c j)) := by
  unfold upperX; rw [(cat T j).head_path_last, xBulb_eq]

theorem upperX_notMem_Keep (j : Fin k) (i : Fin (c j + 1)) : upperX T M j i ∉ Keep T M := by
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [upperX_last]; exact xBulb_notMem_Keep T M j _
  · rw [upperX_castSucc]; exact xSpine_notMem_Keep T M j i'

include hc in
theorem lowerX_ne_upperX (j : Fin k) (i : Fin (c j + 1)) : lowerX T M j i ≠ upperX T M j i := by
  intro h
  have hne := (cat T j).tail_path_ne_head i
  apply hne
  have h1 := TailAt.pathE_incident_tail (cat T j) M (T.cubic hc) i
  have h2 := TailAt.pathE_incident_head (cat T j) M (T.cubic hc) i
  have hEq := LollipopBridgeFibre.eq_of_incident_of_target_eq h h1 h2
  exact (TailAt.vSource_injective M hEq)

/-- **A tail edge has a deleted end.** -/
theorem exists_deleted_end (j : Fin k) (s : CatSlot (c j)) :
    ∃ v, v ∉ Keep T M ∧ tEdge T hc M j s ∈ GluingDatum.incidentEdges v := by
  rcases s with i | i | i
  · exact ⟨_, upperX_notMem_Keep T M j i, path_mem_upperX T hc M j i⟩
  · refine ⟨_, xSpine_notMem_Keep T M j i, ?_⟩
    rw [incidentEdges_xSpine T hc M]; simp
  · refine ⟨_, xBulb_notMem_Keep T M j i, ?_⟩
    rw [incidentEdges_xBulb T hc M]; simp

/-- **The deleted target edges are the tail edges.** -/
theorem not_keptEdge_iff (e : M.target.edges) :
    ¬ KeptEdge (Keep T M) e ↔ ∃ j s, e = tEdge T hc M j s := by
  constructor
  · intro he
    have hv : ∃ v, v ∉ Keep T M ∧ e ∈ GluingDatum.incidentEdges v := by
      unfold KeptEdge at he
      by_cases h1 : (e : M.target.V × M.target.V).1 ∈ Keep T M
      · exact ⟨_, fun h2 ↦ he ⟨h1, h2⟩, (mem_incidentEdges_iff_end T M).mpr (Or.inr rfl)⟩
      · exact ⟨_, h1, (mem_incidentEdges_iff_end T M).mpr (Or.inl rfl)⟩
    obtain ⟨v, hvK, hve⟩ := hv
    rw [mem_Keep] at hvK
    push Not at hvK
    obtain ⟨⟨j, i | i | i⟩, rfl⟩ := hvK
    · simp only [tailVertex, incidentEdges_xSpine T hc M, Finset.mem_insert,
        Finset.mem_singleton] at hve
      rcases hve with h | h | h <;> exact ⟨j, _, h⟩
    · simp only [tailVertex, incidentEdges_xBulb T hc M, Finset.mem_insert,
        Finset.mem_singleton] at hve
      rcases hve with h | h <;> exact ⟨j, _, h⟩
    · simp only [tailVertex, incidentEdges_xLeaf T hc M, Finset.mem_singleton] at hve
      exact ⟨j, _, hve⟩
  · rintro ⟨j, s, rfl⟩ ⟨h1, h2⟩
    obtain ⟨v, hv, hve⟩ := exists_deleted_end T hc M j s
    rcases (mem_incidentEdges_iff_end T M).mp hve with h | h
    · exact hv (h ▸ h1)
    · exact hv (h ▸ h2)

theorem not_keptEdge_tEdge (j : Fin k) (s : CatSlot (c j)) : ¬ KeptEdge (Keep T M) (tEdge T hc M j s) :=
  (not_keptEdge_iff T hc M _).mpr ⟨j, s, rfl⟩

/-- **The only deleted edge at a kept vertex is the first path edge at the image of a mark.** -/
theorem eq_tEdge_zero_of_kept {v : M.target.V} (hv : v ∈ Keep T M) {e : M.target.edges}
    (he : e ∈ GluingDatum.incidentEdges v) (hk : ¬ KeptEdge (Keep T M) e) :
    ∃ j, e = tEdge T hc M j (Sum.inl 0) ∧ xMark T M j = v := by
  obtain ⟨j, s, rfl⟩ := (not_keptEdge_iff T hc M e).mp hk
  have hU := upperX_notMem_Keep T M
  rcases s with i | i | i
  · rcases eq_of_mem_incidentEdges T M (path_mem_lowerX T hc M j i) (path_mem_upperX T hc M j i)
      (lowerX_ne_upperX T hc M j i) he with h | h
    · refine Fin.cases (fun h ↦ ⟨j, rfl, by rw [h, lowerX_zero]⟩) (fun i' h ↦ ?_) i h
      rw [h, lowerX_succ] at hv
      exact absurd hv (xSpine_notMem_Keep T M j i')
    · exact absurd (h ▸ hv) (hU j i)
  · have hS : tEdge T hc M j (Sum.inr (Sum.inl i)) ∈ GluingDatum.incidentEdges (xSpine T M j i) := by
      rw [incidentEdges_xSpine T hc M]; simp
    have hB : tEdge T hc M j (Sum.inr (Sum.inl i)) ∈
        GluingDatum.incidentEdges (xBulb T M j i.castSucc) := by
      rw [incidentEdges_xBulb T hc M, bulbBridge_castSucc]; simp
    rcases eq_of_mem_incidentEdges T M hS hB (xSpine_ne_xBulb T hc M _ _ _ _) he with h | h
    · exact absurd (h ▸ hv) (xSpine_notMem_Keep T M j i)
    · exact absurd (h ▸ hv) (xBulb_notMem_Keep T M j _)
  · have hB : tEdge T hc M j (Sum.inr (Sum.inr i)) ∈ GluingDatum.incidentEdges (xBulb T M j i) := by
      rw [incidentEdges_xBulb T hc M]; simp
    have hL : tEdge T hc M j (Sum.inr (Sum.inr i)) ∈ GluingDatum.incidentEdges (xLeaf T M j i) := by
      rw [incidentEdges_xLeaf T hc M]; simp
    rcases eq_of_mem_incidentEdges T M hB hL (xBulb_ne_xLeaf T M _ _ _ _) he with h | h
    · exact absurd (h ▸ hv) (xBulb_notMem_Keep T M j i)
    · exact absurd (h ▸ hv) (xLeaf_notMem_Keep T M j i)

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
