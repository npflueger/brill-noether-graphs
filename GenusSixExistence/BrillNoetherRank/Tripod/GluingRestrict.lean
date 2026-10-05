module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gluing

@[expose] public section

/-!
# Restricting an isomorphism of glued data

Infrastructure for the class-level gluing lemmas of `GluingClasses.lean`, in
particular injectivity on classes (`nonempty_iso_of_isGluingOf_iso`). Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection, "Injective": deleting from
glue(ψ) the new sheet and the arms, and undoing the refinement at the marks, gives back ψ).

* **Generic** (`equivOfRange`, `restrictPerm`, `extendNew_relabel`, `unorderedEnds_of_incident`):
  restricting an equivalence along two injections with corresponding ranges, a permutation of
  `Fin (d + 1)` fixing `Fin.last d` to `Fin d`, and the partition `extendNew P` relabelled by such
  a permutation.
* **Un-refining** (`exists_unrefine`): an isomorphism `refineDatum D t ≅ refineDatum D' t'`
  carrying the fresh vertex to the fresh vertex descends to an isomorphism `D ≅ D'`, compatible
  with the old source vertices (`Refine.oldSV`) and with the parents of source edges
  (`Refine.parentSE`).
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion

/-! ## Generic facts -/

section Generic

/-- **Restrict an equivalence along two injections whose ranges correspond.** -/
noncomputable def equivOfRange {α β γ δ : Type*} (e : α ≃ β) (f : γ → α) (g : δ → β)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h₁ : ∀ c, ∃ c', e (f c) = g c') (h₂ : ∀ c', ∃ c, e.symm (g c') = f c) : γ ≃ δ where
  toFun c := Classical.choose (h₁ c)
  invFun c' := Classical.choose (h₂ c')
  left_inv c := by
    apply hf
    have hA := Classical.choose_spec (h₂ (Classical.choose (h₁ c)))
    have hB := Classical.choose_spec (h₁ c)
    rw [← hA, ← hB, Equiv.symm_apply_apply]
  right_inv c' := by
    apply hg
    have hA := Classical.choose_spec (h₁ (Classical.choose (h₂ c')))
    have hB := Classical.choose_spec (h₂ c')
    rw [← hA, ← hB, Equiv.apply_symm_apply]

theorem equivOfRange_spec {α β γ δ : Type*} (e : α ≃ β) (f : γ → α) (g : δ → β)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h₁ : ∀ c, ∃ c', e (f c) = g c') (h₂ : ∀ c', ∃ c, e.symm (g c') = f c) (c : γ) :
    e (f c) = g (equivOfRange e f g hf hg h₁ h₂ c) :=
  Classical.choose_spec (h₁ c)

/-- **A permutation of `Fin (d + 1)` fixing the last sheet**, as a permutation of `Fin d`. -/
def restrictPerm {d : ℕ} (σ : Equiv.Perm (Fin (d + 1))) (h : σ (Fin.last d) = Fin.last d) :
    Equiv.Perm (Fin d) where
  toFun i := (σ i.castSucc).castPred fun h' ↦
    (Fin.castSucc_lt_last i).ne (σ.injective (h'.trans h.symm))
  invFun i := (σ.symm i.castSucc).castPred fun h' ↦
    (Fin.castSucc_lt_last i).ne (by rw [← Equiv.apply_symm_apply σ i.castSucc, h', h])
  left_inv i := by simp
  right_inv i := by simp

@[simp] theorem castSucc_restrictPerm {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (h : σ (Fin.last d) = Fin.last d) (i : Fin d) :
    (restrictPerm σ h i).castSucc = σ i.castSucc := by
  simp only [restrictPerm, Equiv.coe_fn_mk, Fin.castSucc_castPred]

@[simp] theorem castSucc_restrictPerm_symm {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (h : σ (Fin.last d) = Fin.last d) (i : Fin d) :
    ((restrictPerm σ h).symm i).castSucc = σ.symm i.castSucc := by
  simp only [restrictPerm, Equiv.coe_fn_symm_mk, Fin.castSucc_castPred]

theorem symm_last_of {d : ℕ} {σ : Equiv.Perm (Fin (d + 1))} (h : σ (Fin.last d) = Fin.last d) :
    σ.symm (Fin.last d) = Fin.last d := by
  rw [Equiv.symm_apply_eq, h]

/-- **Relabelling `extendNew P`** by a permutation fixing the new sheet. -/
theorem extendNew_relabel {d : ℕ} (P : SheetPartition d) (σ : Equiv.Perm (Fin (d + 1)))
    (h : σ (Fin.last d) = Fin.last d) :
    (SheetOps.extendNew P).relabel σ = SheetOps.extendNew (P.relabel (restrictPerm σ h)) := by
  apply SheetPartition.ext_repr
  funext j
  induction j using Fin.lastCases with
  | last =>
    show σ ((SheetOps.extendNew P).repr (σ.symm (Fin.last d))) =
      (SheetOps.extendNew (P.relabel (restrictPerm σ h))).repr (Fin.last d)
    rw [symm_last_of h, SheetOps.extendNew_repr_last, SheetOps.extendNew_repr_last, h]
  | cast i =>
    show σ ((SheetOps.extendNew P).repr (σ.symm i.castSucc)) =
      (SheetOps.extendNew (P.relabel (restrictPerm σ h))).repr i.castSucc
    rw [← castSucc_restrictPerm_symm σ h, SheetOps.extendNew_repr_castSucc,
      ← castSucc_restrictPerm σ h, SheetOps.extendNew_repr_castSucc]
    rfl

theorem extendNew_injective {d : ℕ} : Function.Injective (SheetOps.extendNew (d := d)) := by
  intro P Q h
  apply SheetPartition.ext_repr
  funext i
  have := congrArg (fun R : SheetPartition (d + 1) ↦ R.repr i.castSucc) h
  simpa using this

/-- Two representatives of one block are equal. -/
theorem eq_of_rel_of_repr {d : ℕ} {P : SheetPartition d} {a b : Fin d} (h : P.Rel a b)
    (ha : P.repr a = a) (hb : P.repr b = b) : a = b := by
  rw [← ha, ← hb]
  exact h

/-- **Unordered ends from incidence**: a bijection matching the incident vertices of two
loopless ends matches the ends up to order. -/
theorem unorderedEnds_of_incident {α β : Type*} (f : α ≃ β) (a : α × α) (b : β × β)
    (ha : a.1 ≠ a.2) (h : ∀ v, (b.1 = f v ∨ b.2 = f v) ↔ (a.1 = v ∨ a.2 = v)) :
    UnorderedEnds f a b := by
  have h1 := (h a.1).mpr (Or.inl rfl)
  have h2 := (h a.2).mpr (Or.inr rfl)
  have hne : f a.1 ≠ f a.2 := f.injective.ne ha
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h2 h1)
  · exact absurd (h1.symm.trans h2) hne

theorem mem_incidentEdges_iff {S : CFGraph} (v : S.V) (e : S.edges) :
    e ∈ GluingDatum.incidentEdges v ↔ ((e : S.V × S.V).1 = v ∨ (e : S.V × S.V).2 = v) := by
  simp [GluingDatum.incidentEdges]

variable {S₁ S₂ S₃ : CFGraph} {k : ℕ} {E₁ : GluingDatum S₁ k} {E₂ : GluingDatum S₂ k}
  {E₃ : GluingDatum S₃ k}

theorem iso_mem_incidentEdges_iff (iso : GeometricDatumIso E₁ E₂) (e : S₁.edges) (v : S₁.V) :
    iso.targetEdge e ∈ GluingDatum.incidentEdges (iso.targetVertex v) ↔
      e ∈ GluingDatum.incidentEdges v := by
  rw [mem_incidentEdges_iff, mem_incidentEdges_iff]
  exact iso.target_incident_map_iff e v

theorem sourceVertexEquiv_val (iso : GeometricDatumIso E₁ E₂) (x : E₁.SourceVertex) :
    (iso.sourceVertexEquiv x).1 = (iso.targetVertex x.1.1, iso.vertexPerm x.1.1 x.1.2) := rfl

theorem sourceEdgeEquiv_val (iso : GeometricDatumIso E₁ E₂) (x : E₁.SourceEdge) :
    (iso.sourceEdgeEquiv x).1 = (iso.targetEdge x.1.1, iso.edgePerm x.1.1 x.1.2) := rfl

theorem trans_sourceVertexEquiv (A : GeometricDatumIso E₁ E₂) (B : GeometricDatumIso E₂ E₃)
    (x : E₁.SourceVertex) :
    (A.trans B).sourceVertexEquiv x = B.sourceVertexEquiv (A.sourceVertexEquiv x) := rfl

theorem trans_sourceEdgeEquiv (A : GeometricDatumIso E₁ E₂) (B : GeometricDatumIso E₂ E₃)
    (x : E₁.SourceEdge) :
    (A.trans B).sourceEdgeEquiv x = B.sourceEdgeEquiv (A.sourceEdgeEquiv x) := rfl

theorem symm_sourceVertexEquiv (A : GeometricDatumIso E₁ E₂) (x : E₂.SourceVertex) :
    A.symm.sourceVertexEquiv x = A.sourceVertexEquiv.symm x := rfl

theorem symm_sourceEdgeEquiv (A : GeometricDatumIso E₁ E₂) (x : E₂.SourceEdge) :
    A.symm.sourceEdgeEquiv x = A.sourceEdgeEquiv.symm x := rfl

/-- **A property of target vertices that every edge preserves is constant** on a connected
target. -/
theorem iff_of_edges {S : CFGraph} (hS : graph_connected S) (P : S.V → Prop)
    (h : ∀ e : S.edges, (P (e : S.V × S.V).1 ↔ P (e : S.V × S.V).2)) (a b : S.V) :
    P a ↔ P b := by
  let H : SimpleGraph Prop := SimpleGraph.fromRel fun A B ↦ (A ↔ B)
  have hwalk : ∀ {A B : Prop}, H.Reachable A B → (A ↔ B) := by
    intro A B hAB
    obtain ⟨w⟩ := hAB
    induction w with
    | nil => exact Iff.rfl
    | cons hadj _ ih =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h' | h'
      · exact h'.trans ih
      · exact h'.symm.trans ih
  refine hwalk (reachable_of_targetEdges H P (fun e ↦ ?_) hS a b)
  by_cases hEq : P (e : S.V × S.V).1 = P (e : S.V × S.V).2
  · rw [hEq]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hEq, Or.inl (h e)⟩)

end Generic


/-! ## Un-refining an isomorphism -/

section Unrefine

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  {t : T.edges} {t' : T'.edges}

theorem mem_incidentEdges_iff_piece (t : T.edges) (v : T.V) (e : T.edges) :
    e ∈ GluingDatum.incidentEdges v ↔
      ∃ ε, parentT t ε = e ∧ ε ∈ GluingDatum.incidentEdges (subdivOld T t v) := by
  constructor
  · intro h
    refine ⟨pieceT t v e, parentT_pieceT _ _ _, ?_⟩
    rw [mem_incidentEdges_subdivOld, parentT_pieceT]
    exact ⟨h, rfl⟩
  · rintro ⟨ε, rfl, hε⟩
    exact ((mem_incidentEdges_subdivOld t v ε).mp hε).1

variable (Θ : GeometricDatumIso (refineDatum D t) (refineDatum D' t'))
  (hfresh : Θ.targetVertex (subdivFresh T t) = subdivFresh T' t')

include hfresh in
theorem symm_fresh : Θ.symm.targetVertex (subdivFresh T' t') = subdivFresh T t := by
  show Θ.targetVertex.symm _ = _
  rw [Equiv.symm_apply_eq, hfresh]

include hfresh in
theorem parentT_eq_iff_map (ε : (subdivTarget T t).edges) :
    parentT t' (Θ.targetEdge ε) = t' ↔ parentT t ε = t := by
  rw [← mem_incidentEdges_subdivFresh t' (Θ.targetEdge ε), ← mem_incidentEdges_subdivFresh t ε,
    ← hfresh]
  exact iso_mem_incidentEdges_iff Θ ε _

/-- The old target edge under the image of the first half of `e`. -/
def unrefineEdge (e : T.edges) : T'.edges := parentT t' (Θ.targetEdge (subdivOcc T t (some e)))

include hfresh in
theorem parentT_map (ε : (subdivTarget T t).edges) :
    parentT t' (Θ.targetEdge ε) = unrefineEdge Θ (parentT t ε) := by
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  cases o with
  | none =>
    rw [parentT_none]
    unfold unrefineEdge
    rw [(parentT_eq_iff_map Θ hfresh _).mpr (parentT_none t),
      (parentT_eq_iff_map Θ hfresh _).mpr (parentT_some t t)]
  | some e => rw [parentT_some]; rfl

include hfresh in
theorem unrefineEdge_symm (e : T.edges) :
    unrefineEdge Θ.symm (unrefineEdge Θ e) = e := by
  have h := parentT_map Θ.symm (symm_fresh Θ hfresh) (Θ.targetEdge (subdivOcc T t (some e)))
  have h' : Θ.symm.targetEdge (Θ.targetEdge (subdivOcc T t (some e))) = subdivOcc T t (some e) :=
    Θ.targetEdge.symm_apply_apply _
  rw [h', parentT_some] at h
  exact h.symm

/-- The target edges of the un-refined isomorphism. -/
def unrefineEdgeEquiv : T.edges ≃ T'.edges where
  toFun := unrefineEdge Θ
  invFun := unrefineEdge Θ.symm
  left_inv := unrefineEdge_symm Θ hfresh
  right_inv e := by
    have := unrefineEdge_symm Θ.symm (symm_fresh Θ hfresh) e
    exact this

include hfresh in
theorem exists_subdivOld (v : T.V) : ∃ w, Θ.targetVertex (subdivOld T t v) = subdivOld T' t' w := by
  rcases h : Θ.targetVertex (subdivOld T t v) with w | ⟨⟩
  · exact ⟨w, rfl⟩
  · exfalso
    have h2 : Θ.targetVertex (subdivOld T t v) = Θ.targetVertex (subdivFresh T t) := by
      rw [h, hfresh]; rfl
    exact subdivFresh_ne_subdivOld T t v (Θ.targetVertex.injective h2).symm

/-- The target vertices of the un-refined isomorphism. -/
def unrefineVertex : T.V ≃ T'.V :=
  equivOfRange Θ.targetVertex (subdivOld T t) (subdivOld T' t') (subdivOld_injective T t)
    (subdivOld_injective T' t') (exists_subdivOld Θ hfresh)
    (exists_subdivOld Θ.symm (symm_fresh Θ hfresh))

theorem unrefineVertex_spec (v : T.V) :
    Θ.targetVertex (subdivOld T t v) = subdivOld T' t' (unrefineVertex Θ hfresh v) :=
  equivOfRange_spec _ _ _ _ _ _ _ v

theorem unrefine_incident_iff (e : T.edges) (v : T.V) :
    unrefineEdgeEquiv Θ hfresh e ∈ GluingDatum.incidentEdges (unrefineVertex Θ hfresh v) ↔
      e ∈ GluingDatum.incidentEdges v := by
  rw [mem_incidentEdges_iff_piece t' (unrefineVertex Θ hfresh v),
    mem_incidentEdges_iff_piece t v]
  constructor
  · rintro ⟨ε', hε', hinc⟩
    refine ⟨Θ.targetEdge.symm ε', ?_, ?_⟩
    · apply (unrefineEdgeEquiv Θ hfresh).injective
      show unrefineEdge Θ _ = unrefineEdge Θ e
      rw [← parentT_map Θ hfresh, Equiv.apply_symm_apply]
      exact hε'
    · rw [← iso_mem_incidentEdges_iff Θ, Equiv.apply_symm_apply, unrefineVertex_spec]
      exact hinc
  · rintro ⟨ε, rfl, hinc⟩
    refine ⟨Θ.targetEdge ε, (parentT_map Θ hfresh ε), ?_⟩
    rw [← unrefineVertex_spec, iso_mem_incidentEdges_iff]
    exact hinc

theorem unrefine_vertexPartition (v : T.V) :
    D'.vertexPartition (unrefineVertex Θ hfresh v) =
      (D.vertexPartition v).relabel (Θ.vertexPerm (subdivOld T t v)) := by
  have h := Θ.vertexPartition (subdivOld T t v)
  rw [unrefineVertex_spec Θ hfresh] at h
  exact h

theorem unrefine_edgePartition (e : T.edges) :
    D'.edgePartition (unrefineEdgeEquiv Θ hfresh e) =
      (D.edgePartition e).relabel (Θ.edgePerm (subdivOcc T t (some e))) := by
  have h := Θ.edgePartition (subdivOcc T t (some e))
  rw [refineDatum_edgePartition, refineDatum_edgePartition_some] at h
  exact h

include hfresh in
/-- The images of two pieces of one old edge, in one sheet, lie in one block of its image. -/
theorem rel_edgePerm_of_parentT_eq {ε₁ ε₂ : (subdivTarget T t).edges}
    (h : parentT t ε₁ = parentT t ε₂) (i : Fin d) :
    (D'.edgePartition (unrefineEdge Θ (parentT t ε₁))).Rel (Θ.edgePerm ε₁ i)
      (Θ.edgePerm ε₂ i) := by
  by_cases h12 : ε₁ = ε₂
  · subst h12; rfl
  -- two different pieces of one edge are the two halves of `t`
  have ht : parentT t ε₁ = t := by
    rcases (parentT_eq_iff t ε₁ _).mp rfl with h1 | ⟨h1t, -⟩
    · rcases (parentT_eq_iff t ε₂ _).mp h.symm with h2 | ⟨h2t, -⟩
      · exact absurd (h1.trans h2.symm) h12
      · exact h2t
    · exact h1t
  have ht₂ : parentT t ε₂ = t := h ▸ ht
  have hinc₁ := (mem_incidentEdges_subdivFresh t ε₁).mpr ht
  have hinc₂ := (mem_incidentEdges_subdivFresh t ε₂).mpr ht₂
  rw [mem_incidentEdges_iff] at hinc₁ hinc₂
  have c₁ := Θ.compatible ε₁ _ hinc₁ i
  have c₂ := Θ.compatible ε₂ _ hinc₂ i
  -- in the old block at the fresh vertex, then relabelled
  have hrel : ((refineDatum D t).vertexPartition (subdivFresh T t)).Rel
      ((Θ.vertexPerm (subdivFresh T t)).symm (Θ.edgePerm ε₁ i))
      ((Θ.vertexPerm (subdivFresh T t)).symm (Θ.edgePerm ε₂ i)) := c₁.trans c₂.symm
  have hrel' := (((refineDatum D t).vertexPartition (subdivFresh T t)).relabel_rel_iff
    (Θ.vertexPerm (subdivFresh T t)) _ _).mpr hrel
  simp only [Equiv.apply_symm_apply] at hrel'
  rw [← Θ.vertexPartition, hfresh] at hrel'
  have hU : unrefineEdge Θ (parentT t ε₁) = t' := by
    rw [← parentT_map Θ hfresh]
    exact (parentT_eq_iff_map Θ hfresh ε₁).mpr ht
  rw [hU]
  exact hrel'

include hfresh in
theorem unrefine_compatible (e : T.edges) (v : T.V)
    (hv : (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v) (i : Fin d) :
    (D.vertexPartition v).Rel ((Θ.vertexPerm (subdivOld T t v)).symm
      (Θ.edgePerm (subdivOcc T t (some e)) i)) i := by
  set ε := pieceT t v e with hεdef
  have hε : ε ∈ GluingDatum.incidentEdges (subdivOld T t v) := by
    rw [mem_incidentEdges_subdivOld, parentT_pieceT]
    exact ⟨(mem_incidentEdges_iff v e).mpr hv, rfl⟩
  have c := Θ.compatible ε (subdivOld T t v) ((mem_incidentEdges_iff _ _).mp hε) i
  -- the image of the first half and of the piece at `v` are related at the image of `v`
  have hpar : parentT t (subdivOcc T t (some e)) = parentT t ε := by
    rw [parentT_some, parentT_pieceT]
  have hE := rel_edgePerm_of_parentT_eq Θ hfresh hpar i
  rw [parentT_some] at hE
  have hinc : unrefineEdgeEquiv Θ hfresh e ∈
      GluingDatum.incidentEdges (unrefineVertex Θ hfresh v) :=
    (unrefine_incident_iff Θ hfresh e v).mpr ((mem_incidentEdges_iff v e).mpr hv)
  rw [mem_incidentEdges_iff] at hinc
  have hV : (D'.vertexPartition (unrefineVertex Θ hfresh v)).Rel
      (Θ.edgePerm (subdivOcc T t (some e)) i) (Θ.edgePerm ε i) := by
    rcases hinc with h | h
    · rw [← h]; exact D'.refines_left _ _ _ hE
    · rw [← h]; exact D'.refines_right _ _ _ hE
  rw [unrefine_vertexPartition Θ hfresh] at hV
  have hV' := ((D.vertexPartition v).relabel_rel_iff (Θ.vertexPerm (subdivOld T t v))
    ((Θ.vertexPerm (subdivOld T t v)).symm (Θ.edgePerm (subdivOcc T t (some e)) i))
    ((Θ.vertexPerm (subdivOld T t v)).symm (Θ.edgePerm ε i))).mp (by
      simp only [Equiv.apply_symm_apply]; exact hV)
  exact hV'.trans c

/-- **The un-refined isomorphism** `D ≅ D'`. -/
def unrefine : GeometricDatumIso D D' where
  targetVertex := unrefineVertex Θ hfresh
  targetEdge := unrefineEdgeEquiv Θ hfresh
  ends e := unorderedEnds_of_incident _ _ _ (fst_ne_snd e) fun v ↦ by
    rw [← mem_incidentEdges_iff, ← mem_incidentEdges_iff]
    exact unrefine_incident_iff Θ hfresh e v
  vertexPerm v := Θ.vertexPerm (subdivOld T t v)
  edgePerm e := Θ.edgePerm (subdivOcc T t (some e))
  vertexPartition := unrefine_vertexPartition Θ hfresh
  edgePartition := unrefine_edgePartition Θ hfresh
  compatible := unrefine_compatible Θ hfresh

theorem unrefine_targetVertex (v : T.V) :
    Θ.targetVertex (subdivOld T t v) = subdivOld T' t' ((unrefine Θ hfresh).targetVertex v) :=
  unrefineVertex_spec Θ hfresh v

theorem unrefine_oldSV (x : D.SourceVertex) :
    Θ.sourceVertexEquiv (Refine.oldSV D t x) =
      Refine.oldSV D' t' ((unrefine Θ hfresh).sourceVertexEquiv x) :=
  Subtype.ext (Prod.ext (unrefineVertex_spec Θ hfresh x.1.1) rfl)

theorem unrefine_parentSE (y : (refineDatum D t).SourceEdge) :
    Refine.parentSE D' t' (Θ.sourceEdgeEquiv y) =
      (unrefine Θ hfresh).sourceEdgeEquiv (Refine.parentSE D t y) := by
  apply Subtype.ext
  apply Prod.ext (parentT_map Θ hfresh y.1.1)
  -- two representatives of one block
  show Θ.edgePerm y.1.1 y.1.2 = Θ.edgePerm (subdivOcc T t (some (parentT t y.1.1))) y.1.2
  have hpar : parentT t y.1.1 = parentT t (subdivOcc T t (some (parentT t y.1.1))) := by
    rw [parentT_some]
  have hrel := rel_edgePerm_of_parentT_eq Θ hfresh hpar y.1.2
  have h₁ : (D'.edgePartition (unrefineEdge Θ (parentT t y.1.1))).repr
      (Θ.edgePerm y.1.1 y.1.2) = Θ.edgePerm y.1.1 y.1.2 := by
    have := (Θ.sourceEdgeEquiv y).2
    rw [sourceEdgeEquiv_val, refineDatum_edgePartition, parentT_map Θ hfresh] at this
    exact this
  have h₂ : (D'.edgePartition (unrefineEdge Θ (parentT t y.1.1))).repr
      (Θ.edgePerm (subdivOcc T t (some (parentT t y.1.1))) y.1.2) =
        Θ.edgePerm (subdivOcc T t (some (parentT t y.1.1))) y.1.2 :=
    ((unrefine Θ hfresh).sourceEdgeEquiv (Refine.parentSE D t y)).2
  exact eq_of_rel_of_repr hrel h₁ h₂

end Unrefine

/-! ## Restricting an isomorphism of glued data to the old sheets -/

section Restrict

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  {π : Placement T d} {π' : Placement T' d}
  (Ψ : GeometricDatumIso (glueDatum D π) (glueDatum D' π'))

/-- **Over an edge of `T₃`, the new sheet goes where it goes at either end**: by compatibility,
since the new sheet is a singleton block at every vertex of `T₃`. -/
theorem edgePerm_last_eq (e : π.T₃.edges) (v : π.T₃.V)
    (hv : (e : π.T₃.V × π.T₃.V).1 = v ∨ (e : π.T₃.V × π.T₃.V).2 = v) :
    Ψ.edgePerm (π.liftE₃ e) (Fin.last d) = Ψ.vertexPerm (π.lift₃ v) (Fin.last d) := by
  have hv' : ((π.liftE₃ e : π.T₆.edges) : π.T₆.V × π.T₆.V).1 = π.lift₃ v ∨
      ((π.liftE₃ e : π.T₆.edges) : π.T₆.V × π.T₆.V).2 = π.lift₃ v := by
    rw [π.liftE₃_ends]
    rcases hv with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have c := Ψ.compatible (π.liftE₃ e) (π.lift₃ v) hv' (Fin.last d)
  rw [glueDatum_vertexPartition_lift₃] at c
  have c' := (extendNew_rel_last_iff _ _).mp c.symm
  rw [Equiv.symm_apply_eq] at c'
  exact c'

theorem vertexPerm_last_iff (e : π.T₃.edges) :
    (Ψ.vertexPerm (π.lift₃ (e : π.T₃.V × π.T₃.V).1) (Fin.last d) = Fin.last d ↔
      Ψ.vertexPerm (π.lift₃ (e : π.T₃.V × π.T₃.V).2) (Fin.last d) = Fin.last d) := by
  rw [← edgePerm_last_eq Ψ e _ (Or.inl rfl), ← edgePerm_last_eq Ψ e _ (Or.inr rfl)]

/-- A source vertex in the new sheet lies over `T₃`: at a tip the new sheet is glued to the sheet
of the mark, which represents the block. -/
theorem exists_lift₃_of_last (c : (glueDatum D π).SourceVertex) (hc : c.1.2 = Fin.last d) :
    ∃ v, c.1.1 = π.lift₃ v := by
  rcases π.T₆_vertex_cases c.1.1 with ⟨v, hv⟩ | ⟨k, hk⟩
  · exact ⟨v, hv⟩
  · exfalso
    have h := c.2
    rw [hk, glueDatum_vertexPartition_tipTarget, hc] at h
    simp [SheetOps.pair] at h

/-- **The new sheet goes to the new sheet** over all of `T₃`, once it does at one vertex. -/
theorem vertexPerm_last (hT : graph_connected T) (c : (glueDatum D π).SourceVertex)
    (hc : c.1.2 = Fin.last d) (hc' : (Ψ.sourceVertexEquiv c).1.2 = Fin.last d)
    (v : π.T₃.V) : Ψ.vertexPerm (π.lift₃ v) (Fin.last d) = Fin.last d := by
  obtain ⟨v₀, hv₀⟩ := exists_lift₃_of_last c hc
  have h₀ : Ψ.vertexPerm (π.lift₃ v₀) (Fin.last d) = Fin.last d := by
    rw [sourceVertexEquiv_val, hv₀, hc] at hc'
    exact hc'
  exact (iff_of_edges (π.T₃_connected hT)
    (fun v ↦ Ψ.vertexPerm (π.lift₃ v) (Fin.last d) = Fin.last d)
    (vertexPerm_last_iff Ψ) v₀ v).mp h₀

variable (htip : ∀ k, Ψ.targetVertex (π.tipTarget k) = π'.tipTarget k)
  (harm : ∀ k, Ψ.targetEdge (π.armEdge k) = π'.armEdge k)
  (hnew : ∀ v, Ψ.vertexPerm (π.lift₃ v) (Fin.last d) = Fin.last d)

include htip in
theorem exists_lift₃_map (v : π.T₃.V) : ∃ w, Ψ.targetVertex (π.lift₃ v) = π'.lift₃ w := by
  rcases π'.T₆_vertex_cases (Ψ.targetVertex (π.lift₃ v)) with ⟨w, h⟩ | ⟨k, h⟩
  · exact ⟨w, h⟩
  · exfalso
    rw [← htip k] at h
    exact π.lift₃_ne_tipTarget v k (Ψ.targetVertex.injective h)

include htip in
theorem exists_lift₃_map_symm (w : π'.T₃.V) :
    ∃ v, Ψ.targetVertex.symm (π'.lift₃ w) = π.lift₃ v := by
  rcases π.T₆_vertex_cases (Ψ.targetVertex.symm (π'.lift₃ w)) with ⟨v, h⟩ | ⟨k, h⟩
  · exact ⟨v, h⟩
  · exfalso
    rw [Equiv.symm_apply_eq, htip k] at h
    exact π'.lift₃_ne_tipTarget w k h

include harm in
theorem exists_liftE₃_map (e : π.T₃.edges) : ∃ e', Ψ.targetEdge (π.liftE₃ e) = π'.liftE₃ e' := by
  rcases π'.T₆_edge_cases (Ψ.targetEdge (π.liftE₃ e)) with ⟨e', h⟩ | ⟨k, h⟩
  · exact ⟨e', h⟩
  · exfalso
    rw [← harm k] at h
    exact π.liftE₃_ne_armEdge e k (Ψ.targetEdge.injective h)

include harm in
theorem exists_liftE₃_map_symm (e' : π'.T₃.edges) :
    ∃ e, Ψ.targetEdge.symm (π'.liftE₃ e') = π.liftE₃ e := by
  rcases π.T₆_edge_cases (Ψ.targetEdge.symm (π'.liftE₃ e')) with ⟨e, h⟩ | ⟨k, h⟩
  · exact ⟨e, h⟩
  · exfalso
    rw [Equiv.symm_apply_eq, harm k] at h
    exact π'.liftE₃_ne_armEdge e' k h

/-- The restricted vertex map `T₃ ≃ T₃'`. -/
def restrictVertex : π.T₃.V ≃ π'.T₃.V :=
  equivOfRange Ψ.targetVertex π.lift₃ π'.lift₃ π.lift₃_injective π'.lift₃_injective
    (exists_lift₃_map Ψ htip) (exists_lift₃_map_symm Ψ htip)

theorem restrictVertex_spec (v : π.T₃.V) :
    Ψ.targetVertex (π.lift₃ v) = π'.lift₃ (restrictVertex Ψ htip v) :=
  equivOfRange_spec _ _ _ _ _ _ _ v

/-- The restricted edge map `E(T₃) ≃ E(T₃')`. -/
def restrictEdge : π.T₃.edges ≃ π'.T₃.edges :=
  equivOfRange Ψ.targetEdge π.liftE₃ π'.liftE₃ π.liftE₃_injective π'.liftE₃_injective
    (exists_liftE₃_map Ψ harm) (exists_liftE₃_map_symm Ψ harm)

theorem restrictEdge_spec (e : π.T₃.edges) :
    Ψ.targetEdge (π.liftE₃ e) = π'.liftE₃ (restrictEdge Ψ harm e) :=
  equivOfRange_spec _ _ _ _ _ _ _ e

include hnew in
theorem edgePerm_last (e : π.T₃.edges) : Ψ.edgePerm (π.liftE₃ e) (Fin.last d) = Fin.last d := by
  rw [edgePerm_last_eq Ψ e _ (Or.inl rfl), hnew]

theorem restrict_ends (e : π.T₃.edges) :
    UnorderedEnds (restrictVertex Ψ htip) (e : π.T₃.V × π.T₃.V)
      (restrictEdge Ψ harm e : π'.T₃.V × π'.T₃.V) := by
  have h := Ψ.ends (π.liftE₃ e)
  have h1 := π.liftE₃_ends e
  have h2 := π'.liftE₃_ends (restrictEdge Ψ harm e)
  rw [restrictEdge_spec Ψ harm, h1, h2] at h
  have hv := fun v ↦ restrictVertex_spec Ψ htip v
  rcases h with h | h
  · have ha : π'.lift₃ (restrictEdge Ψ harm e : π'.T₃.V × π'.T₃.V).1 =
        Ψ.targetVertex (π.lift₃ (e : π.T₃.V × π.T₃.V).1) := congrArg Prod.fst h
    have hb : π'.lift₃ (restrictEdge Ψ harm e : π'.T₃.V × π'.T₃.V).2 =
        Ψ.targetVertex (π.lift₃ (e : π.T₃.V × π.T₃.V).2) := congrArg Prod.snd h
    rw [hv] at ha hb
    exact Or.inl (Prod.ext (π'.lift₃_injective ha) (π'.lift₃_injective hb))
  · have ha : π'.lift₃ (restrictEdge Ψ harm e : π'.T₃.V × π'.T₃.V).1 =
        Ψ.targetVertex (π.lift₃ (e : π.T₃.V × π.T₃.V).2) := congrArg Prod.fst h
    have hb : π'.lift₃ (restrictEdge Ψ harm e : π'.T₃.V × π'.T₃.V).2 =
        Ψ.targetVertex (π.lift₃ (e : π.T₃.V × π.T₃.V).1) := congrArg Prod.snd h
    rw [hv] at ha hb
    exact Or.inr (Prod.ext (π'.lift₃_injective ha) (π'.lift₃_injective hb))

/-- **The restriction to the old sheets over `T₃`.** -/
def restrict₃ : GeometricDatumIso (refine₃ D π) (refine₃ D' π') where
  targetVertex := restrictVertex Ψ htip
  targetEdge := restrictEdge Ψ harm
  ends := restrict_ends Ψ htip harm
  vertexPerm v := restrictPerm (Ψ.vertexPerm (π.lift₃ v)) (hnew v)
  edgePerm e := restrictPerm (Ψ.edgePerm (π.liftE₃ e)) (edgePerm_last Ψ hnew e)
  vertexPartition v := by
    have h := Ψ.vertexPartition (π.lift₃ v)
    rw [restrictVertex_spec Ψ htip, glueDatum_vertexPartition_lift₃,
      glueDatum_vertexPartition_lift₃, extendNew_relabel _ _ (hnew v)] at h
    exact extendNew_injective h
  edgePartition e := by
    have h := Ψ.edgePartition (π.liftE₃ e)
    rw [restrictEdge_spec Ψ harm, glueDatum_edgePartition_liftE₃,
      glueDatum_edgePartition_liftE₃, extendNew_relabel _ _ (edgePerm_last Ψ hnew e)] at h
    exact extendNew_injective h
  compatible e v hv i := by
    have hv' : ((π.liftE₃ e : π.T₆.edges) : π.T₆.V × π.T₆.V).1 = π.lift₃ v ∨
        ((π.liftE₃ e : π.T₆.edges) : π.T₆.V × π.T₆.V).2 = π.lift₃ v := by
      rw [π.liftE₃_ends]
      rcases hv with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    have c := Ψ.compatible (π.liftE₃ e) (π.lift₃ v) hv' i.castSucc
    rw [glueDatum_vertexPartition_lift₃,
      ← castSucc_restrictPerm (Ψ.edgePerm (π.liftE₃ e)) (edgePerm_last Ψ hnew e),
      ← castSucc_restrictPerm_symm (Ψ.vertexPerm (π.lift₃ v)) (hnew v)] at c
    obtain ⟨i', hi', hrel⟩ := (extendNew_rel_castSucc_iff _ _ _).mp c
    rw [Fin.castSucc_inj] at hi'
    subst hi'
    exact hrel

theorem restrict₃_lift₃ (v : π.T₃.V) :
    Ψ.targetVertex (π.lift₃ v) = π'.lift₃ ((restrict₃ Ψ htip harm hnew).targetVertex v) :=
  restrictVertex_spec Ψ htip v

theorem restrict₃_oldVertex₃ (x : (refine₃ D π).SourceVertex) :
    Ψ.sourceVertexEquiv (oldVertex₃ D π x) =
      oldVertex₃ D' π' ((restrict₃ Ψ htip harm hnew).sourceVertexEquiv x) := by
  apply Subtype.ext
  rw [sourceVertexEquiv_val, oldVertex₃_val, oldVertex₃_val, sourceVertexEquiv_val]
  refine Prod.ext (restrictVertex_spec Ψ htip _) ?_
  exact (castSucc_restrictPerm _ (hnew _) _).symm

theorem restrict₃_liftSE (y : (refine₃ D π).SourceEdge) :
    Ψ.sourceEdgeEquiv (liftSE D π y) =
      liftSE D' π' ((restrict₃ Ψ htip harm hnew).sourceEdgeEquiv y) := by
  apply Subtype.ext
  rw [sourceEdgeEquiv_val]
  refine Prod.ext (restrictEdge_spec Ψ harm _) ?_
  exact (castSucc_restrictPerm _ (edgePerm_last Ψ hnew _) _).symm

end Restrict

/-! ## Un-refining at the three marks -/

section Unrefine₃

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  {π : Placement T d} {π' : Placement T' d}

/-- An old source vertex of `D`, in `refine₃ D π`. -/
def oldSV₃ (D : GluingDatum T d) (π : Placement T d) (x : D.SourceVertex) :
    (refine₃ D π).SourceVertex :=
  Refine.oldSV _ π.edge₂ (Refine.oldSV _ π.edge₁ (Refine.oldSV D π.edge₀ x))

/-- The old source edge of `D` under a source edge of `refine₃ D π`. -/
def parentSE₃ (D : GluingDatum T d) (π : Placement T d) (y : (refine₃ D π).SourceEdge) :
    D.SourceEdge :=
  Refine.parentSE D π.edge₀ (Refine.parentSE _ π.edge₁ (Refine.parentSE _ π.edge₂ y))

/-- **Un-refining at the three marks**: an isomorphism of the refined data carrying each mark
image to the same mark image descends to `D ≅ D'`. -/
theorem exists_unrefine₃ (Θ : GeometricDatumIso (refine₃ D π) (refine₃ D' π'))
    (hmark : ∀ k, Θ.targetVertex (π.markVertex₃ k) = π'.markVertex₃ k) :
    ∃ R : GeometricDatumIso D D',
      (∀ x, Θ.sourceVertexEquiv (oldSV₃ D π x) = oldSV₃ D' π' (R.sourceVertexEquiv x)) ∧
      (∀ y, parentSE₃ D' π' (Θ.sourceEdgeEquiv y) = R.sourceEdgeEquiv (parentSE₃ D π y)) := by
  have h₂ : Θ.targetVertex (subdivFresh π.T₂ π.edge₂) = subdivFresh π'.T₂ π'.edge₂ := hmark 2
  set R₂ := unrefine Θ h₂ with hR₂
  have h₁ : R₂.targetVertex (subdivFresh π.T₁ π.edge₁) = subdivFresh π'.T₁ π'.edge₁ := by
    have h := hmark 1
    change Θ.targetVertex (subdivOld _ _ (subdivFresh π.T₁ π.edge₁)) =
      subdivOld _ _ (subdivFresh π'.T₁ π'.edge₁) at h
    rw [unrefine_targetVertex Θ h₂] at h
    exact subdivOld_injective _ _ h
  set R₁ := unrefine R₂ h₁ with hR₁
  have h₀ : R₁.targetVertex (subdivFresh T π.edge₀) = subdivFresh T' π'.edge₀ := by
    have h := hmark 0
    change Θ.targetVertex (subdivOld _ _ (subdivOld _ _ (subdivFresh T π.edge₀))) =
      subdivOld _ _ (subdivOld _ _ (subdivFresh T' π'.edge₀)) at h
    rw [unrefine_targetVertex Θ h₂, unrefine_targetVertex R₂ h₁] at h
    exact subdivOld_injective _ _ (subdivOld_injective _ _ h)
  refine ⟨unrefine R₁ h₀, fun x ↦ ?_, fun y ↦ ?_⟩
  · unfold oldSV₃
    rw [unrefine_oldSV Θ h₂, unrefine_oldSV R₂ h₁, unrefine_oldSV R₁ h₀]
  · unfold parentSE₃
    rw [unrefine_parentSE Θ h₂, unrefine_parentSE R₂ h₁, unrefine_parentSE R₁ h₀]

end Unrefine₃

end GenusSixExistence.Tripod.Gluing

end
