module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Sheets
public import DraismaVargas.LocalCases.DanglingDescent

@[expose] public section

/-!
# Isomorphisms carry lone sheets to lone sheets

For an isomorphism `Φ` of gluing data over a connected target, a sheet `i` is lone in the first
datum exactly when `Φ.vertexPerm v i` (or `Φ.edgePerm e i`) is lone in the second, for every
target vertex `v` (edge `e`) (`isLone_vertexPerm_iff`, `isLone_edgePerm_iff`). The relabelled
lone sheet does not depend on the vertex (`vertexPerm_eq_of_isLone`): the compatibility clause
pins it along every edge, and the target is connected.

This is what `Sheets.restrictSheetsIso` needs to restrict an isomorphism to the deletion of the
lone sheets.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.Sheets

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.Count (GeometricDatumIso)

variable {T₁ T₂ : CFGraph.{0}} {d : ℕ} {D₁ : GluingDatum T₁ d} {D₂ : GluingDatum T₂ d}
  (Φ : GeometricDatumIso D₁ D₂)

/-- The two ends of an edge occurrence `e` between `a` and `b`, from `0 < num_edges a b`. -/
theorem exists_edge_of_num_edges_pos {T : CFGraph.{0}} {a b : T.V} (hab : 0 < num_edges T a b) :
    ∃ e : T.edges, ((e : T.V × T.V).1 = a ∨ (e : T.V × T.V).2 = a) ∧
      ((e : T.V × T.V).1 = b ∨ (e : T.V × T.V).2 = b) := by
  obtain ⟨pair, hPair, hEnds⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos _ a b hab
  let e : T.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  refine ⟨e, ?_, ?_⟩
  · change pair.1 = a ∨ pair.2 = a
    rcases hEnds with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · change pair.1 = b ∨ pair.2 = b
    rcases hEnds with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- At an end of `e`, the edge relabelling of a lone sheet is its vertex relabelling. -/
theorem edgePerm_eq_of_isLone {i : Fin d} (hi : IsLone D₁ i) (e : T₁.edges) (v : T₁.V)
    (hv : (e : T₁.V × T₁.V).1 = v ∨ (e : T₁.V × T₁.V).2 = v) :
    Φ.edgePerm e i = Φ.vertexPerm v i := by
  have h := Φ.compatible e v hv i
  have h' : (Φ.vertexPerm v).symm (Φ.edgePerm e i) = i := hi v _ h.symm
  exact (Equiv.symm_apply_eq _).mp h'

/-- **The relabelled lone sheet does not depend on the vertex.** -/
theorem vertexPerm_eq_of_isLone (hT : graph_connected T₁) {i : Fin d} (hi : IsLone D₁ i)
    (v w : T₁.V) : Φ.vertexPerm w i = Φ.vertexPerm v i := by
  refine reach_propagate (motive := fun w ↦ Φ.vertexPerm w i = Φ.vertexPerm v i) rfl
    (fun a b hab ha ↦ ?_) (reach_of_graph_connected hT v w)
  obtain ⟨e, hea, heb⟩ := exists_edge_of_num_edges_pos hab
  rw [← edgePerm_eq_of_isLone Φ hi e b heb, edgePerm_eq_of_isLone Φ hi e a hea, ha]

/-- **A lone sheet relabels to a lone sheet.** -/
theorem isLone_vertexPerm (hT : graph_connected T₁) {i : Fin d} (hi : IsLone D₁ i) (v : T₁.V) :
    IsLone D₂ (Φ.vertexPerm v i) := by
  intro v' j hj
  obtain ⟨w, rfl⟩ := Φ.targetVertex.surjective v'
  rw [Φ.vertexPartition w, ← vertexPerm_eq_of_isLone Φ hT hi v w,
    ← Equiv.apply_symm_apply (Φ.vertexPerm w) j, SheetPartition.relabel_rel_iff] at hj
  rw [← vertexPerm_eq_of_isLone Φ hT hi v w, ← hi w _ hj, Equiv.apply_symm_apply]

/-- Pulled back along a relabelling, a lone sheet is alone in its block. -/
theorem single_of_isLone {i' : Fin d} (h : IsLone D₂ i') (w : T₁.V) (j : Fin d)
    (hj : (D₁.vertexPartition w).Rel ((Φ.vertexPerm w).symm i') j) :
    j = (Φ.vertexPerm w).symm i' := by
  have h2 : (D₂.vertexPartition (Φ.targetVertex w)).Rel i' (Φ.vertexPerm w j) := by
    rw [Φ.vertexPartition w, ← Equiv.apply_symm_apply (Φ.vertexPerm w) i',
      SheetPartition.relabel_rel_iff]
    simpa using hj
  have h3 := h _ _ h2
  rw [← h3, Equiv.symm_apply_apply]

/-- At an end of `e`, the pull-back of a lone sheet along `e` is its pull-back at the end. -/
theorem edgePerm_symm_eq {i' : Fin d} (h : IsLone D₂ i') (e : T₁.edges) (v : T₁.V)
    (hv : (e : T₁.V × T₁.V).1 = v ∨ (e : T₁.V × T₁.V).2 = v) :
    (Φ.edgePerm e).symm i' = (Φ.vertexPerm v).symm i' := by
  have hc := Φ.compatible e v hv ((Φ.edgePerm e).symm i')
  rw [Equiv.apply_symm_apply] at hc
  exact single_of_isLone Φ h v _ hc

/-- **A sheet relabelling to a lone sheet is lone.** -/
theorem isLone_of_vertexPerm (hT : graph_connected T₁) {i : Fin d} (v : T₁.V)
    (h : IsLone D₂ (Φ.vertexPerm v i)) : IsLone D₁ i := by
  have hConst : ∀ w, (Φ.vertexPerm w).symm (Φ.vertexPerm v i) = i := by
    intro w
    refine reach_propagate (motive := fun w ↦ (Φ.vertexPerm w).symm (Φ.vertexPerm v i) = i)
      (Equiv.symm_apply_apply _ _) (fun a b hab ha ↦ ?_) (reach_of_graph_connected hT v w)
    obtain ⟨e, hea, heb⟩ := exists_edge_of_num_edges_pos hab
    rw [← edgePerm_symm_eq Φ h e b heb, edgePerm_symm_eq Φ h e a hea, ha]
  intro w j hj
  rw [← hConst w] at hj ⊢
  exact single_of_isLone Φ h w j hj

theorem isLone_vertexPerm_iff (hT : graph_connected T₁) (v : T₁.V) (i : Fin d) :
    IsLone D₂ (Φ.vertexPerm v i) ↔ IsLone D₁ i :=
  ⟨isLone_of_vertexPerm Φ hT v, fun hi ↦ isLone_vertexPerm Φ hT hi v⟩

theorem isLone_edgePerm_iff (hT : graph_connected T₁) (e : T₁.edges) (i : Fin d) :
    IsLone D₂ (Φ.edgePerm e i) ↔ IsLone D₁ i := by
  constructor
  · intro h
    have hs := edgePerm_symm_eq Φ h e (e : T₁.V × T₁.V).1 (Or.inl rfl)
    rw [Equiv.symm_apply_apply] at hs
    refine isLone_of_vertexPerm Φ hT (e : T₁.V × T₁.V).1 ?_
    rw [show Φ.vertexPerm (e : T₁.V × T₁.V).1 i = Φ.edgePerm e i from
      ((Equiv.symm_apply_eq _).mp hs.symm).symm]
    exact h
  · intro hi
    rw [edgePerm_eq_of_isLone Φ hi e (e : T₁.V × T₁.V).1 (Or.inl rfl)]
    exact isLone_vertexPerm Φ hT hi _

end DraismaVargas.Count.MarkedCountGeneral.Sheets
