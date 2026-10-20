module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropRows
public import DraismaVargasMarkedCount.MarkedCountGeneral.DenomRow

@[expose] public section

/-!
# The denominator step of the drop, part 3: indices and jumps under the contraction

For a contraction
site `S` (modules `DropContract`, `DropRows`):

* `sourceEdgeIndex_edgeMap`: the edge map keeps indices (an occurrence over `c` goes to its
  partner, which has its index, `sourceEdgeIndex_partner`);
* `sourceEdgeIndex_fo`: the two occurrences at `V` have one index;
* `ndMap_fc`: they have one image;
* `not_over_x_of_isJump`: no jump lies over `x` (at a vertex over `x` both occurrences have the
  index of the block, `x` being divalent of change zero);
* `isJump_vmap`: a jump of a marked row goes to a jump of its image row.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount

namespace DivalentContraction

namespace Site

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
variable (S : Site data)

/-- **The edge map keeps indices.** -/
theorem sourceEdgeIndex_edgeMap (e : data.SourceEdge) :
    S.D.sourceEdgeIndex (S.edgeMap e) = data.sourceEdgeIndex e := by
  unfold edgeMap
  rw [ContractionFibre.sourceEdgeIndex_sourceEdgeMap data (contracted := S.c) rfl
    (fst_ne_snd S.c) S.hOne (S.mu e)]
  by_cases h : e.1.1 = S.c
  · rw [S.mu_of_eq h]
    exact S.sourceEdgeIndex_partner h
  · rw [S.mu_of_ne h]

/-- The two occurrences through a sheet at `x` have one index. -/
theorem sourceEdgeIndex_other_eq (i : Fin degree) :
    data.sourceEdgeIndex (data.sourceEdge S.other i) = data.sourceEdgeIndex (data.sourceEdge S.c i) := by
  rw [← S.partner_sourceEdge_c]
  exact S.sourceEdgeIndex_partner (GluingDatum.sourceEdge_target data S.c i)

/-- At a source vertex over `x`, all occurrences have one index. -/
theorem sourceEdgeIndex_eq_of_over_x {X : data.SourceVertex} (hX : X.1.1 = S.x)
    {e f : data.SourceEdge} (he : Incident data e X) (hf : Incident data f X) :
    data.sourceEdgeIndex e = data.sourceEdgeIndex f := by
  rcases (S.incident_x_iff X hX e).mp he with rfl | rfl <;>
    rcases (S.incident_x_iff X hX f).mp hf with rfl | rfl
  · rfl
  · exact (S.sourceEdgeIndex_other_eq _).symm
  · exact S.sourceEdgeIndex_other_eq _
  · rfl

variable {M : Finset data.SourceVertex} {V : data.SourceVertex} {M' : Finset S.D.SourceVertex}

/-- The two occurrences at `V` have one index. -/
theorem sourceEdgeIndex_fo (hM : S.MarkHyp M V M') :
    data.sourceEdgeIndex (S.fo hM).1 = data.sourceEdgeIndex (S.fc hM).1 :=
  S.sourceEdgeIndex_eq_of_over_x hM.onX (S.incident_fo hM) (S.incident_fc hM)

/-- The two occurrences at `V` have one image. -/
theorem ndMap_fc (hM : S.MarkHyp M V M') : S.ndMap (S.fc hM) = S.ndMap (S.fo hM) :=
  Subtype.ext (S.edgeMap_eq_of_incident_x hM.onX (S.incident_fc hM) (S.incident_fo hM))

/-- **The image of a row through `V`** is the merged row. -/
theorem rowMap_eq_fc_iff (hM : S.MarkHyp M V M') (r : MarkedStablePath data M) :
    S.rowMap hM r = S.rowMap hM (markedRow M (S.fc hM)) ↔
      r = markedRow M (S.fc hM) ∨ r = markedRow M (S.fo hM) := by
  rw [S.rowMap_eq_iff hM]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact h
  · intro h
    exact Or.inr ⟨h, Or.inl rfl⟩

/-- **No jump lies over `x`.** -/
theorem not_over_x_of_isJump {P : MarkedStablePath data M} {Y : data.SourceVertex}
    (hJ : IsJump data M P Y) : Y.1.1 ≠ S.x := by
  intro hY
  obtain ⟨-, -, F, G, -, hF, hG, hne⟩ := hJ
  exact hne (S.sourceEdgeIndex_eq_of_over_x hY hF hG)

/-- **A jump goes to a jump of the image row.** -/
theorem isJump_vmap (hM : S.MarkHyp M V M') {P : MarkedStablePath data M}
    {Y : data.SourceVertex} (hJ : IsJump data M P Y) :
    IsJump S.D M' (S.rowMap hM P) (S.vmap Y) := by
  have hYx := S.not_over_x_of_isJump hJ
  obtain ⟨hYm, hY2, F, G, rfl, hF, hG, hne⟩ := hJ
  refine ⟨fun h ↦ hYm ((hM.marks Y hYx).mp h), ?_, S.ndMap F, S.ndMap G, rfl,
    S.incident_edgeMap hYx hF, S.incident_edgeMap hYx hG, ?_⟩
  · rw [S.nonDanglingValency_vmap hYx]; exact hY2
  · rw [ndMap_val, ndMap_val, S.sourceEdgeIndex_edgeMap, S.sourceEdgeIndex_edgeMap]
    exact hne

end Site

end DivalentContraction

end DraismaVargas.Count.MarkedCountGeneral
