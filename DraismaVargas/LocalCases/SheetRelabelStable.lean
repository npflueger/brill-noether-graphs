import DraismaVargas.LocalCases.SheetRelabelPruning
import DraismaVargas.LocalCases.StableSourceMatrix

/-!
# Actual stable-row and matrix transport under sheet relabelling

The source's compatible labellings use the graph isomorphism induced by
sheet relabelling (Draisma--Vargas Part I, the compatible labellings of the
subsection on inherited properties). Pruning and incidence transport
give the complete surviving-star census and preserve the consecutive
relation. `Quot.congr` then descends the literal edge equivalence, rather
than choosing a bijection from a row count. Transporting each row-filtered
occurrence set and its indices proves equality of every natural column.
-/

namespace DraismaVargas.LocalCases.SheetRelabelStable

open DraismaVargas.Infrastructure W4StableSource SheetRelabelPruning
open StableSourceMatrix

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- The actual surviving source occurrences are transported by the edge
equivalence, with pruning proved rather than assumed. -/
noncomputable def nonDanglingEdgeEquiv (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) :
    NonDanglingEdge data ≃ NonDanglingEdge relabeling.apply :=
  relabeling.sourceEdgeEquiv.subtypeEquiv fun edge ↦
    not_congr (isDangling_sourceEdgeEquiv_iff relabeling hConnected edge).symm

theorem nonDanglingIncident_map (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (vertex : data.SourceVertex) :
    nonDanglingIncident relabeling.apply (relabeling.sourceVertexEquiv vertex) =
      (nonDanglingIncident data vertex).image relabeling.sourceEdgeEquiv := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := relabeling.sourceEdgeEquiv.surjective edge
  rw [mem_nonDanglingIncident, isDangling_sourceEdgeEquiv_iff relabeling hConnected,
    incident_sourceEdgeEquiv_iff]
  simp only [Finset.mem_image, Equiv.apply_eq_iff_eq, exists_eq_right,
    mem_nonDanglingIncident]

theorem nonDanglingValency_map (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (vertex : data.SourceVertex) :
    nonDanglingValency relabeling.apply (relabeling.sourceVertexEquiv vertex) =
      nonDanglingValency data vertex := by
  rw [← card_nonDanglingIncident, nonDanglingIncident_map relabeling hConnected,
    Finset.card_image_of_injective _ relabeling.sourceEdgeEquiv.injective,
    card_nonDanglingIncident]

theorem consecutive_map_iff (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (first second : NonDanglingEdge data) :
    Consecutive relabeling.apply
        (nonDanglingEdgeEquiv relabeling hConnected first)
        (nonDanglingEdgeEquiv relabeling hConnected second) ↔
      Consecutive data first second := by
  constructor
  · rintro ⟨hNe, vertex, hFirst, hSecond, hValency⟩
    obtain ⟨vertex, rfl⟩ := relabeling.sourceVertexEquiv.surjective vertex
    refine ⟨fun h ↦ hNe (congrArg (nonDanglingEdgeEquiv relabeling hConnected) h),
      vertex, ?_, ?_, ?_⟩
    · exact (incident_sourceEdgeEquiv_iff relabeling first.1 vertex).mp hFirst
    · exact (incident_sourceEdgeEquiv_iff relabeling second.1 vertex).mp hSecond
    · rwa [nonDanglingValency_map relabeling hConnected] at hValency
  · rintro ⟨hNe, vertex, hFirst, hSecond, hValency⟩
    refine ⟨(nonDanglingEdgeEquiv relabeling hConnected).injective.ne hNe,
      relabeling.sourceVertexEquiv vertex, ?_, ?_, ?_⟩
    · exact (incident_sourceEdgeEquiv_iff relabeling first.1 vertex).mpr hFirst
    · exact (incident_sourceEdgeEquiv_iff relabeling second.1 vertex).mpr hSecond
    · rwa [nonDanglingValency_map relabeling hConnected]

/-- The induced stable-row equivalence follows the literal source edge map. -/
noncomputable def stablePathEquiv (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) : StablePath data ≃ StablePath relabeling.apply :=
  Quot.congr (nonDanglingEdgeEquiv relabeling hConnected)
    fun first second ↦ (consecutive_map_iff relabeling hConnected first second).symm

theorem stablePathEquiv_mk (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (edge : NonDanglingEdge data) :
    stablePathEquiv relabeling hConnected edge.stablePath =
      (nonDanglingEdgeEquiv relabeling hConnected edge).stablePath := rfl

theorem sourceEdgeIndex_map (relabeling : data.SheetRelabeling)
    (edge : data.SourceEdge) :
    relabeling.apply.sourceEdgeIndex (relabeling.sourceEdgeEquiv edge) =
      data.sourceEdgeIndex edge :=
  (data.edgePartition edge.1.1).relabel_blockCard
    (relabeling.edgePermutation edge.1.1) edge.1.2

theorem danglingEdgeNoGlue_map (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hNoGlue : DanglingEdgeNoGlue data) :
    DanglingEdgeNoGlue relabeling.apply := by
  intro edge hDangling
  obtain ⟨edge, rfl⟩ := relabeling.sourceEdgeEquiv.surjective edge
  rw [sourceEdgeIndex_map]
  exact hNoGlue edge ((isDangling_sourceEdgeEquiv_iff relabeling hConnected edge).mp hDangling)

/-- Exact row-filtered occurrence transport under compatible sheet relabelling. -/
theorem occurrences_map (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (path : StablePath data) (place : target.edges) :
    occurrences relabeling.apply (stablePathEquiv relabeling hConnected path) place =
      (occurrences data path place).image relabeling.sourceEdgeEquiv := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := relabeling.sourceEdgeEquiv.surjective edge
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hOld : ¬ IsDangling data edge := fun h ↦ hSurvives
      ((isDangling_sourceEdgeEquiv_iff relabeling hConnected edge).mpr h)
    apply Finset.mem_image.mpr
    refine ⟨edge, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, hTarget⟩, rfl⟩
    apply (stablePathEquiv relabeling hConnected).injective
    exact (stablePathEquiv_mk relabeling hConnected ⟨edge, hOld⟩).trans hRow
  · intro hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    have hEq : old = edge := relabeling.sourceEdgeEquiv.injective hEqual
    subst old
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    have hNew : ¬ IsDangling relabeling.apply (relabeling.sourceEdgeEquiv edge) := fun h ↦
      hSurvives ((isDangling_sourceEdgeEquiv_iff relabeling hConnected edge).mp h)
    refine ⟨⟨hNew, ?_⟩, hTarget⟩
    exact (stablePathEquiv_mk relabeling hConnected ⟨edge, hSurvives⟩).symm.trans
      (congrArg (stablePathEquiv relabeling hConnected) hRow)

/-- All natural matrix columns agree in the induced stable-row coordinates. -/
theorem matrix_map (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (path : StablePath data) (place : target.edges) :
    matrix relabeling.apply (stablePathEquiv relabeling hConnected path) place =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_map, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [sourceEdgeIndex_map]
  · exact fun _ _ _ _ h ↦ relabeling.sourceEdgeEquiv.injective h

end DraismaVargas.LocalCases.SheetRelabelStable
