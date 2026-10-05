module

public import DraismaVargas.LocalCases.TargetRelabelPruning
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# Induced stable rows, matrix entries and branch flags under target relabelling

The compatible-labelling rule (Draisma--Vargas Part I, §5.2: labellings
compatible at a contracted edge) follows actual source occurrences, even when an
isomorphism reverses a stored edge orientation. The pruning equivalence descends
through consecutiveness to stable rows; the target columns follow
`GluingTransport.edgeEquiv`. Row-filtered occurrence and branch-flag bijections
give the natural matrix and incidence identities.
-/

namespace DraismaVargas.LocalCases.TargetRelabelStable

open Utilities DraismaVargas.Infrastructure GluingTransport
open W4StableSource TargetRelabelPruning StableSourceMatrix StableGraphIncidence

variable {G H : CFGraph} {degree : ℕ} (φ : CFGraphIso G H)
  (data : GluingDatum G degree)

noncomputable def nonDanglingEdgeEquiv (hConnected : data.Connected) :
    NonDanglingEdge data ≃ NonDanglingEdge (transport φ data) :=
  (sourceEdgeEquiv φ data).subtypeEquiv fun edge ↦
    not_congr (isDangling_sourceEdgeEquiv_iff φ data hConnected edge).symm

theorem nonDanglingIncident_map (hConnected : data.Connected) (vertex : data.SourceVertex) :
    nonDanglingIncident (transport φ data) (sourceVertexEquiv φ data vertex) =
      (nonDanglingIncident data vertex).image (sourceEdgeEquiv φ data) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := (sourceEdgeEquiv φ data).surjective edge
  rw [mem_nonDanglingIncident, isDangling_sourceEdgeEquiv_iff φ data hConnected,
    incident_sourceEdgeEquiv_iff]
  simp only [Finset.mem_image, Equiv.apply_eq_iff_eq, exists_eq_right,
    mem_nonDanglingIncident]

theorem nonDanglingValency_map (hConnected : data.Connected) (vertex : data.SourceVertex) :
    nonDanglingValency (transport φ data) (sourceVertexEquiv φ data vertex) =
      nonDanglingValency data vertex := by
  rw [← card_nonDanglingIncident, nonDanglingIncident_map φ data hConnected,
    Finset.card_image_of_injective _ (sourceEdgeEquiv φ data).injective,
    card_nonDanglingIncident]

theorem consecutive_map_iff (hConnected : data.Connected) (first second : NonDanglingEdge data) :
    Consecutive (transport φ data)
        (nonDanglingEdgeEquiv φ data hConnected first)
        (nonDanglingEdgeEquiv φ data hConnected second) ↔
      Consecutive data first second := by
  constructor
  · rintro ⟨hNe, vertex, hFirst, hSecond, hValency⟩
    obtain ⟨vertex, rfl⟩ := (sourceVertexEquiv φ data).surjective vertex
    refine ⟨fun h ↦ hNe (congrArg (nonDanglingEdgeEquiv φ data hConnected) h),
      vertex, ?_, ?_, ?_⟩
    · exact (incident_sourceEdgeEquiv_iff φ data first.1 vertex).mp hFirst
    · exact (incident_sourceEdgeEquiv_iff φ data second.1 vertex).mp hSecond
    · rwa [nonDanglingValency_map φ data hConnected] at hValency
  · rintro ⟨hNe, vertex, hFirst, hSecond, hValency⟩
    refine ⟨(nonDanglingEdgeEquiv φ data hConnected).injective.ne hNe,
      sourceVertexEquiv φ data vertex, ?_, ?_, ?_⟩
    · exact (incident_sourceEdgeEquiv_iff φ data first.1 vertex).mpr hFirst
    · exact (incident_sourceEdgeEquiv_iff φ data second.1 vertex).mpr hSecond
    · rwa [nonDanglingValency_map φ data hConnected]

/-- The quotient map is induced by the actual source occurrence map. -/
noncomputable def stablePathEquiv (hConnected : data.Connected) :
    StablePath data ≃ StablePath (transport φ data) :=
  Quot.congr (nonDanglingEdgeEquiv φ data hConnected)
    fun first second ↦ (consecutive_map_iff φ data hConnected first second).symm

theorem stablePathEquiv_mk (hConnected : data.Connected) (edge : NonDanglingEdge data) :
    stablePathEquiv φ data hConnected edge.stablePath =
      (nonDanglingEdgeEquiv φ data hConnected edge).stablePath := rfl

theorem danglingEdgeNoGlue_map (hConnected : data.Connected) (hNoGlue : DanglingEdgeNoGlue data) :
    DanglingEdgeNoGlue (transport φ data) := by
  intro edge hDangling
  obtain ⟨edge, rfl⟩ := (sourceEdgeEquiv φ data).surjective edge
  rw [sourceEdgeIndex_map]
  exact hNoGlue edge ((isDangling_sourceEdgeEquiv_iff φ data hConnected edge).mp hDangling)

theorem occurrences_map (hConnected : data.Connected) (path : StablePath data) (place : G.edges) :
    occurrences (transport φ data) (stablePathEquiv φ data hConnected path) (edgeEquiv φ place) =
      (occurrences data path place).image (sourceEdgeEquiv φ data) := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := (sourceEdgeEquiv φ data).surjective edge
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hOld : ¬ IsDangling data edge := fun h ↦ hSurvives
      ((isDangling_sourceEdgeEquiv_iff φ data hConnected edge).mpr h)
    have hOldTarget : edge.1.1 = place := (edgeEquiv φ).injective hTarget
    apply Finset.mem_image.mpr
    refine ⟨edge, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, hOldTarget⟩, rfl⟩
    apply (stablePathEquiv φ data hConnected).injective
    exact (stablePathEquiv_mk φ data hConnected ⟨edge, hOld⟩).trans hRow
  · intro hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    have hEq : old = edge := (sourceEdgeEquiv φ data).injective hEqual
    subst old
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    have hNew : ¬ IsDangling (transport φ data) (sourceEdgeEquiv φ data edge) := fun h ↦
      hSurvives ((isDangling_sourceEdgeEquiv_iff φ data hConnected edge).mp h)
    refine ⟨⟨hNew, ?_⟩, congrArg (edgeEquiv φ) hTarget⟩
    exact (stablePathEquiv_mk φ data hConnected ⟨edge, hSurvives⟩).symm.trans
      (congrArg (stablePathEquiv φ data hConnected) hRow)

/-- Every natural matrix entry agrees in the induced row and target coordinates. -/
theorem matrix_map (hConnected : data.Connected) (path : StablePath data) (place : G.edges) :
    matrix (transport φ data) (stablePathEquiv φ data hConnected path) (edgeEquiv φ place) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_map, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [sourceEdgeIndex_map]
  · exact fun _ _ _ _ h ↦ (sourceEdgeEquiv φ data).injective h

noncomputable def branchVertexEquiv (hConnected : data.Connected) :
    BranchVertex data ≃ BranchVertex (transport φ data) :=
  (sourceVertexEquiv φ data).subtypeEquiv fun vertex ↦ by
    rw [nonDanglingValency_map φ data hConnected]

/-- Count flags, so a stable loop retains its two incidences at one branch. -/
theorem incidenceCount_map (hConnected : data.Connected)
    (vertex : data.SourceVertex) (path : StablePath data) :
    StablePathCount.incidenceCount data vertex path =
      StablePathCount.incidenceCount (transport φ data) (sourceVertexEquiv φ data vertex)
        (stablePathEquiv φ data hConnected path) := by
  classical
  unfold StablePathCount.incidenceCount
  apply Finset.card_bij (fun edge _ ↦ nonDanglingEdgeEquiv φ data hConnected edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hEdge ⊢
    refine ⟨(incident_sourceEdgeEquiv_iff φ data edge.1 vertex).mpr hEdge.1, ?_⟩
    rw [← stablePathEquiv_mk, hEdge.2]
  · intro first _ second _ hEq
    exact (nonDanglingEdgeEquiv φ data hConnected).injective hEq
  · intro edge hEdge
    obtain ⟨oldEdge, rfl⟩ := (nonDanglingEdgeEquiv φ data hConnected).surjective edge
    refine ⟨oldEdge, ?_, rfl⟩
    simp only [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hEdge ⊢
    refine ⟨(incident_sourceEdgeEquiv_iff φ data oldEdge.1 vertex).mp hEdge.1, ?_⟩
    apply (stablePathEquiv φ data hConnected).injective
    rw [stablePathEquiv_mk]
    exact hEdge.2

/-- Actual target relabelling inhabits the common stable-graph dictionary. -/
noncomputable def graphEquivalence (hConnected : data.Connected) :
    StableGraphIncidence.Equivalence data (transport φ data) where
  vertex := branchVertexEquiv φ data hConnected
  row := stablePathEquiv φ data hConnected
  incidence vertex path := incidenceCount_map φ data hConnected vertex.1 path

theorem hasPathEnds_map (hConnected : data.Connected) (hEnds : HasPathEnds data) :
    HasPathEnds (transport φ data) :=
  (graphEquivalence φ data hConnected).hasPathEnds hConnected hEnds

end DraismaVargas.LocalCases.TargetRelabelStable
